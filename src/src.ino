#include <Wire.h>
#include <math.h>
#include <Protocentral_FDC1004.h>

#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>

// =============================
// USER PINS
// =============================
static const int BUTTON_PIN                = 27; // Active-LOW button to GND, uses INPUT_PULLUP
static const int LED_POWER_RED_PIN         = 15; // Red LED (power)
static const int LED_STABILITY_PIN         = 2;  // Green LED (stable / accepted)
static const int LED_MEASURING_PIN         = 12; // Orange LED (measuring mode)
static const int LED_CLASS_FRESH_PIN       = 0;  // Reserved for Flutter AI classification (Fresh)
static const int LED_CLASS_MODERATE_PIN    = 4;  // Reserved for Flutter AI classification (Moderately Fresh)
static const int LED_CLASS_SPOILED_PIN     = 16; // Reserved for Flutter AI classification (Spoiled)

// =============================
// I2C + Sensor
// =============================
static const int I2C_SDA = 21;
static const int I2C_SCL = 22;

const uint8_t  NUM_CHANNELS         = 4;
const uint16_t MEASUREMENT_DELAY_MS = 500;

FDC1004 capacitanceSensor(&Wire1, FDC1004_RATE_100HZ);

// =============================
// Filtering / Stability Settings
// =============================
const uint8_t MEDIAN_WIN       = 5;
const float   STABLE_SPREAD_PF = 0.80f; // first-layer differential stability
const float   VALUE_SPREAD_PF  = 0.30f; // second-layer corrected-value stability

// Better lock qualification / contact confirmation
static const float    CONTACT_MIN_PF_IDE1 = 0.80f; // TODO: validate experimentally
static const float    CONTACT_MIN_PF_IDE2 = 0.80f; // TODO: validate experimentally
static const uint32_t LOCK_STABLE_HOLD_MS = 2000;  // locally stable + contact-qualified before lock
static const float    REFERENCE_TOL_PF    = 0.50f;

// Threshold validation instrumentation
static const uint16_t CONTACT_REJECT_LOG_INTERVAL = 4; // print every N rejected ticks to reduce spam

// Rolling median windows per channel (raw capacitance in pF)
static float   chWin[NUM_CHANNELS][MEDIAN_WIN];
static uint8_t chCount[NUM_CHANNELS] = {0};
static uint8_t chIdx[NUM_CHANNELS]   = {0};

// Differential windows used ONLY for first-layer electrical stability checking
static float   ide1DiffWin[MEDIAN_WIN];
static float   ide2DiffWin[MEDIAN_WIN];
static uint8_t ide1DiffCount = 0, ide1DiffIdx = 0;
static uint8_t ide2DiffCount = 0, ide2DiffIdx = 0;

// Baseline-corrected TRUE capacitance windows used for second-layer value stability
static float   ide1CalWin[MEDIAN_WIN];
static float   ide2CalWin[MEDIAN_WIN];
static uint8_t ide1CalCount = 0, ide1CalIdx = 0;
static uint8_t ide2CalCount = 0, ide2CalIdx = 0;

// =============================
// Session settings
// =============================
static const uint32_t REQUIRED_STABLE_ACCUM_MS = 5000;  // 5 seconds cumulative accepted stable
static const uint32_t SESSION_TIMEOUT_MS       = 20000; // 20 seconds timeout
static const uint32_t CONTACT_DETECT_TIMEOUT_MS = 7000; // fail early if no valid fish contact is found

// =============================
// BLE GATT Settings
// =============================
static const char *BLE_DEVICE_NAME = "FDC1004_IDE";
static const char *UUID_SVC_IDE    = "6a6e2d3b-2c5f-4d3a-9b41-2c8a9c0a9b10";
static const char *UUID_CHR_PKT    = "6a6e2d3b-2c5f-4d3a-9b41-2c8a9c0a9b11"; // Notify only

// flags
static const uint8_t FLAG_STABLE_NOW    = (1 << 0);
static const uint8_t FLAG_IDE1_VALID    = (1 << 1);
static const uint8_t FLAG_IDE2_VALID    = (1 << 2);
static const uint8_t FLAG_SESSION_VALID = (1 << 4); // FINAL packet: session met stable requirement
static const uint8_t FLAG_FINAL         = (1 << 5); // FINAL packet marker
static const uint8_t FLAG_CLAMPED       = (1 << 6); // value clamped to fit int16 mpF

typedef struct __attribute__((packed)) {
  uint16_t seq;
  int16_t  ide1_mpF;
  int16_t  ide2_mpF;
  uint8_t  flags;
} ide_packet_t;

static_assert(sizeof(ide_packet_t) == 7, "ide_packet_t must be 7 bytes");

// =============================
// BLE globals
// =============================
static BLEServer         *gServer = nullptr;
static BLECharacteristic *gPktChr = nullptr;
static BLEAdvertising    *gAdvertising = nullptr;
static bool gDeviceConnected = false;
static bool gAdvertisingActive = false;
static volatile bool gRestartAdvertisingRequested = false;
static uint32_t lastAdvertiseAttemptMs = 0;
static uint16_t gSeq = 0;

// =============================
// State machine / failure reasons
// =============================
enum State {
  ST_CALIBRATING,
  ST_IDLE,
  ST_CONTACT_DETECTING,
  ST_REFERENCE_LOCKING,
  ST_MEASURING_VALID,
  ST_INVALIDATED
};

static State state = ST_CALIBRATING;

enum FailureReason {
  FAIL_NONE,
  FAIL_TIMEOUT_NO_CONTACT,
  FAIL_TIMEOUT_UNSTABLE,
  FAIL_CONTINUITY_BROKEN,
  FAIL_SENSOR_INVALID,
  FAIL_BLE_DISCONNECTED
};

static FailureReason lastFailureReason = FAIL_NONE;

static uint32_t sessionStartMs      = 0;
static uint32_t lastTickMs          = 0;
static uint32_t stableAccumMs       = 0; // cumulative accepted stable time
static uint32_t stableRunMs         = 0; // current continuous accepted stable run
static uint32_t contactQualifiedMs  = 0; // cumulative dwell for lock qualification
static uint32_t lastContactQualifyMs = 0;

// =============================
// Stable-only accumulators for FINAL summary
// These store baseline-corrected values gathered only while accepted.
// =============================
static double ide1StableSum = 0.0;
static double ide2StableSum = 0.0;
static uint16_t ide1StableSamples = 0;
static uint16_t ide2StableSamples = 0;

// Threshold validation counters (for experimental tuning logs)
static uint16_t sessionStableTicks = 0;
static uint16_t sessionRejectedLocalTicks = 0;
static uint16_t sessionRejectedContactTicks = 0;
static uint16_t sessionRejectedContinuityTicks = 0;

// =============================
// Startup calibration
// =============================
static const uint32_t CALIBRATION_TIME_MS = 5000;

static uint32_t calibrationStartMs = 0;

// Baseline of TRUE capacitance (not differential)
static double ide1BaselineSum = 0.0;
static double ide2BaselineSum = 0.0;
static uint16_t ide1BaselineSamples = 0;
static uint16_t ide2BaselineSamples = 0;

static float ide1BaselinePf = 0.0f;
static float ide2BaselinePf = 0.0f;

static bool baselineReady = false;

// =============================
// Session continuity lock
// =============================
static bool  referenceLocked = false;
static float ide1RefPf       = 0.0f;
static float ide2RefPf       = 0.0f;

// =============================
// Forward declarations for BLE helpers used by callbacks
// =============================
static void startBleAdvertising(const char *reason);
static void stopBleAdvertising(const char *reason);

// =============================
// Callbacks
// =============================
class ServerCallbacks : public BLEServerCallbacks {
  void onConnect(BLEServer*) override {
    gDeviceConnected = true;
    gAdvertisingActive = false;
    gRestartAdvertisingRequested = false;
    Serial.println("[BLE] Client connected");
  }

  void onDisconnect(BLEServer*) override {
    gDeviceConnected = false;
    gAdvertisingActive = false;
    gRestartAdvertisingRequested = true;
    Serial.println("[BLE] Client disconnected");
  }
};

// =============================
// Helpers
// =============================
static void startBleAdvertising(const char *reason)
{
  Serial.print("[BLE] startBleAdvertising called: ");
  Serial.println(reason);

  if (!gAdvertising) {
    Serial.print("[BLE] Advertising start skipped (null advertising) reason=");
    Serial.println(reason);
    gAdvertisingActive = false;
    return;
  }

  Serial.println("[BLE] Calling gAdvertising->start()...");
  if (gAdvertising->start()) {
    gAdvertisingActive = true;
    lastAdvertiseAttemptMs = millis();
    Serial.print("[BLE] Advertising started: ");
    Serial.println(reason);
  } else {
    gAdvertisingActive = false;
    lastAdvertiseAttemptMs = millis();
    Serial.print("[BLE] Advertising start failed: ");
    Serial.println(reason);
  }
}

static void stopBleAdvertising(const char *reason)
{
  if (!gAdvertising) return;

  gAdvertising->stop();
  gAdvertisingActive = false;
  Serial.print("[BLE] Advertising stopped: ");
  Serial.println(reason);
}

static const char* stateName(State s)
{
  switch (s) {
    case ST_CALIBRATING:       return "CALIBRATING";
    case ST_IDLE:              return "IDLE";
    case ST_CONTACT_DETECTING: return "CONTACT_DETECTING";
    case ST_REFERENCE_LOCKING: return "REFERENCE_LOCKING";
    case ST_MEASURING_VALID:   return "MEASURING_VALID";
    case ST_INVALIDATED:       return "INVALIDATED";
    default:                   return "UNKNOWN";
  }
}

static const char* failureName(FailureReason r)
{
  switch (r) {
    case FAIL_NONE:               return "NONE";
    case FAIL_TIMEOUT_NO_CONTACT: return "TIMEOUT_NO_CONTACT";
    case FAIL_TIMEOUT_UNSTABLE:   return "TIMEOUT_UNSTABLE";
    case FAIL_CONTINUITY_BROKEN:  return "CONTINUITY_BROKEN";
    case FAIL_SENSOR_INVALID:     return "SENSOR_INVALID";
    case FAIL_BLE_DISCONNECTED:   return "BLE_DISCONNECTED";
    default:                      return "UNKNOWN";
  }
}

static void setState(State nextState)
{
  if (state != nextState) {
    Serial.print("[STATE] ");
    Serial.print(stateName(state));
    Serial.print(" -> ");
    Serial.println(stateName(nextState));
    state = nextState;
  }
}

static void setFailure(FailureReason reason)
{
  lastFailureReason = reason;
  if (reason != FAIL_NONE) {
    Serial.print("[FAILURE] ");
    Serial.println(failureName(reason));
  }
}

static inline void ledWrite(int pin, bool on) {
  if (pin < 0) return;
  digitalWrite(pin, on ? HIGH : LOW);
}

static void resetClassificationLeds()
{
  ledWrite(LED_CLASS_FRESH_PIN, false);
  ledWrite(LED_CLASS_MODERATE_PIN, false);
  ledWrite(LED_CLASS_SPOILED_PIN, false);
}

static inline void pushSample(float *win, uint8_t &count, uint8_t &idx, float v)
{
  win[idx] = v;
  idx = (uint8_t)((idx + 1) % MEDIAN_WIN);
  if (count < MEDIAN_WIN) count++;
}

static float medianOf(const float *win, uint8_t count)
{
  if (count == 0) return NAN;

  float tmp[MEDIAN_WIN];
  for (uint8_t i = 0; i < count; i++) tmp[i] = win[i];

  for (uint8_t i = 1; i < count; i++) {
    float key = tmp[i];
    int8_t j = (int8_t)i - 1;
    while (j >= 0 && tmp[j] > key) {
      tmp[j + 1] = tmp[j];
      j--;
    }
    tmp[j + 1] = key;
  }
  return tmp[count / 2];
}

static void minMaxOf(const float *win, uint8_t count, float &mn, float &mx)
{
  mn =  1e9f;
  mx = -1e9f;
  for (uint8_t i = 0; i < count; i++) {
    if (win[i] < mn) mn = win[i];
    if (win[i] > mx) mx = win[i];
  }
}

static bool isStableSpread(const float *win, uint8_t count, float thresh_pf)
{
  if (count < MEDIAN_WIN) return false;
  float mn, mx;
  minMaxOf(win, count, mn, mx);
  return (mx - mn) <= thresh_pf;
}

static bool hasContactSignature(float ide1CalMed, bool ide1Valid,
                                float ide2CalMed, bool ide2Valid)
{
  const bool ide1Contact = ide1Valid && !isnan(ide1CalMed) && (fabsf(ide1CalMed) >= CONTACT_MIN_PF_IDE1);
  const bool ide2Contact = ide2Valid && !isnan(ide2CalMed) && (fabsf(ide2CalMed) >= CONTACT_MIN_PF_IDE2);
  return ide1Contact && ide2Contact;
}

static void clearWindows()
{
  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    chCount[ch] = 0;
    chIdx[ch] = 0;
    for (uint8_t i = 0; i < MEDIAN_WIN; i++) {
      chWin[ch][i] = 0.0f;
    }
  }

  ide1DiffCount = ide1DiffIdx = 0;
  ide2DiffCount = ide2DiffIdx = 0;
  ide1CalCount = ide1CalIdx = 0;
  ide2CalCount = ide2CalIdx = 0;

  for (uint8_t i = 0; i < MEDIAN_WIN; i++) {
    ide1DiffWin[i] = 0.0f;
    ide2DiffWin[i] = 0.0f;
    ide1CalWin[i] = 0.0f;
    ide2CalWin[i] = 0.0f;
  }
}

static void resetCalibration()
{
  calibrationStartMs = 0;
  ide1BaselineSum = 0.0;
  ide2BaselineSum = 0.0;
  ide1BaselineSamples = 0;
  ide2BaselineSamples = 0;
  ide1BaselinePf = 0.0f;
  ide2BaselinePf = 0.0f;
  baselineReady = false;
  clearWindows();
}

static void resetSessionStats()
{
  stableAccumMs = 0;
  stableRunMs = 0;
  contactQualifiedMs = 0;
  lastContactQualifyMs = 0;
  ide1StableSum = 0.0;
  ide2StableSum = 0.0;
  ide1StableSamples = 0;
  ide2StableSamples = 0;
  lastTickMs = 0;

  referenceLocked = false;
  ide1RefPf = 0.0f;
  ide2RefPf = 0.0f;

  sessionStableTicks = 0;
  sessionRejectedLocalTicks = 0;
  sessionRejectedContactTicks = 0;
  sessionRejectedContinuityTicks = 0;

  lastFailureReason = FAIL_NONE;
}

static bool calibrationTickAndFinish(uint32_t nowMs)
{
  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    fdc1004_capacitance_t m =
        capacitanceSensor.getCapacitanceMeasurement((fdc1004_channel_t)ch);

    if (!isnan(m.capacitance_pf)) {
      pushSample(chWin[ch], chCount[ch], chIdx[ch], m.capacitance_pf);
    }

    delay(10);
  }

  float chMed[NUM_CHANNELS];
  bool chValid[NUM_CHANNELS];

  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    chMed[ch] = medianOf(chWin[ch], chCount[ch]);
    chValid[ch] = !isnan(chMed[ch]);
  }

  const bool ide1TrueValid = chValid[0] && chValid[1];
  const bool ide2TrueValid = chValid[2] && chValid[3];

  const float ide1True = ide1TrueValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;
  const float ide2True = ide2TrueValid ? (0.5f * (chMed[2] + chMed[3])) : NAN;

  if (ide1TrueValid) {
    ide1BaselineSum += (double)ide1True;
    ide1BaselineSamples++;
  }

  if (ide2TrueValid) {
    ide2BaselineSum += (double)ide2True;
    ide2BaselineSamples++;
  }

  Serial.print("[CAL] IDE1_RAW=");
  if (ide1TrueValid) Serial.print(ide1True, 3); else Serial.print("ERR");
  Serial.print("\tIDE2_RAW=");
  if (ide2TrueValid) Serial.print(ide2True, 3); else Serial.print("ERR");
  Serial.print("\telapsedMs=");
  Serial.println(nowMs - calibrationStartMs);

  if ((nowMs - calibrationStartMs) >= CALIBRATION_TIME_MS) {
    if (ide1BaselineSamples > 0) {
      ide1BaselinePf = (float)(ide1BaselineSum / (double)ide1BaselineSamples);
    }

    if (ide2BaselineSamples > 0) {
      ide2BaselinePf = (float)(ide2BaselineSum / (double)ide2BaselineSamples);
    }

    baselineReady = (ide1BaselineSamples > 0) || (ide2BaselineSamples > 0);

    Serial.println("== CALIBRATION COMPLETE ==");
    Serial.print("IDE1 baseline pF = ");
    Serial.println(ide1BaselinePf, 3);
    Serial.print("IDE2 baseline pF = ");
    Serial.println(ide2BaselinePf, 3);
    Serial.println("[TUNE] Contact thresholds should be validated against repeated fish-contact trials.");

    clearWindows();
    return true;
  }

  return false;
}

static bool buttonPressedEvent()
{
  static bool lastStable = true;
  static bool lastRead = true;
  static uint32_t lastChange = 0;

  bool r = digitalRead(BUTTON_PIN);

  if (r != lastRead) {
    lastRead = r;
    lastChange = millis();
  }

  if (millis() - lastChange >= 30) {
    if (r != lastStable) {
      lastStable = r;
      if (lastStable == false) return true;
    }
  }
  return false;
}

static int16_t pfToMilliPfClamped(float pf, bool &clamped)
{
  if (isnan(pf)) return 0;

  long mpf = lroundf(pf * 1000.0f);
  if (mpf > 32767L) {
    mpf = 32767L;
    clamped = true;
  } else if (mpf < -32768L) {
    mpf = -32768L;
    clamped = true;
  }
  return (int16_t)mpf;
}

static void sendPacket(float ide1Pf, bool ide1Valid,
                       float ide2Pf, bool ide2Valid,
                       bool stableNow, bool sessionValid, bool finalPacket)
{
  bool clamped = false;
  int16_t ide1_mpF = ide1Valid ? pfToMilliPfClamped(ide1Pf, clamped) : 0;
  int16_t ide2_mpF = ide2Valid ? pfToMilliPfClamped(ide2Pf, clamped) : 0;

  uint8_t flags = 0;
  if (stableNow)    flags |= FLAG_STABLE_NOW;
  if (ide1Valid)    flags |= FLAG_IDE1_VALID;
  if (ide2Valid)    flags |= FLAG_IDE2_VALID;
  if (sessionValid) flags |= FLAG_SESSION_VALID;
  if (finalPacket)  flags |= FLAG_FINAL;
  if (clamped)      flags |= FLAG_CLAMPED;

  ide_packet_t pkt;
  pkt.seq      = gSeq++;
  pkt.ide1_mpF = ide1_mpF;
  pkt.ide2_mpF = ide2_mpF;
  pkt.flags    = flags;

  if (gDeviceConnected && gPktChr) {
    gPktChr->setValue((uint8_t*)&pkt, sizeof(pkt));
    gPktChr->notify();
  }
}

static void setupBle()
{
  BLEDevice::init(BLE_DEVICE_NAME);

  gServer = BLEDevice::createServer();
  gServer->setCallbacks(new ServerCallbacks());

  BLEService *svc = gServer->createService(UUID_SVC_IDE);

  gPktChr = svc->createCharacteristic(
    UUID_CHR_PKT,
    BLECharacteristic::PROPERTY_READ |
    BLECharacteristic::PROPERTY_NOTIFY
  );
  gPktChr->addDescriptor(new BLE2902());

  ide_packet_t initPkt = {0, 0, 0, 0};
  gPktChr->setValue((uint8_t*)&initPkt, sizeof(initPkt));

  svc->start();

  gAdvertising = BLEDevice::getAdvertising();
  gAdvertising->addServiceUUID(UUID_SVC_IDE);
  gAdvertising->setScanResponse(true);
  startBleAdvertising("setupBle");

  Serial.println("✓ BLE notify service started");
}

static void finishInvalidSession(float ide1Pf, bool ide1Valid,
                                 float ide2Pf, bool ide2Valid,
                                 FailureReason reason)
{
  setFailure(reason);
  sendPacket(ide1Pf, ide1Valid, ide2Pf, ide2Valid, false, false, true);

  Serial.print("== FINAL: INVALID SESSION / ");
  Serial.print(failureName(reason));
  Serial.println(" ==");

  Serial.print("[SUMMARY] stableTicks=");
  Serial.print(sessionStableTicks);
  Serial.print("\trejectLocal=");
  Serial.print(sessionRejectedLocalTicks);
  Serial.print("\trejectContact=");
  Serial.print(sessionRejectedContactTicks);
  Serial.print("\trejectContinuity=");
  Serial.println(sessionRejectedContinuityTicks);

  ledWrite(LED_STABILITY_PIN, false);
  ledWrite(LED_MEASURING_PIN, false);
  setState(ST_INVALIDATED);
}

// =============================
// One measurement tick
// =============================
static bool measurementTickAndMaybeFinish(uint32_t nowMs)
{
  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    fdc1004_capacitance_t m =
        capacitanceSensor.getCapacitanceMeasurement((fdc1004_channel_t)ch);

    if (!isnan(m.capacitance_pf)) {
      pushSample(chWin[ch], chCount[ch], chIdx[ch], m.capacitance_pf);
    }
    delay(10);
  }

  float chMed[NUM_CHANNELS];
  bool  chValid[NUM_CHANNELS];

  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    chMed[ch] = medianOf(chWin[ch], chCount[ch]);
    chValid[ch] = !isnan(chMed[ch]);
  }

  const bool ide1TrueValid = chValid[0] && chValid[1];
  const bool ide2TrueValid = chValid[2] && chValid[3];

  const float ide1True = ide1TrueValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;
  const float ide2True = ide2TrueValid ? (0.5f * (chMed[2] + chMed[3])) : NAN;

  const float ide1Cal = ide1TrueValid ? (ide1True - ide1BaselinePf) : NAN;
  const float ide2Cal = ide2TrueValid ? (ide2True - ide2BaselinePf) : NAN;

  const bool ide1DiffValid = ide1TrueValid;
  const bool ide2DiffValid = ide2TrueValid;

  const float ide1Diff = ide1DiffValid ? (chMed[0] - chMed[1]) : NAN;
  const float ide2Diff = ide2DiffValid ? (chMed[2] - chMed[3]) : NAN;

  if (ide1DiffValid) pushSample(ide1DiffWin, ide1DiffCount, ide1DiffIdx, ide1Diff);
  if (ide2DiffValid) pushSample(ide2DiffWin, ide2DiffCount, ide2DiffIdx, ide2Diff);

  if (ide1TrueValid) pushSample(ide1CalWin, ide1CalCount, ide1CalIdx, ide1Cal);
  if (ide2TrueValid) pushSample(ide2CalWin, ide2CalCount, ide2CalIdx, ide2Cal);

  const bool diffStable1 = ide1DiffValid && isStableSpread(ide1DiffWin, ide1DiffCount, STABLE_SPREAD_PF);
  const bool diffStable2 = ide2DiffValid && isStableSpread(ide2DiffWin, ide2DiffCount, STABLE_SPREAD_PF);
  const bool valueStable1 = ide1TrueValid && isStableSpread(ide1CalWin, ide1CalCount, VALUE_SPREAD_PF);
  const bool valueStable2 = ide2TrueValid && isStableSpread(ide2CalWin, ide2CalCount, VALUE_SPREAD_PF);

  const bool localStableNow = diffStable1 && diffStable2 && valueStable1 && valueStable2;

  const float ide1CalMed = medianOf(ide1CalWin, ide1CalCount);
  const float ide2CalMed = medianOf(ide2CalWin, ide2CalCount);

  const bool contactQualifiedNow = hasContactSignature(ide1CalMed, ide1TrueValid,
                                                       ide2CalMed, ide2TrueValid);

  const uint32_t dt = (lastTickMs == 0) ? MEASUREMENT_DELAY_MS : (nowMs - lastTickMs);
  lastTickMs = nowMs;

  if (!ide1TrueValid || !ide2TrueValid) {
    sessionRejectedLocalTicks++;
  }

  if (localStableNow && contactQualifiedNow && !referenceLocked) {
    contactQualifiedMs += dt;
  } else if (!referenceLocked) {
    contactQualifiedMs = 0;
  }

  if (!referenceLocked) {
    if (!localStableNow) {
      sessionRejectedLocalTicks++;
      setState(ST_CONTACT_DETECTING);
    } else if (!contactQualifiedNow) {
      sessionRejectedContactTicks++;
      setState(ST_CONTACT_DETECTING);
      if ((sessionRejectedContactTicks % CONTACT_REJECT_LOG_INTERVAL) == 0) {
        Serial.print("[CONTACT] Rejected stable window: ide1Med=");
        if (!isnan(ide1CalMed)) Serial.print(ide1CalMed, 3); else Serial.print("ERR");
        Serial.print(" ide2Med=");
        if (!isnan(ide2CalMed)) Serial.print(ide2CalMed, 3); else Serial.print("ERR");
        Serial.print(" thresholds=(");
        Serial.print(CONTACT_MIN_PF_IDE1, 3);
        Serial.print(", ");
        Serial.print(CONTACT_MIN_PF_IDE2, 3);
        Serial.println(")");
      }
    } else if (contactQualifiedMs < LOCK_STABLE_HOLD_MS) {
      setState(ST_REFERENCE_LOCKING);
    }
  }

  if (!referenceLocked && localStableNow && contactQualifiedNow && contactQualifiedMs >= LOCK_STABLE_HOLD_MS) {
    ide1RefPf = ide1CalMed;
    ide2RefPf = ide2CalMed;
    referenceLocked = true;
    setState(ST_MEASURING_VALID);

    Serial.println("[LOCK] Reference locked after qualified contact dwell");
    Serial.print("[LOCK] ide1Ref=");
    Serial.print(ide1RefPf, 3);
    Serial.print("\tide2Ref=");
    Serial.println(ide2RefPf, 3);
  }

  const bool continuity1 =
      referenceLocked && !isnan(ide1CalMed) && (fabsf(ide1CalMed - ide1RefPf) <= REFERENCE_TOL_PF);
  const bool continuity2 =
      referenceLocked && !isnan(ide2CalMed) && (fabsf(ide2CalMed - ide2RefPf) <= REFERENCE_TOL_PF);

  const bool stableNow = referenceLocked && localStableNow && continuity1 && continuity2;
  const bool continuityBroken = referenceLocked && localStableNow && (!continuity1 || !continuity2);

  ledWrite(LED_STABILITY_PIN, stableNow);

  if (stableNow) {
    stableAccumMs += dt;
    stableRunMs += dt;
    sessionStableTicks++;

    if (ide1TrueValid) {
      ide1StableSum += (double)ide1Cal;
      ide1StableSamples++;
    }
    if (ide2TrueValid) {
      ide2StableSum += (double)ide2Cal;
      ide2StableSamples++;
    }

    sendPacket(ide1Cal, ide1TrueValid, ide2Cal, ide2TrueValid,
               true, false, false);
  } else {
    stableRunMs = 0;
    if (referenceLocked && !continuity1) sessionRejectedContinuityTicks++;
    if (referenceLocked && !continuity2) sessionRejectedContinuityTicks++;
  }

  const uint32_t elapsed = nowMs - sessionStartMs;
  const bool sessionValid = (stableAccumMs >= REQUIRED_STABLE_ACCUM_MS);
  const bool timedOut     = (elapsed >= SESSION_TIMEOUT_MS);
  const bool contactTimedOut = (!referenceLocked && elapsed >= CONTACT_DETECT_TIMEOUT_MS);

  Serial.print("state=");
  Serial.print(stateName(state));
  Serial.print("\tCH0=");
  if (chValid[0]) Serial.print(chMed[0], 3); else Serial.print("ERR");
  Serial.print("\tCH1=");
  if (chValid[1]) Serial.print(chMed[1], 3); else Serial.print("ERR");
  Serial.print("\tCH2=");
  if (chValid[2]) Serial.print(chMed[2], 3); else Serial.print("ERR");
  Serial.print("\tCH3=");
  if (chValid[3]) Serial.print(chMed[3], 3); else Serial.print("ERR");

  Serial.print("\tIDE1_CAL=");
  if (ide1TrueValid) Serial.print(ide1Cal, 3); else Serial.print("ERR");
  Serial.print("\tIDE2_CAL=");
  if (ide2TrueValid) Serial.print(ide2Cal, 3); else Serial.print("ERR");

  Serial.print("\tlocalStableNow=");
  Serial.print(localStableNow ? 1 : 0);
  Serial.print("\tcontactQualifiedNow=");
  Serial.print(contactQualifiedNow ? 1 : 0);
  Serial.print("\tcontactQualifiedMs=");
  Serial.print(contactQualifiedMs);
  Serial.print("\trefLocked=");
  Serial.print(referenceLocked ? 1 : 0);
  Serial.print("\tide1Ref=");
  if (referenceLocked) Serial.print(ide1RefPf, 3); else Serial.print("NA");
  Serial.print("\tide2Ref=");
  if (referenceLocked) Serial.print(ide2RefPf, 3); else Serial.print("NA");
  Serial.print("\tide1Med=");
  if (!isnan(ide1CalMed)) Serial.print(ide1CalMed, 3); else Serial.print("ERR");
  Serial.print("\tide2Med=");
  if (!isnan(ide2CalMed)) Serial.print(ide2CalMed, 3); else Serial.print("ERR");
  Serial.print("\tcontinuity1=");
  Serial.print(continuity1 ? 1 : 0);
  Serial.print("\tcontinuity2=");
  Serial.print(continuity2 ? 1 : 0);
  Serial.print("\tstableNow=");
  Serial.print(stableNow ? 1 : 0);
  Serial.print("\tstableRunMs=");
  Serial.print(stableRunMs);
  Serial.print("\tstableAccumMs=");
  Serial.print(stableAccumMs);
  Serial.print("\telapsedMs=");
  Serial.println(elapsed);

  if (!gDeviceConnected && referenceLocked) {
    Serial.println("[WARN] BLE disconnected during active measurement");
    if (!gAdvertisingActive) {
      startBleAdvertising("measurement watchdog");
    }
  }

  if (continuityBroken) {
    finishInvalidSession(ide1Cal, ide1TrueValid, ide2Cal, ide2TrueValid,
                         FAIL_CONTINUITY_BROKEN);
    return true;
  }

  if (contactTimedOut) {
    finishInvalidSession(ide1Cal, ide1TrueValid, ide2Cal, ide2TrueValid,
                         FAIL_TIMEOUT_NO_CONTACT);
    return true;
  }

  if (sessionValid || timedOut) {
    if (sessionValid) {
      bool ide1AvgValid = (ide1StableSamples > 0);
      bool ide2AvgValid = (ide2StableSamples > 0);

      float ide1Avg = ide1AvgValid ? (float)(ide1StableSum / (double)ide1StableSamples) : NAN;
      float ide2Avg = ide2AvgValid ? (float)(ide2StableSum / (double)ide2StableSamples) : NAN;

      sendPacket(ide1Avg, ide1AvgValid, ide2Avg, ide2AvgValid,
                 stableNow, true, true);

      Serial.println("== FINAL: VALID SESSION ==");
      Serial.print("[SUMMARY] stableTicks=");
      Serial.print(sessionStableTicks);
      Serial.print("\trejectLocal=");
      Serial.print(sessionRejectedLocalTicks);
      Serial.print("\trejectContact=");
      Serial.print(sessionRejectedContactTicks);
      Serial.print("\trejectContinuity=");
      Serial.println(sessionRejectedContinuityTicks);
    } else {
      finishInvalidSession(ide1Cal, ide1TrueValid, ide2Cal, ide2TrueValid,
                           referenceLocked ? FAIL_TIMEOUT_UNSTABLE : FAIL_TIMEOUT_NO_CONTACT);
    }

    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, false);
    return true;
  }

  return false;
}

// =============================
// Setup / loop
// =============================
void setup()
{
  Serial.begin(115200);
  delay(200);

  pinMode(BUTTON_PIN, INPUT_PULLUP);
  pinMode(LED_POWER_RED_PIN, OUTPUT);
  pinMode(LED_STABILITY_PIN, OUTPUT);
  if (LED_MEASURING_PIN >= 0) pinMode(LED_MEASURING_PIN, OUTPUT);
  if (LED_CLASS_FRESH_PIN >= 0) pinMode(LED_CLASS_FRESH_PIN, OUTPUT);
  if (LED_CLASS_MODERATE_PIN >= 0) pinMode(LED_CLASS_MODERATE_PIN, OUTPUT);
  if (LED_CLASS_SPOILED_PIN >= 0) pinMode(LED_CLASS_SPOILED_PIN, OUTPUT);

  ledWrite(LED_POWER_RED_PIN, true);
  ledWrite(LED_STABILITY_PIN, false);
  ledWrite(LED_MEASURING_PIN, false);
  resetClassificationLeds();

  Wire1.setPins(I2C_SDA, I2C_SCL);

  Serial.println("FDC1004 BLE Flow: button-start, qualified contact lock, stable sample notify, FINAL notify");

  if (!capacitanceSensor.begin()) {
    Serial.println("✗ FDC1004 init failed");
    while (1) delay(1000);
  }
  if (!capacitanceSensor.isConnected()) {
    Serial.println("✗ FDC1004 not responding");
    while (1) delay(1000);
  }
  Serial.println("✓ FDC1004 OK");

  setupBle();

  resetCalibration();
  calibrationStartMs = millis();
  setState(ST_CALIBRATING);

  Serial.println("== STARTUP CALIBRATION ==");
  Serial.println("Keep electrodes in open air for 5 seconds...");
}

void loop()
{
  if (!gDeviceConnected && gRestartAdvertisingRequested) {
    gRestartAdvertisingRequested = false;
    startBleAdvertising("deferred disconnect restart");
  }

  if (state == ST_CALIBRATING) {
    ledWrite(LED_POWER_RED_PIN, true);
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, false);

    const uint32_t nowCalAdv = millis();
    // Watchdog retry: if advertising silently stopped while nobody is connected,
    // try again every few seconds instead of relying on a single callback restart.
    if (!gDeviceConnected && (!gAdvertisingActive || (nowCalAdv - lastAdvertiseAttemptMs >= 3000))) {
      startBleAdvertising("calibrating watchdog");
    }

    static uint32_t lastCalibrationTickMs = 0;
    const uint32_t now = millis();

    if (now - lastCalibrationTickMs >= MEASUREMENT_DELAY_MS) {
      lastCalibrationTickMs = now;

      const bool done = calibrationTickAndFinish(now);
      if (done) {
        setState(ST_IDLE);
        Serial.println("== DEVICE READY ==");
        Serial.println("Press button to start measurement session.\n");
      }
    }
    return;
  }

  if (state == ST_IDLE && buttonPressedEvent()) {
    clearWindows();
    resetSessionStats();
    sessionStartMs = millis();

    setState(ST_CONTACT_DETECTING);
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, true);

    Serial.println("== SESSION START ==");
    Serial.print("[CONFIG] contact thresholds IDE1/IDE2 = ");
    Serial.print(CONTACT_MIN_PF_IDE1, 3);
    Serial.print(" / ");
    Serial.println(CONTACT_MIN_PF_IDE2, 3);
    Serial.print("[CONFIG] lock dwell ms = ");
    Serial.println(LOCK_STABLE_HOLD_MS);
  }

  if (state == ST_IDLE) {
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, false);

    const uint32_t nowIdle = millis();
    if (!gDeviceConnected && (!gAdvertisingActive || (nowIdle - lastAdvertiseAttemptMs >= 3000))) {
      startBleAdvertising("idle watchdog");
    }

    delay(50);
    return;
  }

  static uint32_t lastScheduleMs = 0;
  const uint32_t now = millis();

  if (now - lastScheduleMs >= MEASUREMENT_DELAY_MS) {
    lastScheduleMs = now;

    const bool finished = measurementTickAndMaybeFinish(now);
    if (finished) {
      setState(ST_IDLE);
      Serial.println("== SESSION END (IDLE) ==");
      Serial.println("Press button again to start a new session.\n");
    }
  }
}