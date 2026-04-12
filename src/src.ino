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
static const int LED_MEASURING_PIN         = 14; // Orange LED (measuring mode)
static const int LED_CLASS_FRESH_PIN       = 0;  // Reserved for Flutter AI classification (Fresh)
static const int LED_CLASS_MODERATE_PIN    = 4;  // Reserved for Flutter AI classification (Moderately Fresh)
static const int LED_CLASS_SPOILED_PIN     = 16; // Reserved for Flutter AI classification (Spoiled)

// =============================
// I2C + Sensor
// =============================
static const int I2C_SDA = 21;
static const int I2C_SCL = 22;

// Use only channels 0 and 1 for one IDE
static const uint8_t IDE_CH_A = 0;
static const uint8_t IDE_CH_B = 1;
static const uint8_t NUM_USED_CHANNELS = 2;

const uint16_t MEASUREMENT_DELAY_MS = 500;

FDC1004 capacitanceSensor(&Wire1, FDC1004_RATE_100HZ);

// =============================
// Filtering / Stability Settings
// =============================
const uint8_t MEDIAN_WIN       = 5;
const float   STABLE_SPREAD_PF = 0.80f; // differential stability threshold
const float   VALUE_SPREAD_PF  = 0.30f; // corrected-value stability threshold

static const float    CONTACT_MIN_PF_IDE   = 0.80f; // TODO: validate experimentally
static const uint32_t LOCK_STABLE_HOLD_MS  = 2000;  // stable + contact-qualified dwell before reference lock
static const float    REFERENCE_TOL_PF     = 0.50f;
static const uint16_t CONTACT_REJECT_LOG_INTERVAL = 4;

// Rolling windows for raw capacitance from CH0 and CH1
static float   rawWin[NUM_USED_CHANNELS][MEDIAN_WIN];
static uint8_t rawCount[NUM_USED_CHANNELS] = {0};
static uint8_t rawIdx[NUM_USED_CHANNELS]   = {0};

// Window for IDE differential: CH0 - CH1
static float   ideDiffWin[MEDIAN_WIN];
static uint8_t ideDiffCount = 0;
static uint8_t ideDiffIdx   = 0;

// Window for baseline-corrected IDE value
static float   ideCalWin[MEDIAN_WIN];
static uint8_t ideCalCount = 0;
static uint8_t ideCalIdx   = 0;

// =============================
// Session settings
// =============================
static const uint32_t REQUIRED_STABLE_ACCUM_MS  = 5000;  // 5 seconds cumulative accepted stable
static const uint32_t SESSION_TIMEOUT_MS        = 20000; // 20 seconds timeout
static const uint32_t CONTACT_DETECT_TIMEOUT_MS = 7000;  // fail early if no valid fish contact is found

// =============================
// BLE GATT Settings
// =============================
static const char *BLE_DEVICE_NAME = "FDC1004_IDE";
static const char *UUID_SVC_IDE    = "6a6e2d3b-2c5f-4d3a-9b41-2c8a9c0a9b10";
static const char *UUID_CHR_PKT    = "6a6e2d3b-2c5f-4d3a-9b41-2c8a9c0a9b11"; // Notify only

// Flags
static const uint8_t FLAG_STABLE_NOW    = (1 << 0);
static const uint8_t FLAG_IDE_VALID     = (1 << 1);
static const uint8_t FLAG_SESSION_VALID = (1 << 4); // FINAL packet: session met stable requirement
static const uint8_t FLAG_FINAL         = (1 << 5); // FINAL packet marker
static const uint8_t FLAG_CLAMPED       = (1 << 6); // value clamped to fit int16 mpF

typedef struct __attribute__((packed)) {
  uint16_t seq;
  int16_t  ide_mpF;
  uint8_t  flags;
} ide_packet_t;

static_assert(sizeof(ide_packet_t) == 5, "ide_packet_t must be 5 bytes");

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

static uint32_t sessionStartMs       = 0;
static uint32_t lastTickMs           = 0;
static uint32_t stableAccumMs        = 0; // cumulative accepted stable time
static uint32_t stableRunMs          = 0; // current continuous accepted stable run
static uint32_t contactQualifiedMs   = 0; // cumulative dwell for lock qualification

// =============================
// Stable-only accumulator for FINAL summary
// =============================
static double   ideStableSum     = 0.0;
static uint16_t ideStableSamples = 0;

// Threshold validation counters
static uint16_t sessionStableTicks            = 0;
static uint16_t sessionRejectedLocalTicks     = 0;
static uint16_t sessionRejectedContactTicks   = 0;
static uint16_t sessionRejectedContinuityTicks = 0;

// =============================
// Startup calibration
// =============================
static const uint32_t CALIBRATION_TIME_MS = 5000;

static uint32_t calibrationStartMs = 0;
static double   ideBaselineSum     = 0.0;
static uint16_t ideBaselineSamples = 0;
static float    ideBaselinePf      = 0.0f;
static bool     baselineReady      = false;

// =============================
// Session continuity lock
// =============================
static bool  referenceLocked = false;
static float ideRefPf        = 0.0f;

// =============================
// Forward declarations for BLE helpers
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

  gAdvertising->start();
  gAdvertisingActive = true;
  lastAdvertiseAttemptMs = millis();

  Serial.print("[BLE] Advertising started: ");
  Serial.println(reason);
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

static inline void ledWrite(int pin, bool on)
{
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

static bool hasContactSignature(float ideCalMed, bool ideValid)
{
  return ideValid && !isnan(ideCalMed) && (fabsf(ideCalMed) >= CONTACT_MIN_PF_IDE);
}

static void clearWindows()
{
  for (uint8_t ch = 0; ch < NUM_USED_CHANNELS; ch++) {
    rawCount[ch] = 0;
    rawIdx[ch] = 0;
    for (uint8_t i = 0; i < MEDIAN_WIN; i++) {
      rawWin[ch][i] = 0.0f;
    }
  }

  ideDiffCount = 0;
  ideDiffIdx   = 0;
  ideCalCount  = 0;
  ideCalIdx    = 0;

  for (uint8_t i = 0; i < MEDIAN_WIN; i++) {
    ideDiffWin[i] = 0.0f;
    ideCalWin[i]  = 0.0f;
  }
}

static void resetCalibration()
{
  calibrationStartMs = 0;
  ideBaselineSum     = 0.0;
  ideBaselineSamples = 0;
  ideBaselinePf      = 0.0f;
  baselineReady      = false;
  clearWindows();
}

static void resetSessionStats()
{
  stableAccumMs = 0;
  stableRunMs = 0;
  contactQualifiedMs = 0;
  ideStableSum = 0.0;
  ideStableSamples = 0;
  lastTickMs = 0;

  referenceLocked = false;
  ideRefPf = 0.0f;

  sessionStableTicks = 0;
  sessionRejectedLocalTicks = 0;
  sessionRejectedContactTicks = 0;
  sessionRejectedContinuityTicks = 0;

  lastFailureReason = FAIL_NONE;
}

static float readChannelPfNoCapdac(uint8_t channel)
{
  const int32_t FDC_ERROR_VALUE = (int32_t)0x80000000UL;

  int32_t cap_ff = capacitanceSensor.getCapacitance(channel); // returns femtofarads
  if (cap_ff == FDC_ERROR_VALUE) {
    return NAN;
  }

  return ((float)cap_ff) / 1000.0f; // convert fF -> pF
}

static bool calibrationTickAndFinish(uint32_t nowMs)
{
  const uint8_t usedChannels[NUM_USED_CHANNELS] = { IDE_CH_A, IDE_CH_B };

  for (uint8_t i = 0; i < NUM_USED_CHANNELS; i++) {
    float cap_pf = readChannelPfNoCapdac(usedChannels[i]);

    if (!isnan(cap_pf)) {
      pushSample(rawWin[i], rawCount[i], rawIdx[i], cap_pf);
    }

    delay(10);
  }

  float chMed[NUM_USED_CHANNELS];
  bool  chValid[NUM_USED_CHANNELS];

  for (uint8_t i = 0; i < NUM_USED_CHANNELS; i++) {
    chMed[i] = medianOf(rawWin[i], rawCount[i]);
    chValid[i] = !isnan(chMed[i]);
  }

  const bool ideValid = chValid[0] && chValid[1];
  const float ideTrue = ideValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;

  if (ideValid) {
    ideBaselineSum += (double)ideTrue;
    ideBaselineSamples++;
  }

  Serial.print("[CAL] CH0_RAW=");
  if (chValid[0]) Serial.print(chMed[0], 3); else Serial.print("ERR");
  Serial.print("\tCH1_RAW=");
  if (chValid[1]) Serial.print(chMed[1], 3); else Serial.print("ERR");
  Serial.print("\tIDE_RAW=");
  if (ideValid) Serial.print(ideTrue, 3); else Serial.print("ERR");
  Serial.print("\telapsedMs=");
  Serial.println(nowMs - calibrationStartMs);

  if ((nowMs - calibrationStartMs) >= CALIBRATION_TIME_MS) {
    if (ideBaselineSamples > 0) {
      ideBaselinePf = (float)(ideBaselineSum / (double)ideBaselineSamples);
      baselineReady = true;
    }

    Serial.println("== CALIBRATION COMPLETE ==");
    Serial.print("IDE baseline pF = ");
    Serial.println(ideBaselinePf, 3);
    Serial.println("[TUNE] Contact threshold should be validated against repeated fish-contact trials.");

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

static void sendPacket(float idePf, bool ideValid,
                       bool stableNow, bool sessionValid, bool finalPacket)
{
  bool clamped = false;
  int16_t ide_mpF = ideValid ? pfToMilliPfClamped(idePf, clamped) : 0;

  uint8_t flags = 0;
  if (stableNow)    flags |= FLAG_STABLE_NOW;
  if (ideValid)     flags |= FLAG_IDE_VALID;
  if (sessionValid) flags |= FLAG_SESSION_VALID;
  if (finalPacket)  flags |= FLAG_FINAL;
  if (clamped)      flags |= FLAG_CLAMPED;

  ide_packet_t pkt;
  pkt.seq     = gSeq++;
  pkt.ide_mpF = ide_mpF;
  pkt.flags   = flags;

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

  ide_packet_t initPkt = {0, 0, 0};
  gPktChr->setValue((uint8_t*)&initPkt, sizeof(initPkt));

  svc->start();

  gAdvertising = BLEDevice::getAdvertising();
  gAdvertising->addServiceUUID(UUID_SVC_IDE);
  gAdvertising->setScanResponse(true);
  startBleAdvertising("setupBle");

  Serial.println("✓ BLE notify service started");
}

static void finishInvalidSession(float idePf, bool ideValid, FailureReason reason)
{
  setFailure(reason);
  sendPacket(idePf, ideValid, false, false, true);

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
  const uint8_t usedChannels[NUM_USED_CHANNELS] = { IDE_CH_A, IDE_CH_B };

  for (uint8_t i = 0; i < NUM_USED_CHANNELS; i++) {
    float cap_pf = readChannelPfNoCapdac(usedChannels[i]);

    if (!isnan(cap_pf)) {
      pushSample(rawWin[i], rawCount[i], rawIdx[i], cap_pf);
    }
    delay(10);
  }

  float chMed[NUM_USED_CHANNELS];
  bool  chValid[NUM_USED_CHANNELS];

  for (uint8_t i = 0; i < NUM_USED_CHANNELS; i++) {
    chMed[i] = medianOf(rawWin[i], rawCount[i]);
    chValid[i] = !isnan(chMed[i]);
  }

  const bool  ideValid = chValid[0] && chValid[1];
  const float ideTrue  = ideValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;
  const float ideCal   = ideValid ? (ideTrue - ideBaselinePf) : NAN;
  const float ideDiff  = ideValid ? (chMed[0] - chMed[1]) : NAN;

  if (ideValid) {
    pushSample(ideDiffWin, ideDiffCount, ideDiffIdx, ideDiff);
    pushSample(ideCalWin,  ideCalCount,  ideCalIdx,  ideCal);
  }

  const bool diffStable  = ideValid && isStableSpread(ideDiffWin, ideDiffCount, STABLE_SPREAD_PF);
  const bool valueStable = ideValid && isStableSpread(ideCalWin,  ideCalCount,  VALUE_SPREAD_PF);
  const bool localStableNow = diffStable && valueStable;

  const float ideCalMed = medianOf(ideCalWin, ideCalCount);
  const bool contactQualifiedNow = hasContactSignature(ideCalMed, ideValid);

  const uint32_t dt = (lastTickMs == 0) ? MEASUREMENT_DELAY_MS : (nowMs - lastTickMs);
  lastTickMs = nowMs;

  if (!ideValid) {
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
        Serial.print("[CONTACT] Rejected stable window: ideMed=");
        if (!isnan(ideCalMed)) Serial.print(ideCalMed, 3); else Serial.print("ERR");
        Serial.print(" threshold=");
        Serial.println(CONTACT_MIN_PF_IDE, 3);
      }
    } else if (contactQualifiedMs < LOCK_STABLE_HOLD_MS) {
      setState(ST_REFERENCE_LOCKING);
    }
  }

  if (!referenceLocked && localStableNow && contactQualifiedNow &&
      contactQualifiedMs >= LOCK_STABLE_HOLD_MS) {
    ideRefPf = ideCalMed;
    referenceLocked = true;
    setState(ST_MEASURING_VALID);

    Serial.println("[LOCK] Reference locked after qualified contact dwell");
    Serial.print("[LOCK] ideRef=");
    Serial.println(ideRefPf, 3);
  }

  const bool continuity =
    referenceLocked && !isnan(ideCalMed) && (fabsf(ideCalMed - ideRefPf) <= REFERENCE_TOL_PF);

  const bool stableNow = referenceLocked && localStableNow && continuity;
  const bool continuityBroken = referenceLocked && localStableNow && !continuity;

  ledWrite(LED_STABILITY_PIN, stableNow);

  if (stableNow) {
    stableAccumMs += dt;
    stableRunMs += dt;
    sessionStableTicks++;

    ideStableSum += (double)ideCal;
    ideStableSamples++;

    sendPacket(ideCal, ideValid, true, false, false);
  } else {
    stableRunMs = 0;
    if (referenceLocked && !continuity) {
      sessionRejectedContinuityTicks++;
    }
  }

  const uint32_t elapsed = nowMs - sessionStartMs;
  const bool sessionValid   = (stableAccumMs >= REQUIRED_STABLE_ACCUM_MS);
  const bool timedOut       = (elapsed >= SESSION_TIMEOUT_MS);
  const bool contactTimedOut = (!referenceLocked && elapsed >= CONTACT_DETECT_TIMEOUT_MS);

  Serial.print("state=");
  Serial.print(stateName(state));
  Serial.print("\tCH0=");
  if (chValid[0]) Serial.print(chMed[0], 3); else Serial.print("ERR");
  Serial.print("\tCH1=");
  if (chValid[1]) Serial.print(chMed[1], 3); else Serial.print("ERR");
  Serial.print("\tIDE_CAL=");
  if (ideValid) Serial.print(ideCal, 3); else Serial.print("ERR");
  Serial.print("\tIDE_DIFF=");
  if (ideValid) Serial.print(ideDiff, 3); else Serial.print("ERR");
  Serial.print("\tlocalStableNow=");
  Serial.print(localStableNow ? 1 : 0);
  Serial.print("\tcontactQualifiedNow=");
  Serial.print(contactQualifiedNow ? 1 : 0);
  Serial.print("\tcontactQualifiedMs=");
  Serial.print(contactQualifiedMs);
  Serial.print("\trefLocked=");
  Serial.print(referenceLocked ? 1 : 0);
  Serial.print("\tideRef=");
  if (referenceLocked) Serial.print(ideRefPf, 3); else Serial.print("NA");
  Serial.print("\tideMed=");
  if (!isnan(ideCalMed)) Serial.print(ideCalMed, 3); else Serial.print("ERR");
  Serial.print("\tcontinuity=");
  Serial.print(continuity ? 1 : 0);
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
    finishInvalidSession(ideCal, ideValid, FAIL_CONTINUITY_BROKEN);
    return true;
  }

  if (contactTimedOut) {
    finishInvalidSession(ideCal, ideValid, FAIL_TIMEOUT_NO_CONTACT);
    return true;
  }

  if (sessionValid || timedOut) {
    if (sessionValid) {
      const bool ideAvgValid = (ideStableSamples > 0);
      const float ideAvg = ideAvgValid
        ? (float)(ideStableSum / (double)ideStableSamples)
        : NAN;

      sendPacket(ideAvg, ideAvgValid, stableNow, true, true);

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
      finishInvalidSession(
        ideCal,
        ideValid,
        referenceLocked ? FAIL_TIMEOUT_UNSTABLE : FAIL_TIMEOUT_NO_CONTACT
      );
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
  pinMode(LED_MEASURING_PIN, OUTPUT);
  pinMode(LED_CLASS_FRESH_PIN, OUTPUT);
  pinMode(LED_CLASS_MODERATE_PIN, OUTPUT);
  pinMode(LED_CLASS_SPOILED_PIN, OUTPUT);

  ledWrite(LED_POWER_RED_PIN, true);
  ledWrite(LED_STABILITY_PIN, false);
  ledWrite(LED_MEASURING_PIN, false);
  resetClassificationLeds();

  Wire1.setPins(I2C_SDA, I2C_SCL);

  Serial.println("FDC1004 BLE Flow: one IDE only (CH0 + CH1), button-start, qualified contact lock, stable sample notify, FINAL notify");

  if (!capacitanceSensor.begin()) {
    Serial.println("✗ FDC1004 init failed");
    while (1) delay(1000);
  }

  if (!capacitanceSensor.isConnected()) {
    Serial.println("✗ FDC1004 not responding");
    while (1) delay(1000);
  }

  Serial.println("✓ FDC1004 OK");

  capacitanceSensor.setCapdac(FDC1004_CHANNEL_0, 0);
  capacitanceSensor.setCapdac(FDC1004_CHANNEL_1, 0);
  
  setupBle();

  resetCalibration();
  calibrationStartMs = millis();
  setState(ST_CALIBRATING);

  Serial.println("== STARTUP CALIBRATION ==");
  Serial.println("Keep IDE on open air for 5 seconds...");
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
    if (!baselineReady) {
      Serial.println("[WARN] Baseline not ready yet");
      return;
    }

    clearWindows();
    resetSessionStats();
    sessionStartMs = millis();

    setState(ST_CONTACT_DETECTING);
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, true);

    Serial.println("== SESSION START ==");
    Serial.print("[CONFIG] contact threshold IDE = ");
    Serial.println(CONTACT_MIN_PF_IDE, 3);
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