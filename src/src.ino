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
static const int BUTTON_PIN             = 27; // Active-LOW button to GND, uses INPUT_PULLUP
static const int LED_POWER_RED_PIN      = 15; // Red LED (power)
static const int LED_STABILITY_PIN     = 2; // Green LED (stable)
static const int LED_MEASURING_PIN      = 12; // Orange LED (measuring mode)
static const int LED_CLASS_FRESH_PIN      = 0; // AI model Classification (Fresh)
static const int LED_CLASS_MODERATE_PIN      = 4; // AI model Classification (Moderately Fresh)
static const int LED_CLASS_SPOILED_PIN      = 16; // AI model Classification (Spoiled)

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
const uint8_t MEDIAN_WIN         = 5;
const float   STABLE_SPREAD_PF   = 0.80f; // first-layer differential stability
const float   VALUE_SPREAD_PF    = 0.30f; // second-layer corrected-value stability

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
static const uint32_t REQUIRED_STABLE_ACCUM_MS = 5000;  // 5 seconds cumulative stable
static const uint32_t SESSION_TIMEOUT_MS       = 20000; // 20 seconds timeout

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
static bool gDeviceConnected = false;
static uint16_t gSeq = 0;

// =============================
// State machine
// =============================
enum State {
  ST_CALIBRATING,
  ST_IDLE,
  ST_MEASURING
};
static State state = ST_CALIBRATING;

static uint32_t sessionStartMs = 0;
static uint32_t lastTickMs     = 0;
static uint32_t stableAccumMs  = 0; // cumulative stable time
static uint32_t stableRunMs    = 0; // current continuous stable run (debug only)

// =============================
// Stable-only accumulators for FINAL summary
// These store baseline-corrected values gathered only while stable.
// =============================
static double ide1StableSum = 0.0;
static double ide2StableSum = 0.0;
static uint16_t ide1StableSamples = 0;
static uint16_t ide2StableSamples = 0;

// =============================
// Startup calibration
// On boot, measure open-air capacitance for 5 seconds and store
// that average as the baseline to subtract from reported readings.
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
// Session continuity lock (Option B)
// Once a stable fish-contact state is found, lock onto the median
// corrected value of each IDE and require future stable readings to
// remain close to that same region. If continuity breaks, invalidate
// the session immediately.
// =============================
static bool  referenceLocked = false;
static float ide1RefPf       = 0.0f;
static float ide2RefPf       = 0.0f;
static const float REFERENCE_TOL_PF = 0.50f;

// =============================
// Callbacks
// =============================
class ServerCallbacks : public BLEServerCallbacks {
  void onConnect(BLEServer*) override {
    gDeviceConnected = true;
  }

  void onDisconnect(BLEServer*) override {
    gDeviceConnected = false;
    BLEDevice::startAdvertising();
  }
};

// =============================
// Helpers
// =============================
static inline void ledWrite(int pin, bool on) {
  if (pin < 0) return;
  digitalWrite(pin, on ? HIGH : LOW);
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
  // Reset timing and accumulators used during startup calibration.
  calibrationStartMs = 0;

  // Running sums used to compute the average open-air baseline.
  ide1BaselineSum = 0.0;
  ide2BaselineSum = 0.0;

  // Number of valid samples collected for each IDE pair.
  ide1BaselineSamples = 0;
  ide2BaselineSamples = 0;

  // Final computed baseline values in pF.
  ide1BaselinePf = 0.0f;
  ide2BaselinePf = 0.0f;

  // This becomes true once the calibration window completes.
  baselineReady = false;

  // Clear rolling windows so calibration starts from a clean state.
  clearWindows();
}

static bool calibrationTickAndFinish(uint32_t nowMs)
{
  // ------------------------------------------------------------
  // Startup calibration phase:
  // For 5 seconds after power-up, measure the electrodes in
  // open-air condition and compute the baseline capacitance.
  //
  // This baseline is later subtracted from IDE1 / IDE2 TRUE
  // capacitance so Flutter receives baseline-corrected values.
  // ------------------------------------------------------------

  // Step 1: Read CH0..CH3 and update rolling windows.
  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    fdc1004_capacitance_t m =
        capacitanceSensor.getCapacitanceMeasurement((fdc1004_channel_t)ch);

    if (!isnan(m.capacitance_pf)) {
      pushSample(chWin[ch], chCount[ch], chIdx[ch], m.capacitance_pf);
    }

    delay(10);
  }

  // Step 2: Compute median-filtered capacitance for each channel.
  float chMed[NUM_CHANNELS];
  bool chValid[NUM_CHANNELS];

  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    chMed[ch] = medianOf(chWin[ch], chCount[ch]);
    chValid[ch] = !isnan(chMed[ch]);
  }

  // Step 3: Compute TRUE capacitance for each IDE pair.
  // IDE1 = average(CH0, CH1)
  // IDE2 = average(CH2, CH3)
  const bool ide1TrueValid = chValid[0] && chValid[1];
  const bool ide2TrueValid = chValid[2] && chValid[3];

  const float ide1True =
      ide1TrueValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;
  const float ide2True =
      ide2TrueValid ? (0.5f * (chMed[2] + chMed[3])) : NAN;

  // Step 4: Accumulate raw TRUE capacitance values into baseline sums.
  if (ide1TrueValid) {
    ide1BaselineSum += (double)ide1True;
    ide1BaselineSamples++;
  }

  if (ide2TrueValid) {
    ide2BaselineSum += (double)ide2True;
    ide2BaselineSamples++;
  }

  // Step 5: Print calibration progress for serial debugging.
  Serial.print("[CAL] IDE1_RAW=");
  if (ide1TrueValid) {
    Serial.print(ide1True, 3);
  } else {
    Serial.print("ERR");
  }

  Serial.print("\tIDE2_RAW=");
  if (ide2TrueValid) {
    Serial.print(ide2True, 3);
  } else {
    Serial.print("ERR");
  }

  Serial.print("\telapsedMs=");
  Serial.println(nowMs - calibrationStartMs);

  // Step 6: Finish calibration once the 5-second window has elapsed.
  if ((nowMs - calibrationStartMs) >= CALIBRATION_TIME_MS) {
    if (ide1BaselineSamples > 0) {
      ide1BaselinePf =
          (float)(ide1BaselineSum / (double)ide1BaselineSamples);
    }

    if (ide2BaselineSamples > 0) {
      ide2BaselinePf =
          (float)(ide2BaselineSum / (double)ide2BaselineSamples);
    }

    baselineReady = (ide1BaselineSamples > 0) || (ide2BaselineSamples > 0);

    Serial.println("== CALIBRATION COMPLETE ==");
    Serial.print("IDE1 baseline pF = ");
    Serial.println(ide1BaselinePf, 3);
    Serial.print("IDE2 baseline pF = ");
    Serial.println(ide2BaselinePf, 3);

    // Clear windows so the actual measurement session starts fresh.
    clearWindows();
    return true;
  }

  // Calibration still in progress.
  return false;
}

static void resetSessionStats()
{
  stableAccumMs = 0;
  stableRunMs   = 0;
  ide1StableSum = 0.0;
  ide2StableSum = 0.0;
  ide1StableSamples = 0;
  ide2StableSamples = 0;
  lastTickMs = 0;

  // Reset the session continuity lock so every button press starts fresh.
  referenceLocked = false;
  ide1RefPf = 0.0f;
  ide2RefPf = 0.0f;
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

  BLEAdvertising *adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(UUID_SVC_IDE);
  adv->setScanResponse(true);
  adv->start();

  Serial.println("✓ BLE notify service started");
}

// =============================
// One measurement tick
// - Differential is used ONLY for stability
// - TRUE capacitance is baseline-corrected for reporting
// - Stable sample packets are notified on every stable tick
// - FINAL packet is sent once on success or timeout
// =============================
static bool measurementTickAndMaybeFinish(uint32_t nowMs)
{
  // Step 1: Read CH0..CH3 and update rolling windows.
  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    fdc1004_capacitance_t m =
        capacitanceSensor.getCapacitanceMeasurement((fdc1004_channel_t)ch);

    if (!isnan(m.capacitance_pf)) {
      pushSample(chWin[ch], chCount[ch], chIdx[ch], m.capacitance_pf);
    }
    delay(10);
  }

  // Step 2: Compute median-filtered raw capacitance for each channel.
  float chMed[NUM_CHANNELS];
  bool  chValid[NUM_CHANNELS];

  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    chMed[ch] = medianOf(chWin[ch], chCount[ch]);
    chValid[ch] = !isnan(chMed[ch]);
  }

  // Step 3: Compute TRUE capacitance values for IDE1 and IDE2.
  const bool ide1TrueValid = chValid[0] && chValid[1];
  const bool ide2TrueValid = chValid[2] && chValid[3];

  const float ide1True = ide1TrueValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;
  const float ide2True = ide2TrueValid ? (0.5f * (chMed[2] + chMed[3])) : NAN;

  // Step 4: Subtract the startup baseline so the reported values represent
  // capacitance above the open-air/base level.
  const float ide1Cal = ide1TrueValid ? (ide1True - ide1BaselinePf) : NAN;
  const float ide2Cal = ide2TrueValid ? (ide2True - ide2BaselinePf) : NAN;

  // Step 5: Compute pseudo-differential values used for first-layer electrical stability.
  const bool ide1DiffValid = ide1TrueValid;
  const bool ide2DiffValid = ide2TrueValid;

  const float ide1Diff = ide1DiffValid ? (chMed[0] - chMed[1]) : NAN;
  const float ide2Diff = ide2DiffValid ? (chMed[2] - chMed[3]) : NAN;

  if (ide1DiffValid) pushSample(ide1DiffWin, ide1DiffCount, ide1DiffIdx, ide1Diff);
  if (ide2DiffValid) pushSample(ide2DiffWin, ide2DiffCount, ide2DiffIdx, ide2Diff);

  // Step 6: Store baseline-corrected TRUE capacitance for second-layer value stability.
  if (ide1TrueValid) pushSample(ide1CalWin, ide1CalCount, ide1CalIdx, ide1Cal);
  if (ide2TrueValid) pushSample(ide2CalWin, ide2CalCount, ide2CalIdx, ide2Cal);

  // Layer 1: differential/electrical stability
  const bool diffStable1 = ide1DiffValid && isStableSpread(ide1DiffWin, ide1DiffCount, STABLE_SPREAD_PF);
  const bool diffStable2 = ide2DiffValid && isStableSpread(ide2DiffWin, ide2DiffCount, STABLE_SPREAD_PF);

  // Layer 2: corrected-value local stability
  const bool valueStable1 = ide1TrueValid && isStableSpread(ide1CalWin, ide1CalCount, VALUE_SPREAD_PF);
  const bool valueStable2 = ide2TrueValid && isStableSpread(ide2CalWin, ide2CalCount, VALUE_SPREAD_PF);

  // Local stability must pass before a session can lock or continue.
  const bool localStableNow = diffStable1 && diffStable2 && valueStable1 && valueStable2;

  // Use the median of the corrected-value windows as the session reference.
  const float ide1CalMed = medianOf(ide1CalWin, ide1CalCount);
  const float ide2CalMed = medianOf(ide2CalWin, ide2CalCount);

  // If no reference is locked yet and the signal is locally stable,
  // lock the current fish-contact state using the corrected-value medians.
  if (!referenceLocked && localStableNow) {
    ide1RefPf = ide1CalMed;
    ide2RefPf = ide2CalMed;
    referenceLocked = true;
  }

  // Layer 3 / Option B: session continuity check.
  // Once locked, the current corrected-value medians must remain close to the
  // original reference. If not, the fish/contact state changed too much.
  const bool continuity1 =
      referenceLocked && !isnan(ide1CalMed) && (fabsf(ide1CalMed - ide1RefPf) <= REFERENCE_TOL_PF);
  const bool continuity2 =
      referenceLocked && !isnan(ide2CalMed) && (fabsf(ide2CalMed - ide2RefPf) <= REFERENCE_TOL_PF);

  const bool stableNow = localStableNow && continuity1 && continuity2;
  const bool continuityBroken = referenceLocked && localStableNow && (!continuity1 || !continuity2);

  // Green LED mirrors the final acceptance decision.
  ledWrite(LED_STABILITY_PIN, stableNow);

  // Accurate dt per tick.
  uint32_t dt = (lastTickMs == 0) ? MEASUREMENT_DELAY_MS : (nowMs - lastTickMs);
  lastTickMs = nowMs;

  // Step 7: If final stability is achieved, accumulate stable time and collect
  // baseline-corrected values that will later be averaged into the FINAL packet.
  if (stableNow) {
    stableAccumMs += dt;
    stableRunMs += dt;

    if (ide1TrueValid) {
      ide1StableSum += (double)ide1Cal;
      ide1StableSamples++;
    }
    if (ide2TrueValid) {
      ide2StableSum += (double)ide2Cal;
      ide2StableSamples++;
    }

    // Send a live packet on every accepted stable tick.
    sendPacket(ide1Cal, ide1TrueValid, ide2Cal, ide2TrueValid,
               true, false, false);
  } else {
    stableRunMs = 0;
  }

  const uint32_t elapsed = nowMs - sessionStartMs;
  const bool sessionValid = (stableAccumMs >= REQUIRED_STABLE_ACCUM_MS);
  const bool timedOut     = (elapsed >= SESSION_TIMEOUT_MS);

  // Debug serial output.
  Serial.print("CH0=");
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
  Serial.print("\tcontinuityBroken=");
  Serial.print(continuityBroken ? 1 : 0);
  Serial.print("\tstableNow=");
  Serial.print(stableNow ? 1 : 0);
  Serial.print("\tstableRunMs=");
  Serial.print(stableRunMs);
  Serial.print("\tstableAccumMs=");
  Serial.print(stableAccumMs);
  Serial.print("\telapsedMs=");
  Serial.println(elapsed);

  // If continuity breaks after the session has already locked onto a fish-contact
  // state, immediately invalidate the session and force a restart.
  if (continuityBroken) {
    sendPacket(ide1Cal, ide1TrueValid, ide2Cal, ide2TrueValid,
               false, false, true);

    Serial.println("== FINAL: CONTINUITY BROKEN / INVALID SESSION ==");

    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, false);
    return true;
  }

  // Step 8: Finish if enough stable time has accumulated OR timeout occurs.
  if (sessionValid || timedOut) {
    bool ide1AvgValid = (ide1StableSamples > 0);
    bool ide2AvgValid = (ide2StableSamples > 0);

    float ide1Avg = ide1AvgValid ? (float)(ide1StableSum / (double)ide1StableSamples) : NAN;
    float ide2Avg = ide2AvgValid ? (float)(ide2StableSum / (double)ide2StableSamples) : NAN;

    // FINAL packet carries the stable-only average summary.
    sendPacket(ide1Avg, ide1AvgValid, ide2Avg, ide2AvgValid,
               stableNow, sessionValid, true);

    Serial.println(sessionValid
      ? "== FINAL: VALID SESSION =="
      : "== FINAL: TIMEOUT / INVALID SESSION ==");

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

  ledWrite(LED_POWER_RED_PIN, true);
  ledWrite(LED_STABILITY_PIN, false);
  ledWrite(LED_MEASURING_PIN, false);

  Wire1.setPins(I2C_SDA, I2C_SCL);

  Serial.println("FDC1004 BLE Flow: button-start, stable sample notify, FINAL notify");

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

  // Start the device in calibration mode so open-air baseline is measured
  // before any user measurement sessions are allowed.
  resetCalibration();
  calibrationStartMs = millis();
  state = ST_CALIBRATING;

  Serial.println("== STARTUP CALIBRATION ==");
  Serial.println("Keep electrodes in open air for 5 seconds...");
}

void loop()
{
  // ------------------------------------------------------------
  // STATE: CALIBRATING
  // On power-up, spend 5 seconds measuring the electrode baseline
  // in open air before allowing sessions.
  // ------------------------------------------------------------
  if (state == ST_CALIBRATING) {
    ledWrite(LED_POWER_RED_PIN, true);
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, false);

    static uint32_t lastCalibrationTickMs = 0;
    const uint32_t now = millis();

    if (now - lastCalibrationTickMs >= MEASUREMENT_DELAY_MS) {
      lastCalibrationTickMs = now;

      const bool done = calibrationTickAndFinish(now);
      if (done) {
        state = ST_IDLE;

        Serial.println("== DEVICE READY ==");
        Serial.println("Press button to start measurement session.\n");
      }
    }

    return;
  }

  // Start session from physical button only when idle.
  if (state == ST_IDLE && buttonPressedEvent()) {
    clearWindows();
    resetSessionStats();
    sessionStartMs = millis();

    state = ST_MEASURING;
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, true);

    Serial.println("== SESSION START ==");
  }

  if (state == ST_IDLE) {
    // True idle: no sampling, no notifications, green/orange LEDs off.
    ledWrite(LED_STABILITY_PIN, false);
    ledWrite(LED_MEASURING_PIN, false);
    delay(50);
    return;
  }

  // STATE: MEASURING
  // Run one measurement tick every 500 ms.
  static uint32_t lastScheduleMs = 0;
  const uint32_t now = millis();

  if (now - lastScheduleMs >= MEASUREMENT_DELAY_MS) {
    lastScheduleMs = now;

    const bool finished = measurementTickAndMaybeFinish(now);
    if (finished) {
      state = ST_IDLE;
      Serial.println("== SESSION END (IDLE) ==");
      Serial.println("Press button again to start a new session.\n");
    }
  }
}
