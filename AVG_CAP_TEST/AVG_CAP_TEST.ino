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
static const int BUTTON_PIN            = 27; // Active-LOW button to GND, uses INPUT_PULLUP
static const int LED_POWER_RED_PIN     = 25; // Red LED (power)
static const int LED_STABLE_GRN_PIN    = 26; // Green LED (stable)
static const int LED_MEASURE_ORANGE_PIN = 14; // Orange LED (measuring mode)

// =============================
// I2C + Sensor
// =============================
static const int I2C_SDA = 21;
static const int I2C_SCL = 22;

const uint8_t  NUM_CHANNELS = 4;
const uint16_t MEASUREMENT_DELAY_MS = 500;

FDC1004 capacitanceSensor(&Wire1, FDC1004_RATE_100HZ);

// =============================
// Filtering / Stability Settings
// =============================
const uint8_t MEDIAN_WIN = 5;
const float   STABLE_SPREAD_PF = 0.80f;

// Rolling median windows per channel (real capacitance pF)
static float   chWin[NUM_CHANNELS][MEDIAN_WIN];
static uint8_t chCount[NUM_CHANNELS] = {0};
static uint8_t chIdx[NUM_CHANNELS]   = {0};

// Differential windows used ONLY for stability checking
static float   ide1DiffWin[MEDIAN_WIN];
static float   ide2DiffWin[MEDIAN_WIN];
static uint8_t ide1DiffCount = 0, ide1DiffIdx = 0;
static uint8_t ide2DiffCount = 0, ide2DiffIdx = 0;

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
enum State { ST_IDLE, ST_MEASURING };
static State state = ST_IDLE;

static uint32_t sessionStartMs = 0;
static uint32_t lastTickMs = 0;
static uint32_t stableAccumMs = 0;   // cumulative stable time
static uint32_t stableRunMs   = 0;   // current continuous stable run (debug only)

// =============================
// Stable-only accumulators for FINAL summary
// =============================
static double ide1StableSum = 0.0;
static double ide2StableSum = 0.0;
static uint16_t ide1StableSamples = 0;
static uint16_t ide2StableSamples = 0;

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
  for (uint8_t i = 0; i < MEDIAN_WIN; i++) {
    ide1DiffWin[i] = 0.0f;
    ide2DiffWin[i] = 0.0f;
  }
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
  pkt.seq = gSeq++;
  pkt.ide1_mpF = ide1_mpF;
  pkt.ide2_mpF = ide2_mpF;
  pkt.flags = flags;

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
// - True capacitance is sent to Flutter
// - Stable sample packets are notified on every stable tick
// - FINAL packet sent once on success or timeout
// =============================
static bool measurementTickAndMaybeFinish(uint32_t nowMs)
{
  // Read CH0..CH3 and update rolling windows
  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    fdc1004_capacitance_t m =
        capacitanceSensor.getCapacitanceMeasurement((fdc1004_channel_t)ch);

    if (!isnan(m.capacitance_pf)) {
      pushSample(chWin[ch], chCount[ch], chIdx[ch], m.capacitance_pf);
    }
    delay(10);
  }

  // Median-filtered real capacitance per channel
  float chMed[NUM_CHANNELS];
  bool  chValid[NUM_CHANNELS];

  for (uint8_t ch = 0; ch < NUM_CHANNELS; ch++) {
    chMed[ch] = medianOf(chWin[ch], chCount[ch]);
    chValid[ch] = !isnan(chMed[ch]);
  }

  // True capacitance values for reporting / packets
  const bool ide1TrueValid = chValid[0] && chValid[1];
  const bool ide2TrueValid = chValid[2] && chValid[3];

  const float ide1True = ide1TrueValid ? (0.5f * (chMed[0] + chMed[1])) : NAN;
  const float ide2True = ide2TrueValid ? (0.5f * (chMed[2] + chMed[3])) : NAN;

  // Differential values ONLY for stability
  const bool ide1DiffValid = ide1TrueValid;
  const bool ide2DiffValid = ide2TrueValid;

  const float ide1Diff = ide1DiffValid ? (chMed[0] - chMed[1]) : NAN;
  const float ide2Diff = ide2DiffValid ? (chMed[2] - chMed[3]) : NAN;

  if (ide1DiffValid) pushSample(ide1DiffWin, ide1DiffCount, ide1DiffIdx, ide1Diff);
  if (ide2DiffValid) pushSample(ide2DiffWin, ide2DiffCount, ide2DiffIdx, ide2Diff);

  const bool stable1 = ide1DiffValid && isStableSpread(ide1DiffWin, ide1DiffCount, STABLE_SPREAD_PF);
  const bool stable2 = ide2DiffValid && isStableSpread(ide2DiffWin, ide2DiffCount, STABLE_SPREAD_PF);
  const bool stableNow = stable1 && stable2;

  ledWrite(LED_STABLE_GRN_PIN, stableNow);

  // Accurate dt per tick
  uint32_t dt = (lastTickMs == 0) ? MEASUREMENT_DELAY_MS : (nowMs - lastTickMs);
  lastTickMs = nowMs;

  // Track cumulative stable time and current continuous run
  if (stableNow) {
    stableAccumMs += dt;
    stableRunMs += dt;

    // accumulate stable-only averages for FINAL summary
    if (ide1TrueValid) {
      ide1StableSum += (double)ide1True;
      ide1StableSamples++;
    }
    if (ide2TrueValid) {
      ide2StableSum += (double)ide2True;
      ide2StableSamples++;
    }

    // send stable sample packet on every stable tick
    sendPacket(ide1True, ide1TrueValid, ide2True, ide2TrueValid,
               true, false, false);
  } else {
    stableRunMs = 0;
  }

  const uint32_t elapsed = nowMs - sessionStartMs;
  const bool sessionValid = (stableAccumMs >= REQUIRED_STABLE_ACCUM_MS);
  const bool timedOut = (elapsed >= SESSION_TIMEOUT_MS);

  // Debug serial
  Serial.print("CH0=");
  if (chValid[0]) Serial.print(chMed[0], 3); else Serial.print("ERR");
  Serial.print("\tCH1=");
  if (chValid[1]) Serial.print(chMed[1], 3); else Serial.print("ERR");
  Serial.print("\tCH2=");
  if (chValid[2]) Serial.print(chMed[2], 3); else Serial.print("ERR");
  Serial.print("\tCH3=");
  if (chValid[3]) Serial.print(chMed[3], 3); else Serial.print("ERR");

  Serial.print("\tIDE1_TRUE=");
  if (ide1TrueValid) Serial.print(ide1True, 3); else Serial.print("ERR");
  Serial.print("\tIDE2_TRUE=");
  if (ide2TrueValid) Serial.print(ide2True, 3); else Serial.print("ERR");

  Serial.print("\tstableNow=");
  Serial.print(stableNow ? 1 : 0);
  Serial.print("\tstableRunMs=");
  Serial.print(stableRunMs);
  Serial.print("\tstableAccumMs=");
  Serial.print(stableAccumMs);
  Serial.print("\telapsedMs=");
  Serial.println(elapsed);

  // Finish if enough stable time accumulated OR timeout
  if (sessionValid || timedOut) {
    // FINAL packet carries stable-only average summary
    bool ide1AvgValid = (ide1StableSamples > 0);
    bool ide2AvgValid = (ide2StableSamples > 0);

    float ide1Avg = ide1AvgValid ? (float)(ide1StableSum / (double)ide1StableSamples) : NAN;
    float ide2Avg = ide2AvgValid ? (float)(ide2StableSum / (double)ide2StableSamples) : NAN;

    sendPacket(ide1Avg, ide1AvgValid, ide2Avg, ide2AvgValid,
               stableNow, sessionValid, true);

    Serial.println(sessionValid
      ? "== FINAL: VALID SESSION =="
      : "== FINAL: TIMEOUT / INVALID SESSION ==");

    ledWrite(LED_STABLE_GRN_PIN, false);
    ledWrite(LED_MEASURE_ORANGE_PIN, false);
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
  pinMode(LED_STABLE_GRN_PIN, OUTPUT);
  if (LED_MEASURE_ORANGE_PIN >= 0) pinMode(LED_MEASURE_ORANGE_PIN, OUTPUT);

  ledWrite(LED_POWER_RED_PIN, true);
  ledWrite(LED_STABLE_GRN_PIN, false);
  ledWrite(LED_MEASURE_ORANGE_PIN, false);

  Wire1.setPins(I2C_SDA, I2C_SCL);

  Serial.println("FDC1004 BLE Flow: button-start, stable sample notify, FINAL notify");
  Serial.println("Press ESP32 button to start measurement session.");

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

  state = ST_IDLE;
}

void loop()
{
  // Start session from physical button only when idle
  if (state == ST_IDLE && buttonPressedEvent()) {
    clearWindows();
    resetSessionStats();
    sessionStartMs = millis();

    state = ST_MEASURING;
    ledWrite(LED_STABLE_GRN_PIN, false);
    ledWrite(LED_MEASURE_ORANGE_PIN, true);

    Serial.println("== SESSION START ==");
  }

  if (state == ST_IDLE) {
    // True idle: no sampling, no notify, green LED off
    ledWrite(LED_STABLE_GRN_PIN, false);
    ledWrite(LED_MEASURE_ORANGE_PIN, false);
    delay(50);
    return;
  }

  // Measuring tick
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