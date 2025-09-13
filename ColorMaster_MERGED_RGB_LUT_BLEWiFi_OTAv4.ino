/**
 * basic2_with_blewifi_and_ota.ino
 *
 * BLE-driven CMYK+W motor controller using Nordic UART Service (NUS).
 * - Commands like "c100 m50 y0 k25 w200" run motors for given ms (blocking).
 * - Wi‑Fi credentials are provisioned over BLE (NVS/Preferences).
 * - OTA checks/installs from GitHub using saved credentials.
 * - Strong Serial logging added for all BLE activity and OTA steps.
 *
 * Platform: ESP32 / ESP32-S3 (Arduino core)
 */

#include <Arduino.h>
#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <HTTPClient.h>
#include <Update.h>
#include <math.h>

static bool extractFiveInts(const String& s, int& a, int& b, int& c, int& d, int& e) {
  const char* p = s.c_str();
  long vals[5]; int n = 0;
  while (*p && n < 5) {
    while (*p && !((*p >= '0' && *p <= '9') || *p=='-' )) p++;
    if (!*p) break;
    char* endp = nullptr;
    long v = strtol(p, &endp, 10);
    if (endp == p) break;
    vals[n++] = v;
    p = endp;
  }
  if (n == 5) { a=(int)vals[0]; b=(int)vals[1]; c=(int)vals[2]; d=(int)vals[3]; e=(int)vals[4]; return true; }
  return false;
}

static void rgbToCMYK_ms(int R, int G, int B, int grams, int& c_ms, int& m_ms, int& y_ms, int& k_ms);

// ===== CMYK floors and caps (from RGBBLE) =====
static const int C_MIN_MS = 100;   // floors only applied if channel > 0
static const int M_MIN_MS = 40;
static const int Y_MIN_MS = 40;
static const int K_MIN_MS = 40;

static const int C_MAX_MS = 1500; // tighten later per plateau
static const int M_MAX_MS = 1800;
static const int Y_MAX_MS = 2150;
static const int K_MAX_MS = 1700;

static const float WATER_MS_PER_ML = 120.0f; // update with your calibration
static const int   BASELINE_GRAMS   = 100;   // grams reference for RGB scaling


#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>

#include <Preferences.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/semphr.h>

// ====== RTOS Task Handles and Stack Sizes ======
TaskHandle_t bleTaskHandle = NULL;
TaskHandle_t wifiTaskHandle = NULL;
TaskHandle_t otaTaskHandle = NULL;
TaskHandle_t otaLedTaskHandle = NULL;
volatile bool otaLedBlink = false;
volatile bool otaLedStop = false;
volatile bool blePermanentlyOff = false;
SemaphoreHandle_t stateMutex;
#define BLE_TASK_STACK_SIZE  8192
#define WIFI_TASK_STACK_SIZE 8192
#define OTA_TASK_STACK_SIZE 16384

// ====== USER CONFIG: GitHub raw URLs for OTA ======
static const char* VERSION_URL  = "https://raw.githubusercontent.com/kaifsakes/dyedispenser_ota/main/version.txt";
static const char* FIRMWARE_URL = "https://raw.githubusercontent.com/kaifsakes/dyedispenser_ota/main/firmware.bin";
// Bump this locally when you flash; device compares against version.txt
static const char* CURRENT_VERSION = "1.0.0";

// ====== Motor pins (forward-only drive per channel) ======
#define C_IN1 38
#define C_IN2 37
#define M_IN1 48
#define M_IN2 47
#define Y_IN1 12
#define Y_IN2 13
#define K_IN1 21
#define K_IN2 14
#define W_IN1 9
#define W_IN2 10
#define LED_BLE   4
#define LED_OTAOK 5
#define LED_OTAPROG 6

// ====== BLE UUIDs (Nordic UART Service) ======
static const char* NUS_SERVICE_UUID = "6E400001-B5A3-F393-E0A9-E50E24DCCA9E";
static const char* NUS_RX_UUID      = "6E400002-B5A3-F393-E0A9-E50E24DCCA9E"; // Write
static const char* NUS_TX_UUID      = "6E400003-B5A3-F393-E0A9-E50E24DCCA9E"; // Notify

// ====== Globals ======
Preferences prefs;

BLEServer*         pServer  = nullptr;
BLEService*        pService = nullptr;
BLECharacteristic* pRxChar  = nullptr;
BLECharacteristic* pTxChar  = nullptr;
BLE2902*           pTxCcc   = nullptr;

volatile bool bleConnected = false;

String pendingCmd;
volatile bool cmdPending = false;

String wifiSsid = "";
String wifiPass = "";
String provBuf;  // accumulates partial wifi lines across writes
bool   wifiCredsLoaded = false;

volatile bool otaChecked   = false;
volatile bool otaPrompted  = false;
volatile bool otaDeclined  = false;
volatile bool update_available = false;

// BLE reassembly + provisioning fragments
String rxBuf;                 // accumulates chunks until newline or full line
String provSsidTmp = "";      // holds ssid until pass arrives
String provPassTmp = "";

// ====== Utilities ======
void sendToBLE(const String& msg) {
  if (pTxChar) {
    pTxChar->setValue(msg.c_str());
    pTxChar->notify();
  }
  Serial.println("[BLE->APP] " + msg);  // mirror to Serial always
}

bool loadWiFiCreds() {
  prefs.begin("wifi", /*RO=*/true);
  wifiSsid = prefs.getString("ssid", "");
  wifiPass = prefs.getString("pass", "");
  prefs.end();
  wifiCredsLoaded = (wifiSsid.length() && wifiPass.length());
  return wifiCredsLoaded;
}

void saveWiFiCreds(const String& ssid, const String& pass) {
  prefs.begin("wifi", /*RO=*/false);
  prefs.putString("ssid", ssid);
  prefs.putString("pass", pass);
  prefs.end();
  wifiSsid = ssid;
  wifiPass = pass;
  wifiCredsLoaded = true;
}

void clearWiFiCreds() {
  prefs.begin("wifi", /*RO=*/false);
  prefs.remove("ssid");
  prefs.remove("pass");
  prefs.end();
  wifiSsid = "";
  wifiPass = "";
  wifiCredsLoaded = false;
}

// ====== Motors ======
static inline void motorStop(uint8_t in1, uint8_t in2) {
  digitalWrite(in1, LOW);
  digitalWrite(in2, LOW);
}

static inline void motorForward(uint8_t in1, uint8_t in2, uint32_t ms) {
  digitalWrite(in1, HIGH);
  digitalWrite(in2, LOW);
  delay(ms);                     // blocking by design
  motorStop(in1, in2);
}



void handleCommand(const String& lineIn) {
  String line = lineIn; line.trim();
  if (line.length() == 0) return;

  // Accept START/STOP from the app
  if (line.equalsIgnoreCase("START")) {
    otaChecked = true; // allow immediate motor execution
    sendToBLE("STARTED");
    return;
  }
  if (line.equalsIgnoreCase("STOP")) {
    // No hard stop of motors here to avoid cutting power mid-step; just ack
    sendToBLE("STOPPED");
    return;
  }

  // 1) LOAD <ms>
  if (line.startsWith("load") || line.startsWith("LOAD")) {
    long ms = 0;
    int sp = line.indexOf(' ');
    if (sp > 0) ms = line.substring(sp+1).toInt();
    if (ms > 0) {
      motorForward(C_IN1, C_IN2, ms);
      motorForward(M_IN1, M_IN2, ms);
      motorForward(Y_IN1, Y_IN2, ms);
      motorForward(K_IN1, K_IN2, ms);
      motorForward(W_IN1, W_IN2, ms);
    }
    sendToBLE("DONE");
    return;
  }

  // 2) WATER <ml>  (accepts "water 5", "water 5 ml")
  if (line.startsWith("water") || line.startsWith("WATER")) {
    String rest = line.substring(5); rest.trim();
    long ml = 0;
    // Extract first number found
    const char* p = rest.c_str();
    while (*p && !((*p >= '0' && *p <= '9') || *p=='-')) p++;
    if (*p) ml = strtol(p, nullptr, 10);
    if (ml > 0) {
      unsigned long wms = (unsigned long) (ml * WATER_MS_PER_ML);
      motorForward(W_IN1, W_IN2, wms);
      sendToBLE(String(ml) + " ml DONE");
    } else {
      sendToBLE("ERR water <ml>");
    }
    return;
  }

  // 3) Robust numeric path: extract ANY 5 integers as R G B Wml grams
  {
    int R,G,B,Wml,grams;
    if (extractFiveInts(line, R,G,B,Wml,grams)) {
      int c_ms, m_ms, y_ms, k_ms;
      rgbToCMYK_ms(R,G,B,grams, c_ms,m_ms,y_ms,k_ms);
      unsigned long w_ms = (unsigned long)(max(0, Wml) * WATER_MS_PER_ML);

      if (c_ms>0) motorForward(C_IN1, C_IN2, c_ms);
      if (m_ms>0) motorForward(M_IN1, M_IN2, m_ms);
      if (y_ms>0) motorForward(Y_IN1, Y_IN2, y_ms);
      if (k_ms>0) motorForward(K_IN1, K_IN2, k_ms);
      if (w_ms>0) motorForward(W_IN1, W_IN2, w_ms);

      String resp = "C:" + String(c_ms) + ", M:" + String(m_ms) + ", Y:" + String(y_ms) + ", K:" + String(k_ms) +
                    ", W:" + String(Wml) + " ml, Volume:" + String(grams);
      sendToBLE(resp);
      return;
    }
  }

  // 4) Token pairs like "C 1000 M 500" or legacy "c1000 m500"
  long tC=0, tM=0, tY=0, tK=0, tW=0;
  {
    String s = line; s.trim();
    int idx=0;
    while (idx < s.length()) {
      while (idx < s.length() && s[idx]==' ') idx++;
      if (idx >= s.length()) break;
      char ch = tolower(s[idx]);
      if (ch=='c' || ch=='m' || ch=='y' || ch=='k' || ch=='w') {
        idx++;
        while (idx < s.length() && s[idx]==' ') idx++;
        int start=idx;
        while (idx < s.length() && isDigit((unsigned char)s[idx])) idx++;
        long val = (start<idx) ? s.substring(start, idx).toInt() : 0;
        switch (ch) {
          case 'c': tC = max(0L, val); break;
          case 'm': tM = max(0L, val); break;
          case 'y': tY = max(0L, val); break;
          case 'k': tK = max(0L, val); break;
          case 'w': tW = max(0L, val); break;
        }
      } else {
        while (idx < s.length() && s[idx] != ' ') idx++;
      }
    }
  }

  if (tC > 0) { motorForward(C_IN1, C_IN2, tC); sendToBLE("c motor " + String(tC) + " DONE"); }
  if (tM > 0) { motorForward(M_IN1, M_IN2, tM); sendToBLE("m motor " + String(tM) + " DONE"); }
  if (tY > 0) { motorForward(Y_IN1, Y_IN2, tY); sendToBLE("y motor " + String(tY) + " DONE"); }
  if (tK > 0) { motorForward(K_IN1, K_IN2, tK); sendToBLE("k motor " + String(tK) + " DONE"); }
  if (tW > 0) { motorForward(W_IN1, W_IN2, tW); sendToBLE("w motor " + String(tW) + " DONE"); }
}
bool isUpdateAvailable() {
  WiFiClientSecure client;
  client.setInsecure(); // lab use; pin a cert for production

  HTTPClient http;
  if (!http.begin(client, VERSION_URL)) {
    Serial.println("[OTA] http.begin(version) failed");
    return false;
  }
  int code = http.GET();
  if (code != HTTP_CODE_OK) {
    Serial.printf("[OTA] GET version.txt failed: %d\n", code);
    http.end();
    return false;
  }
  String remote = http.getString();
  http.end();
  remote.trim();
  Serial.printf("[OTA] current=%s remote=%s\n", CURRENT_VERSION, remote.c_str());
  return (remote.length() > 0 && remote != CURRENT_VERSION);
}

bool performOTA() {
  WiFiClientSecure client;
  client.setInsecure();

  HTTPClient http;
  if (!http.begin(client, FIRMWARE_URL)) {
    Serial.println("[OTA] http.begin(firmware) failed");
    return false;
  }

  int code = http.GET();
  if (code != HTTP_CODE_OK) {
    Serial.printf("[OTA] GET firmware.bin failed: %d\n", code);
    http.end();
    return false;
  }

  int total = http.getSize();
  WiFiClient* stream = http.getStreamPtr();

  if (!Update.begin(total > 0 ? total : UPDATE_SIZE_UNKNOWN)) {
    Serial.println("[OTA] Update.begin failed");
    http.end();
    return false;
  }

  sendToBLE("Starting OTA...");
  const size_t bufSize = 4096;
  uint8_t buf[bufSize];
  size_t written = 0;
  uint32_t lastNotify = millis();

  while (http.connected() && (written < (size_t)total || total <= 0)) {
    size_t avail = stream->available();
    if (avail) {
      size_t len = stream->readBytes(buf, min(avail, bufSize));
      if (len > 0) {
        if (Update.write(buf, len) != len) {
          Serial.println("[OTA] Update.write mismatch");
          Update.abort();
          http.end();
          return false;
        }
        written += len;
        if (millis() - lastNotify > 500) {
          if (total > 0) {
            int pct = (int)((written * 100ULL) / total);
            sendToBLE("OTA " + String(pct) + "%");
          } else {
            sendToBLE("OTA " + String(written) + " bytes");
          }
          lastNotify = millis();
        }
      }
    } else {
      delay(10);
    }
    if (total > 0 && written >= (size_t)total) break;
  }

  if (!Update.end(true)) {
    Serial.printf("[OTA] Update.end error: %s\n", Update.errorString());
    http.end();
    return false;
  }

  http.end();
  sendToBLE("OTA complete. Rebooting...");
  delay(1500);
  ESP.restart();
  return true; // not reached
}

void checkForOTAUpdate() {
  // Check available memory
  Serial.printf("[OTA] Free heap: %d bytes\n", ESP.getFreeHeap());
  
  // Ensure we have credentials
  if (!wifiCredsLoaded) loadWiFiCreds();
  if (!wifiCredsLoaded) {
    update_available = false;
    otaPrompted = false;
    otaChecked = true;
    sendToBLE("No Wi‑Fi credentials.\nSend:\n  wifi ssid=<SSID> pass=<PASS>\nThen 'ota-check'.");
    Serial.println("[OTA] Missing Wi‑Fi creds.");
    return;
  }

  Serial.printf("[OTA] Starting WiFi connection with SSID: '%s', pass length: %d\n", wifiSsid.c_str(), wifiPass.length());
  sendToBLE("Connecting Wi‑Fi for OTA check...");
  // Keep BLE fully active during OTA check
  Serial.println("[OTA] Keeping BLE active during WiFi operations for check...");
  
  Serial.printf("[OTA] WiFi.begin('%s', <hidden>)\n", wifiSsid.c_str());
  Serial.println("[OTA] Setting WiFi mode to STA...");
  WiFi.mode(WIFI_STA);
  delay(100);
  
  Serial.println("[OTA] Starting WiFi connection...");
  WiFi.begin(wifiSsid.c_str(), wifiPass.c_str());
  Serial.println("[OTA] WiFi.begin() called, waiting for connection...");

  unsigned long t0 = millis();
  Serial.println("[OTA] Waiting for WiFi connection...");
  while (WiFi.status() != WL_CONNECTED && millis() - t0 < 15000) { // Increased timeout to 15 seconds
    if ((millis() - t0) % 1000 == 0) { // Log every second
      int status = WiFi.status();
      String statusText = "";
      switch(status) {
        case WL_IDLE_STATUS: statusText = "IDLE"; break;
        case WL_NO_SSID_AVAIL: statusText = "NO_SSID"; break;
        case WL_SCAN_COMPLETED: statusText = "SCAN_COMPLETED"; break;
        case WL_CONNECTED: statusText = "CONNECTED"; break;
        case WL_CONNECT_FAILED: statusText = "CONNECT_FAILED"; break;
        case WL_CONNECTION_LOST: statusText = "CONNECTION_LOST"; break;
        case WL_DISCONNECTED: statusText = "DISCONNECTED"; break;
        default: statusText = "UNKNOWN(" + String(status) + ")"; break;
      }
      Serial.printf("[OTA] WiFi status: %s (%d), elapsed: %lu ms\n", statusText.c_str(), status, millis() - t0);
    }
    delay(100);
    
    // Add watchdog to prevent infinite hang
    if (millis() - t0 > 10000) { // After 10 seconds, try to recover
      Serial.println("[OTA] WiFi connection taking too long, attempting recovery...");
      WiFi.disconnect();
      delay(1000);
      WiFi.begin(wifiSsid.c_str(), wifiPass.c_str());
      t0 = millis(); // Reset timer
    }
  }

  if (WiFi.status() != WL_CONNECTED) {
    int finalStatus = WiFi.status();
    String statusText = "";
    switch(finalStatus) {
      case WL_IDLE_STATUS: statusText = "IDLE"; break;
      case WL_NO_SSID_AVAIL: statusText = "NO_SSID"; break;
      case WL_SCAN_COMPLETED: statusText = "SCAN_COMPLETED"; break;
      case WL_CONNECTED: statusText = "CONNECTED"; break;
      case WL_CONNECT_FAILED: statusText = "CONNECT_FAILED"; break;
      case WL_CONNECTION_LOST: statusText = "CONNECTION_LOST"; break;
      case WL_DISCONNECTED: statusText = "DISCONNECTED"; break;
      default: statusText = "UNKNOWN(" + String(finalStatus) + ")"; break;
    }
    Serial.printf("[OTA] WiFi connection failed after %lu ms. Final status: %s (%d)\n", millis() - t0, statusText.c_str(), finalStatus);
    sendToBLE("Wi‑Fi connect failed. Check SSID/pass. You can 'wifi clear' and re‑provision.");
    Serial.println("[OTA] Wi‑Fi connect failed.");
    return;
  }
  
  // WiFi connected successfully
  Serial.printf("[OTA] WiFi connected successfully after %lu ms!\n", millis() - t0);
  Serial.printf("[OTA] IP address: %s\n", WiFi.localIP().toString().c_str());
  Serial.printf("[OTA] RSSI: %d dBm\n", WiFi.RSSI());

  if (isUpdateAvailable()) {
    update_available = true;
    otaPrompted = true;
    otaChecked = true;
    otaDeclined = false;
    sendToBLE("OTA update available. Reply 'ota-yes' to install or 'ota-no' to skip.");
    Serial.println("[OTA] Update available — waiting for user decision.");
  } else {
    update_available = false;
    otaPrompted = false;
    otaChecked = true;
    sendToBLE("No OTA update. Ready for commands.");
    Serial.println("[OTA] No update available.");
  }

  WiFi.disconnect(true);
  WiFi.mode(WIFI_OFF);
  Serial.println("[OTA] Wi‑Fi disconnected after check.");
  Serial.printf("[OTA] Free heap after WiFi: %d bytes\n", ESP.getFreeHeap());
}

// ====== BLE Callbacks ======
class ServerCallbacks : public BLEServerCallbacks {
  void onConnect(BLEServer* server) override {
    bleConnected = true;
    Serial.println("[BLE] Central connected");
    sendToBLE("Connected. Provision Wi‑Fi with:\n  wifi ssid=<SSID> pass=<PASS>\nCheck: wifi?\nRun OTA check: ota-check");
  }
  void onDisconnect(BLEServer* server) override {
    bleConnected = false;
    Serial.println("[BLE] Central disconnected");
    if (!blePermanentlyOff) {
      server->startAdvertising();
      Serial.println("[BLE] Advertising restarted");
    }
  }
};

class CmdCallbacks : public BLECharacteristicCallbacks {
public:
  void onWrite(BLECharacteristic* chr) override {
    // Robust against chunking/newlines from BLE apps
    String chunk = String(chr->getValue().c_str());
    if (chunk.length() == 0) return;

    // Normalize CRLF -> LF and accumulate
    chunk.replace("\r", "\n");
    rxBuf += chunk;

    // Process complete lines first
    int nlPos;
    while ((nlPos = rxBuf.indexOf('\n')) >= 0) {
      String line = rxBuf.substring(0, nlPos);
      rxBuf.remove(0, nlPos + 1);
      line.trim();
      if (line.length() > 0) handleBleLine(line);
    }

    // Also attempt to parse current chunk (in case app never sends newline)
    String tryNow = chunk;
    tryNow.trim();
    if (tryNow.length() > 0) handleBleLine(tryNow);
  }

private:
  void handleBleLine(String v) {
    Serial.println("[BLE<-APP] " + v);

// ---- Wi‑Fi provisioning and helpers ----
if (v == "wifi?" || v == "wifi clear" || v == "ota-check" ||
    v.startsWith("wifi") || v.startsWith("ssid=") || v.startsWith("pass=")) {

  if (v == "wifi?") {
    bool had = wifiCredsLoaded || loadWiFiCreds();
    String masked = had ? (wifiSsid.substring(0, min(3,(int)wifiSsid.length())) + "***") : "(none)";
    Serial.println("[BLE] Reporting Wi‑Fi status to central");
    sendToBLE("Wi‑Fi saved: " + String(had ? "yes" : "no") + "\nSSID: " + masked);
    return;
  }

  if (v == "wifi clear") {
    clearWiFiCreds();
    provSsidTmp = ""; provPassTmp = ""; provBuf = "";
    Serial.println("[BLE] Wi‑Fi credentials cleared by user");
    sendToBLE("Wi‑Fi credentials cleared.");
    return;
  }

  if (v == "ota-check") {
    Serial.println("[BLE] User requested OTA check");
    otaChecked = false; otaPrompted = false; otaDeclined = false;
    triggerOTACheck();
    return;
  }

  // Normalize and accumulate fragments into provBuf
  String frag = v;
  frag.replace('\r', ' ');
  frag.replace('\n', ' ');
  // also normalize common weird spaces from some keyboards/apps
  frag.replace(String((char)0xC2) + String((char)0xA0), " "); // non‑breaking space
  
  // Limit buffer size to prevent memory issues
  if (provBuf.length() > 200) {
    provBuf = " " + frag + " ";
    Serial.println("[BLE] Buffer overflow, resetting provBuf");
  } else {
    provBuf += " " + frag + " ";
  }

  // Helper to extract value for a key across fragments
  auto extractKV = [](const String& src, const char* key) -> String {
    String pat = String(key) + "=";
    int k = src.indexOf(pat);
    if (k < 0) return "";
    int start = k + pat.length();
    // support quoted values with spaces: ssid="My Wifi"
    if (start < src.length() && src[start] == '\"') {
      int endq = src.indexOf('\"', start + 1);
      if (endq > start) return src.substring(start + 1, endq);
      return ""; // unfinished quote, wait for more
    }
    // unquoted: read until next space OR next key= pattern
    int sp = src.indexOf(' ', start);
    int nextKey = src.indexOf('=', start);
    
    // Find the earliest delimiter (space or next key)
    int end = src.length();
    if (sp >= 0 && (nextKey < 0 || sp < nextKey)) {
      end = sp;
    } else if (nextKey >= 0) {
      end = nextKey;
    }
    
    return src.substring(start, end);
  };

  String ss = extractKV(provBuf, "ssid");
  String pw = extractKV(provBuf, "pass");

  Serial.printf("[BLE] Debug: provBuf='%s'\n", provBuf.c_str());
  Serial.printf("[BLE] Debug: extracted ssid='%s' pass='%s'\n", ss.c_str(), pw.c_str());

  if (ss.length()) { provSsidTmp = ss; Serial.println("[BLE] Parsed SSID: " + ss); }
  if (pw.length()) { provPassTmp = pw; Serial.println("[BLE] Parsed PASS: " + String(pw.length()) + " chars"); }

  if (provSsidTmp.length() && provPassTmp.length()) {
    Serial.printf("[WIFI] About to save credentials - SSID: '%s', pass length: %d\n", provSsidTmp.c_str(), provPassTmp.length());
    saveWiFiCreds(provSsidTmp, provPassTmp);
    Serial.println("[WIFI] Credentials saved (SSID only shown): " + provSsidTmp);
    Serial.printf("[WIFI] Verification - wifiCredsLoaded: %s, ssid: '%s', pass length: %d\n", 
                  wifiCredsLoaded ? "true" : "false", wifiSsid.c_str(), wifiPass.length());
    sendToBLE("Wi‑Fi credentials saved. Send 'ota-check' to verify and check for updates.");
    // reset buffers for next time
    provSsidTmp = ""; provPassTmp = ""; provBuf = "";
  } else {
    String missing;
    if (!provSsidTmp.length()) missing += "ssid";
    if (!provPassTmp.length()) missing += (missing.length() ? " & pass" : "pass");
    sendToBLE("Waiting for " + missing + ". You can send together:\n  wifi ssid=<SSID> pass=<PASS>\nOr one by one:\n  ssid=<SSID>\n  pass=<PASS>\n(Quotes allowed for spaces)");
  }
  return;
}

    // ---- OTA prompt handling ----
    if (otaPrompted) {
      if (v == "ota-yes") {
        otaPrompted = false;
        blePermanentlyOff = true; // Prevent BLE restart after OTA
        Serial.println("[BLE] OTA accepted by user");
        sendToBLE("Starting OTA...");
        if (!wifiCredsLoaded) loadWiFiCreds();
        WiFi.mode(WIFI_STA);
        WiFi.begin(wifiSsid.c_str(), wifiPass.c_str());
        unsigned long t0 = millis();
        while (WiFi.status() != WL_CONNECTED && millis() - t0 < 8000) delay(100);
        if (WiFi.status() == WL_CONNECTED) {
          triggerOTAUpdate(); // reboots on success
          sendToBLE("OTA failed.");
          WiFi.disconnect(true);
          WiFi.mode(WIFI_OFF);
        } else {
          Serial.println("[BLE] Wi‑Fi connect failed; OTA aborted");
          sendToBLE("Wi‑Fi connect failed, OTA aborted.");
        }
        return;
      } else if (v == "ota-no") {
        otaPrompted = false; otaDeclined = true;
        Serial.println("[BLE] OTA declined by user");
        sendToBLE("OTA skipped. Ready for commands.");
        return;
      } else {
        sendToBLE("Reply 'ota-yes' to install or 'ota-no' to skip.");
        return;
      }
    }

    // ---- Motor command path ----
    pendingCmd = v;
    cmdPending = true;
    otaChecked = true;  // allow motor cmds without explicit ota-check
    Serial.println("[BLE] Queued motor command: " + v);
  }
};

// ====== Setup BLE ======
void setupBLE() {
  BLEDevice::init("ColorMaster");  // Device name seen in scans
  digitalWrite(LED_BLE, HIGH); // BLE LED ON
  pServer = BLEDevice::createServer();
  pServer->setCallbacks(new ServerCallbacks());

  pService = pServer->createService(NUS_SERVICE_UUID);

  pTxChar = pService->createCharacteristic(
    NUS_TX_UUID,
    BLECharacteristic::PROPERTY_NOTIFY | BLECharacteristic::PROPERTY_READ
  );
  pTxCcc = new BLE2902();
  pTxCcc->setNotifications(true);
  pTxChar->addDescriptor(pTxCcc);

  pRxChar = pService->createCharacteristic(
    NUS_RX_UUID,
    BLECharacteristic::PROPERTY_WRITE | BLECharacteristic::PROPERTY_WRITE_NR
  );
  pRxChar->setCallbacks(new CmdCallbacks());

  pService->start();

  BLEAdvertising* adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(NUS_SERVICE_UUID);
  adv->setScanResponse(true);
  adv->setMinPreferred(0x06);
  adv->setMinPreferred(0x12);
  BLEDevice::startAdvertising();

  Serial.println("[BLE] Advertising started as 'Color Dispenser'");
}

// ====== BLE Task ======
void bleTask(void* parameter) {
  setupBLE();
  while (1) {
    // BLE is event/callback driven, just keep task alive
    vTaskDelay(pdMS_TO_TICKS(100));
  }
}

// ====== WiFi/OTA Task ======
volatile bool otaCheckRequested = false;
void wifiTask(void* parameter) {
  while (1) {
    // Wait for notification to run OTA check
    ulTaskNotifyTake(pdTRUE, portMAX_DELAY);
    xSemaphoreTake(stateMutex, portMAX_DELAY);
    bool credsLoaded = wifiCredsLoaded;
    xSemaphoreGive(stateMutex);
    if (credsLoaded) {
      checkForOTAUpdate();
    } else {
      sendToBLE("No Wi-Fi credentials. Provision first.");
    }
  }
}

// ====== OTA Task ======
void otaTask(void* parameter) {
  while (1) {
    // Wait for notification to run OTA update
    ulTaskNotifyTake(pdTRUE, portMAX_DELAY);
    // Turn BLE LED OFF before BLE deinit
    digitalWrite(LED_BLE, LOW);
    // Fully deinit BLE before OTA
    if (pServer) {
      pServer->getAdvertising()->stop();
      Serial.println("[OTA] BLE advertising stopped before OTA");
    }
    delay(50);
    BLEDevice::deinit(true);
    Serial.println("[OTA] BLE deinitialized before OTA");
    // Invalidate BLE pointers to prevent further notifications
    pTxChar = nullptr;
    pServer = nullptr;
    pService = nullptr;
    pTxCcc = nullptr;
    delay(200);
    // Run OTA update
    bool result = performOTAWithProgress();
    if (!result) {
      sendToBLE("OTA failed.");
    }
    // After OTA, device will reboot, so no need to reinit BLE here
  }
}

// ====== OTA Trigger from BLE ======
void triggerOTAUpdate() {
  if (otaTaskHandle) {
    xTaskNotifyGive(otaTaskHandle);
  }
}

// ====== OTACheck Trigger ======
void triggerOTACheck() {
  if (wifiTaskHandle) {
    xTaskNotifyGive(wifiTaskHandle);
  }
}

// ====== OTA with Progress Reporting ======
bool performOTAWithProgress() {
  otaLedBlink = true; // Start blinking
  digitalWrite(LED_OTAPROG, LOW); // Ensure off before start
  Serial.printf("[OTA] WiFi status before OTA: %d\n", WiFi.status());
  Serial.printf("[OTA] Attempting OTA from URL: %s\n", FIRMWARE_URL);

  // Ensure WiFi is connected before OTA
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("[OTA] WiFi not connected, attempting to connect...");
    WiFi.mode(WIFI_STA);
    WiFi.begin(wifiSsid.c_str(), wifiPass.c_str());
    unsigned long t0 = millis();
    while (WiFi.status() != WL_CONNECTED && millis() - t0 < 10000) {
      delay(100);
    }
    if (WiFi.status() != WL_CONNECTED) {
      otaLedBlink = false;
      digitalWrite(LED_OTAPROG, HIGH); // Solid ON for error
      Serial.println("[OTA] WiFi connect failed before OTA!");
      sendToBLE("WiFi connect failed, OTA aborted.");
      return false;
    }
    Serial.println("[OTA] WiFi connected for OTA.");
  }

  WiFiClientSecure client;
  client.setInsecure();
  HTTPClient http;
  if (!http.begin(client, FIRMWARE_URL)) {
    otaLedBlink = false;
    digitalWrite(LED_OTAPROG, HIGH); // Solid ON for error
    Serial.println("[OTA] http.begin(firmware) failed");
    return false;
  }
  int code = http.GET();
  Serial.printf("[OTA] HTTP GET returned code: %d\n", code);
  if (code != HTTP_CODE_OK) {
    otaLedBlink = false;
    digitalWrite(LED_OTAPROG, HIGH); // Solid ON for error
    Serial.printf("[OTA] GET firmware.bin failed: %d\n", code);
    http.end();
    return false;
  }
  int total = http.getSize();
  WiFiClient* stream = http.getStreamPtr();
  if (!Update.begin(total > 0 ? total : UPDATE_SIZE_UNKNOWN)) {
    otaLedBlink = false;
    digitalWrite(LED_OTAPROG, HIGH); // Solid ON for error
    Serial.println("[OTA] Update.begin failed");
    http.end();
    return false;
  }
  sendToBLE("Starting OTA...");
  const size_t bufSize = 4096;
  uint8_t buf[bufSize];
  size_t written = 0;
  uint32_t lastNotify = millis();
  uint32_t lastPercent = 0;
  while (http.connected() && (written < (size_t)total || total <= 0)) {
    size_t avail = stream->available();
    if (avail) {
      size_t len = stream->readBytes(buf, min(avail, bufSize));
      if (len > 0) {
        if (Update.write(buf, len) != len) {
          otaLedBlink = false;
          digitalWrite(LED_OTAPROG, HIGH); // Solid ON for error
          Serial.println("[OTA] Update.write mismatch");
          Update.abort();
          http.end();
          return false;
        }
        written += len;
        uint32_t now = millis();
        if (now - lastNotify > 1000) { // Send update every 1s
          if (total > 0) {
            int pct = (int)((written * 100ULL) / total);
            if (pct != lastPercent) {
              sendToBLE("OTA " + String(pct) + "%");
              lastPercent = pct;
            }
          } else {
            sendToBLE("OTA " + String(written) + " bytes");
          }
          lastNotify = now;
        }
      }
    } else {
      delay(10);
    }
    if (total > 0 && written >= (size_t)total) break;
  }
  if (!Update.end(true)) {
    otaLedBlink = false;
    digitalWrite(LED_OTAPROG, HIGH); // Solid ON for error
    Serial.printf("[OTA] Update.end error: %s\n", Update.errorString());
    http.end();
    return false;
  }
  otaLedBlink = false;
  digitalWrite(LED_OTAPROG, LOW); // OFF for success
  http.end();
  sendToBLE("OTA complete. Rebooting...");
  digitalWrite(LED_OTAOK, HIGH); // Success LED ON
  vTaskDelay(pdMS_TO_TICKS(2000)); // 2 seconds
  digitalWrite(LED_OTAOK, LOW);
  delay(100);
  ESP.restart();
  return true; // not reached
}

// ====== BLE Command Handler (update) ======
// In CmdCallbacks::handleBleLine, replace:
//   if (v == "ota-check") { ... checkForOTAUpdate(); ... }
// with:
//   if (v == "ota-check") { ... triggerOTA(); ... }
//
// Example:
//   if (v == "ota-check") {
//     Serial.println("[BLE] User requested OTA check");
//     otaChecked = false; otaPrompted = false; otaDeclined = false;
//     triggerOTA();
//     return;
//   }

// ====== OTA Progress LED Task ======
// (declarations moved to top)

void otaLedTask(void* parameter) {
  while (1) {
    if (otaLedBlink) {
      digitalWrite(LED_OTAPROG, HIGH);
      vTaskDelay(pdMS_TO_TICKS(500));
      if (!otaLedBlink) continue;
      digitalWrite(LED_OTAPROG, LOW);
      vTaskDelay(pdMS_TO_TICKS(500));
    } else {
      vTaskDelay(pdMS_TO_TICKS(50));
    }
    if (otaLedStop) {
      digitalWrite(LED_OTAPROG, LOW);
      otaLedStop = false;
    }
  }
}

// ====== Arduino entry points ======

static inline int clampMS(int v, int vmin, int vmax) {
  if (v <= 0) return 0;
  if (v < vmin) v = vmin;
  if (v > vmax) v = vmax;
  return v;
}

static void rgbToCMYK_ms(int R, int G, int B, int grams,
                         int& c_ms, int& m_ms, int& y_ms, int& k_ms) {
  float r = constrain(R, 0, 255) / 255.0f;
  float g = constrain(G, 0, 255) / 255.0f;
  float b = constrain(B, 0, 255) / 255.0f;

  float K = 1.0f - max(r, max(g, b));       // 0..1
  float C = (1.0f - r - K) / (1.0f - K + 1e-6f);
  float M = (1.0f - g - K) / (1.0f - K + 1e-6f);
  float Y = (1.0f - b - K) / (1.0f - K + 1e-6f);
  if (K < 1e-6f) { C = 0; M = 0; Y = 0; }

  C = constrain(C, 0.0f, 1.0f);
  M = constrain(M, 0.0f, 1.0f);
  Y = constrain(Y, 0.0f, 1.0f);
  // K already 0..1

  auto scale = [&](float u, int vmin, int vmax)->int {
    if (u <= 0.0f) return 0;
    int ms = (int)round(u * vmax);
    return clampMS(ms, vmin, vmax);
  };

  int c = scale(C, C_MIN_MS, C_MAX_MS);
  int m = scale(M, M_MIN_MS, M_MAX_MS);
  int y = scale(Y, Y_MIN_MS, Y_MAX_MS);
  int k = scale(K, K_MIN_MS, K_MAX_MS);

  if (grams > 0 && grams != BASELINE_GRAMS) {
    float gscale = (float)grams / (float)BASELINE_GRAMS;
    c = min((int)round(c * gscale), C_MAX_MS);
    m = min((int)round(m * gscale), M_MAX_MS);
    y = min((int)round(y * gscale), Y_MAX_MS);
    k = min((int)round(k * gscale), K_MAX_MS);
  }
  c_ms = c; m_ms = m; y_ms = y; k_ms = k;
}

void setup() {
  Serial.begin(115200);
  delay(200);

  // Motor pins
  pinMode(C_IN1, OUTPUT); pinMode(C_IN2, OUTPUT);
  pinMode(M_IN1, OUTPUT); pinMode(M_IN2, OUTPUT);
  pinMode(Y_IN1, OUTPUT); pinMode(Y_IN2, OUTPUT);
  pinMode(K_IN1, OUTPUT); pinMode(K_IN2, OUTPUT);
  pinMode(W_IN1, OUTPUT); pinMode(W_IN2, OUTPUT);
  motorStop(C_IN1, C_IN2);
  motorStop(M_IN1, M_IN2);
  motorStop(Y_IN1, Y_IN2);
  motorStop(K_IN1, K_IN2);
  motorStop(W_IN1, W_IN2);

  // LED pins
  pinMode(LED_BLE, OUTPUT);
  pinMode(LED_OTAOK, OUTPUT);
  pinMode(LED_OTAPROG, OUTPUT);
  digitalWrite(LED_BLE, LOW);
  digitalWrite(LED_OTAOK, LOW);
  digitalWrite(LED_OTAPROG, LOW);

  // Mutex for shared state
  stateMutex = xSemaphoreCreateMutex();

  // Load Wi‑Fi creds if present
  loadWiFiCreds();

  // Start BLE task
  xTaskCreatePinnedToCore(
    bleTask, "BLE Task", BLE_TASK_STACK_SIZE, NULL, 2, &bleTaskHandle, 0);

  // Start WiFi/OTA task
  xTaskCreatePinnedToCore(
    wifiTask, "WiFi Task", WIFI_TASK_STACK_SIZE, NULL, 2, &wifiTaskHandle, 1);

  // Start OTA task
  xTaskCreatePinnedToCore(
    otaTask, "OTA Task", OTA_TASK_STACK_SIZE, NULL, 2, &otaTaskHandle, 1);

  // Start OTA LED task
  xTaskCreatePinnedToCore(
    otaLedTask, "OTA LED Task", 2048, NULL, 1, &otaLedTaskHandle, 1);

  sendToBLE("Ready.\nCommands:\n  wifi ssid=<SSID> pass=<PASS>\n  wifi? | wifi clear\n  ota-check\n  c<msec> m<msec> y<msec> k<msec> w<msec>");
}

void loop() {
  // Run deferred motor command if OTA is cleared
  xSemaphoreTake(stateMutex, portMAX_DELAY);
  bool runCmd = cmdPending && otaChecked && (!update_available || otaDeclined);
  xSemaphoreGive(stateMutex);
  if (runCmd) {
    noInterrupts();
    cmdPending = false;
    String line = pendingCmd;
    interrupts();
    Serial.println("[MOTOR] Executing: " + line);
    handleCommand(line);
    sendToBLE("OK");
  }
  delay(50);
}
