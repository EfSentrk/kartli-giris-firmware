// =============================================================================
// Kartli Giris - NodeMCU firmware (sirsiz, OTA'li)
//
// Bu firmware PUBLIC bir depoda derlenip yayinlanir; bu yuzden ICINDE HICBIR SIR
// YOKTUR. WiFi bilgisi, sunucu adresi ve bootstrap sirri derleme aninda degil,
// CIHAZDA seri porttan bir kez girilir ve EEPROM'da saklanir. Cihaz sirri de
// kayittan sonra EEPROM'a yazilir. Boylece yayinlanan .bin dosyasi guvenlidir.
//
// Ozellikler:
//   - Seri porttan tek satirla kurulum (SETUP ...), EEPROM'da kalici config
//   - WiFi + NTP
//   - Kayit (bootstrap sir) -> cihaz sirri EEPROM'a
//   - RC522 kart okuma -> HMAC-SHA256 imzali /api/devices/scan
//   - 16x2 I2C LCD'de sonuc
//   - Heartbeat + panel komut kuyrugu (CHECK_UPDATE); araliklar sunucudan
//   - GitHub'dan OTA: surum kontrol -> indir -> kendini flashla
//
// -----------------------------------------------------------------------------
// KABLOLAMA (mevcut mimari)
//   RC522: SDA/SS->D8(GPIO15) SCK->D5 MOSI->D7 MISO->D6 RST->D3(GPIO0) 3.3V GND
//   LCD  : SDA->D2(GPIO4) SCL->D1(GPIO5) VCC->5V GND  (I2C 0x27, 16x2)
//   NOT: D8->GND 10k pull-down, D3->3V3 10k pull-up (acilis stabilitesi).
//
// -----------------------------------------------------------------------------
// ILK KURULUM (bir kez, seri monitorde 115200):
//   SETUP <ssid>|<sifre>|<sunucu>|<port>|<bootstrap_secret>
//
//   Port 443 verilirse istekler HTTPS'e gecer; boylece cihaz ayni evde olmak
//   zorunda kalmadan internetteki panele kaydolur. Diger portlarda duz HTTP.
//
//   internetteki panel:  SETUP EvWifi|sifre123|panel.ornek.com|443|<SIR>
//   yerel gelistirme  :  SETUP EvWifi|sifre123|192.168.1.157|3000|<SIR>
//
//   Yedek aglar (4 slota kadar) — internet giderse cihaz kendiliginden gecer:
//     WIFI ADD <ssid>|<sifre>     WIFI DEL <1..4>     WIFI LIST
//
//   Diger komutlar:  INFO (ayarlari goster)  RESET (config sil)  OTA (guncelle)
// =============================================================================

#include <ESP8266WiFi.h>
#include <ESP8266WiFiMulti.h>
#include <ESP8266HTTPClient.h>
#include <ESP8266httpUpdate.h>
#include <WiFiClientSecure.h>
#include <EEPROM.h>
#include <memory>
#include <SPI.h>
#include <Wire.h>
#include <MFRC522.h>
#include <LiquidCrystal_I2C.h>
#include <bearssl/bearssl_hmac.h>
#include <time.h>

#define FIRMWARE_VERSION "0.7.0"

// OTA kaynagi (sir degil, public depo).
#define OTA_OWNER "EfSentrk"
#define OTA_REPO  "kartli-giris-firmware"

// --- RC522 ---
static const uint8_t RC522_SS = 15, RC522_RST = 0;   // D8, D3
MFRC522 rfid(RC522_SS, RC522_RST);

// --- LCD ---
LiquidCrystal_I2C lcd(0x27, 16, 2);
static const uint8_t LCD_SDA = 4, LCD_SCL = 5;       // D2, D1

// --- Zamanlamalar ---
static const unsigned long WIFI_TIMEOUT_MS    = 30000UL;
static const unsigned long REGISTER_RETRY_MS  = 15000UL;
static const unsigned long SAME_CARD_BLOCK_MS = 3000UL;
static const unsigned long RESULT_HOLD_MS     = 4000UL;
// Asagidaki iki aralik SABIT DEGIL: sunucu her heartbeat cevabinda gecerli
// degerleri gonderiyor ve cihaz bunlari yaziyor. Boylece "daha seyrek ugra"
// demek icin cihazi USB'ye takip yeniden yuklemek gerekmiyor. Buradakiler
// yalnizca sunucuya ilk kez ulasana kadar gecerli acilis degerleri.
static unsigned long otaCheckMs  = 10UL * 60UL * 1000UL;   // 10 dakika
static unsigned long heartbeatMs = 60UL * 1000UL;          // 1 dakika

// -----------------------------------------------------------------------------
// EEPROM config
// -----------------------------------------------------------------------------
// Surum 3: tek WiFi yerine 4 slotluk ag listesi. Eski config'ler gecersiz
// sayilir (magic tutmaz) ve cihaz yeniden kurulum ister; alan duzeni degistigi
// icin eski baytlari okumak cop deger uretirdi.
static const uint8_t CFG_MAGIC[4] = { 'K', 'G', 'C', 3 };

// Dort ag pratikte yetiyor: kurulum yeri, yedek hat, telefon hotspot'u ve
// servis icin bir tane. Daha fazlasi EEPROM'dan cok tarama suresini uzatir.
static const uint8_t WIFI_SLOTS = 4;

struct WifiNet {
  char ssid[33];
  char pass[65];
};

struct Config {
  uint8_t  magic[4];
  WifiNet  nets[WIFI_SLOTS];
  char     serverHost[41];
  uint16_t serverPort;
  char     bootstrap[65];
  char     secret[97];   // cihaz sirri (kayittan sonra dolar)
};

static Config cfg;
static const int EEPROM_SIZE = sizeof(Config) + 8;
static ESP8266WiFiMulti wifiMulti;

bool cfgValid() {
  for (int i = 0; i < 4; i++) if (cfg.magic[i] != CFG_MAGIC[i]) return false;
  return true;
}

uint8_t wifiCount() {
  uint8_t n = 0;
  for (uint8_t i = 0; i < WIFI_SLOTS; i++) if (strlen(cfg.nets[i].ssid)) n++;
  return n;
}

void cfgLoad() { EEPROM.get(0, cfg); }
void cfgSave() {
  memcpy(cfg.magic, CFG_MAGIC, 4);
  EEPROM.put(0, cfg);
  EEPROM.commit();
}
void cfgClear() {
  memset(&cfg, 0, sizeof(cfg));
  EEPROM.put(0, cfg);
  EEPROM.commit();
}

// -----------------------------------------------------------------------------
// Durum
// -----------------------------------------------------------------------------
static String lastUid = "";
static unsigned long lastUidAt = 0;
static unsigned long resultShownAt = 0;
static unsigned long lastOtaCheck = 0;
static unsigned long lastHeartbeat = 0;
static bool idleShown = false;

// -----------------------------------------------------------------------------
// Yardimcilar
// -----------------------------------------------------------------------------
String chipIdHex() { char b[9]; snprintf(b, sizeof(b), "%06x", ESP.getChipId()); return String(b); }
String deviceId()  { return "esp8266-" + chipIdHex(); }

// --- Sunucu adresi: yerelde duz HTTP, internette HTTPS ---
//
// Sema icin ayri bir config alani tutmuyoruz: port 443 ise TLS kullaniyoruz.
// Boylece ayni SETUP satiri hem "192.168.1.157|3000" hem "panel.ornek.com|443"
// icin calisiyor ve EEPROM duzeni degismiyor.
bool serverIsTls() { return cfg.serverPort == 443; }

String serverUrl(const char *path) {
  String u = serverIsTls() ? "https://" : "http://";
  u += cfg.serverHost;
  // Varsayilan portu URL'e yazmiyoruz; bazi vekiller Host basliginda :443
  // gorunce isteği reddediyor.
  bool defaultPort = (serverIsTls() && cfg.serverPort == 443) ||
                     (!serverIsTls() && cfg.serverPort == 80);
  if (!defaultPort) { u += ":"; u += cfg.serverPort; }
  u += path;
  return u;
}

// Cagiran taraf donen istemciyi istegin sonuna kadar canli tutmali.
//
// TLS'te buffer boyutunu KUCULTMUYORUZ. OTA'da GitHub icin 1024 byte yetiyor
// cunku o baglanti MFLN destekliyor; genel bir sunucu desteklemeyebilir ve
// kucuk buffer'da el sikisma sessizce basarisiz olur. Varsayilan 16 KB rx
// daha cok heap yiyor ama tek bir istek icin ESP8266'da sorun cikarmiyor.
std::unique_ptr<WiFiClient> makeClient() {
  if (!serverIsTls()) return std::unique_ptr<WiFiClient>(new WiFiClient());
  auto *tls = new WiFiClientSecure();
  // Sertifika dogrulamasi yok: cihazda kok sertifika deposu tutmak ve
  // suresi dolunca hepsini OTA ile guncellemek gerekirdi. Govde zaten
  // HMAC ile imzali, sunucu sahte istegi kabul etmez.
  tls->setInsecure();
  return std::unique_ptr<WiFiClient>(tls);
}

String toHex(const uint8_t *d, size_t n) {
  static const char *h = "0123456789abcdef";
  String o; o.reserve(n * 2);
  for (size_t i = 0; i < n; i++) { o += h[d[i] >> 4]; o += h[d[i] & 15]; }
  return o;
}

String jsonString(const String &body, const char *key) {
  String needle = String("\"") + key + "\":\"";
  int s = body.indexOf(needle);
  if (s < 0) return "";
  s += needle.length();
  int e = body.indexOf('"', s);
  return e < 0 ? "" : body.substring(s, e);
}

// jsonString tirnakli degerler icin; sayilar tirnaksiz geldiginden ayri.
long jsonNumber(const String &body, const char *key, long fallback) {
  String needle = String("\"") + key + "\":";
  int i = body.indexOf(needle);
  if (i < 0) return fallback;
  i += needle.length();
  while (i < (int)body.length() && body[i] == ' ') i++;
  int j = i;
  while (j < (int)body.length() && (isdigit(body[j]) || body[j] == '-')) j++;
  if (j == i) return fallback;
  return body.substring(i, j).toInt();
}

String makeNonce() {
  uint8_t b[12];
  for (int i = 0; i < 12; i += 4) { uint32_t r = RANDOM_REG32; memcpy(b + i, &r, 4); }
  return toHex(b, 12);
}

String hmacSha256Hex(const String &key, const String &msg) {
  br_hmac_key_context kc;
  br_hmac_key_init(&kc, &br_sha256_vtable, key.c_str(), key.length());
  br_hmac_context ctx;
  br_hmac_init(&ctx, &kc, 0);
  br_hmac_update(&ctx, msg.c_str(), msg.length());
  uint8_t out[32]; br_hmac_out(&ctx, out);
  return toHex(out, 32);
}

// -----------------------------------------------------------------------------
// LCD
// -----------------------------------------------------------------------------
void lcdShow(const String &l1, const String &l2) {
  lcd.clear();
  lcd.setCursor(0, 0); lcd.print(l1.substring(0, 16));
  lcd.setCursor(0, 1); lcd.print(l2.substring(0, 16));
}
void lcdIdle() { lcdShow("Kart okutun", ""); idleShown = true; }

// -----------------------------------------------------------------------------
// Seri kurulum komutlari
// -----------------------------------------------------------------------------
void printInfo() {
  Serial.println("--- config ---");
  for (uint8_t i = 0; i < WIFI_SLOTS; i++) {
    Serial.print("  wifi "); Serial.print(i + 1); Serial.print("  : ");
    if (strlen(cfg.nets[i].ssid)) {
      Serial.print(cfg.nets[i].ssid);
      Serial.println(strlen(cfg.nets[i].pass) ? "  (sifreli)" : "  (acik)");
    } else {
      Serial.println("(bos)");
    }
  }
  Serial.print("  bagli  : ");
  Serial.println(WiFi.status() == WL_CONNECTED ? WiFi.SSID() : String("(degil)"));
  Serial.print("  host   : "); Serial.print(cfg.serverHost); Serial.print(":"); Serial.println(cfg.serverPort);
  Serial.print("  boot   : "); Serial.println(strlen(cfg.bootstrap) ? "(dolu)" : "(bos)");
  Serial.print("  sir    : "); Serial.println(strlen(cfg.secret) ? "(EEPROM'da var)" : "(yok - kayit gerekli)");
  Serial.print("  cihaz  : "); Serial.println(deviceId());
  Serial.print("  surum  : "); Serial.println(FIRMWARE_VERSION);
}

// "SETUP ssid|pass|host|port|bootstrap" satirini ayristirir.
bool applySetup(const String &line) {
  String rest = line.substring(6);  // "SETUP " sonrasi
  int p1 = rest.indexOf('|');
  int p2 = rest.indexOf('|', p1 + 1);
  int p3 = rest.indexOf('|', p2 + 1);
  int p4 = rest.indexOf('|', p3 + 1);
  if (p1 < 0 || p2 < 0 || p3 < 0 || p4 < 0) {
    Serial.println("[setup] HATA: bicim -> SETUP ssid|sifre|host|port|bootstrap");
    return false;
  }
  String ssid = rest.substring(0, p1);
  String pass = rest.substring(p1 + 1, p2);
  String host = rest.substring(p2 + 1, p3);
  String port = rest.substring(p3 + 1, p4);
  String boot = rest.substring(p4 + 1);

  // SETUP tam sifirlama: eski aglar ve cihaz sirri da silinir. Sadece ag
  // eklemek icin WIFI ADD var.
  memset(&cfg, 0, sizeof(cfg));
  ssid.toCharArray(cfg.nets[0].ssid, sizeof(cfg.nets[0].ssid));
  pass.toCharArray(cfg.nets[0].pass, sizeof(cfg.nets[0].pass));
  host.toCharArray(cfg.serverHost, sizeof(cfg.serverHost));
  cfg.serverPort = (uint16_t)port.toInt();
  boot.toCharArray(cfg.bootstrap, sizeof(cfg.bootstrap));
  cfgSave();
  Serial.println("[setup] Kaydedildi. Yeniden baslatiliyor...");
  delay(500);
  ESP.restart();
  return true;
}

// "WIFI ADD ssid|sifre" — bos slota yazar, ayni SSID varsa sifresini gunceller.
void wifiAdd(const String &arg) {
  int p = arg.indexOf('|');
  if (p < 0) { Serial.println("[wifi] HATA: bicim -> WIFI ADD ssid|sifre"); return; }
  String ssid = arg.substring(0, p);
  String pass = arg.substring(p + 1);
  if (ssid.length() == 0) { Serial.println("[wifi] HATA: ssid bos"); return; }

  int slot = -1;
  // Once ayni SSID'yi ariyoruz: sifre degistiyse ikinci bir kayit acmak
  // yerine mevcut olani guncellemek dogru davranis.
  for (uint8_t i = 0; i < WIFI_SLOTS; i++) {
    if (strcmp(cfg.nets[i].ssid, ssid.c_str()) == 0) { slot = i; break; }
  }
  if (slot < 0) {
    for (uint8_t i = 0; i < WIFI_SLOTS; i++) {
      if (strlen(cfg.nets[i].ssid) == 0) { slot = i; break; }
    }
  }
  if (slot < 0) { Serial.println("[wifi] HATA: 4 slot da dolu. Once WIFI DEL <no>"); return; }

  memset(&cfg.nets[slot], 0, sizeof(WifiNet));
  ssid.toCharArray(cfg.nets[slot].ssid, sizeof(cfg.nets[slot].ssid));
  pass.toCharArray(cfg.nets[slot].pass, sizeof(cfg.nets[slot].pass));
  cfgSave();
  Serial.print("[wifi] slot "); Serial.print(slot + 1); Serial.print(" = "); Serial.println(ssid);

  // Su an bagli degilsek yeni ag hemen denensin; kullanici yeniden
  // baslatmak zorunda kalmasin.
  if (WiFi.status() != WL_CONNECTED) connectWiFi();
}

void wifiDel(const String &arg) {
  int n = arg.toInt();
  if (n < 1 || n > WIFI_SLOTS) { Serial.println("[wifi] HATA: WIFI DEL 1..4"); return; }
  memset(&cfg.nets[n - 1], 0, sizeof(WifiNet));
  cfgSave();
  Serial.print("[wifi] slot "); Serial.print(n); Serial.println(" silindi.");
}

void wifiList() {
  for (uint8_t i = 0; i < WIFI_SLOTS; i++) {
    Serial.print("  "); Serial.print(i + 1); Serial.print(") ");
    Serial.println(strlen(cfg.nets[i].ssid) ? cfg.nets[i].ssid : "(bos)");
  }
  Serial.print("  bagli: ");
  Serial.println(WiFi.status() == WL_CONNECTED ? WiFi.SSID() : String("(degil)"));
}

// Seri porttan gelen komutlari isler (her loop'ta cagrilir).
void handleSerial() {
  if (!Serial.available()) return;
  String line = Serial.readStringUntil('\n');
  line.trim();
  if (line.length() == 0) return;

  if (line.startsWith("SETUP "))         { applySetup(line); }
  else if (line.startsWith("WIFI ADD "))  { wifiAdd(line.substring(9)); }
  else if (line.startsWith("WIFI DEL "))  { wifiDel(line.substring(9)); }
  else if (line == "WIFI LIST")           { wifiList(); }
  else if (line == "INFO")                { printInfo(); }
  else if (line == "RESET")               { cfgClear(); Serial.println("[reset] Silindi. Yeniden baslat."); delay(300); ESP.restart(); }
  else if (line == "OTA")                 { checkOta(true); }
  else {
    Serial.println("[?] Komutlar:");
    Serial.println("    SETUP ssid|sifre|host|port|bootstrap   (tam kurulum, her seyi sifirlar)");
    Serial.println("    WIFI ADD ssid|sifre | WIFI DEL 1..4 | WIFI LIST");
    Serial.println("    INFO | RESET | OTA");
  }
}

// -----------------------------------------------------------------------------
// WiFi + NTP
// -----------------------------------------------------------------------------
// Tanimli aglardan o an GORUNEN ve sinyali en guclu olani secer. Bir ag
// kapanirsa sonraki cagride liste yeniden taranir; boylece internet giderse
// cihaz yedek hatta kendiliginden gecer ve OTA yolu acik kalir.
void connectWiFi() {
  if (WiFi.status() == WL_CONNECTED) return;

  if (wifiCount() == 0) {
    Serial.println("[wifi] Tanimli ag yok. WIFI ADD ssid|sifre");
    lcdShow("WiFi tanimsiz", "WIFI ADD ...");
    return;
  }

  WiFi.mode(WIFI_STA);
  wifiMulti.cleanAPlist();
  for (uint8_t i = 0; i < WIFI_SLOTS; i++) {
    if (strlen(cfg.nets[i].ssid)) wifiMulti.addAP(cfg.nets[i].ssid, cfg.nets[i].pass);
  }

  Serial.print("[wifi] "); Serial.print(wifiCount()); Serial.println(" ag deneniyor...");
  lcdShow("WiFi araniyor", String(wifiCount()) + " ag");

  if (wifiMulti.run(WIFI_TIMEOUT_MS) != WL_CONNECTED) {
    Serial.println("[wifi] hicbirine baglanilamadi");
    lcdShow("WiFi HATA", "WIFI LIST");
    return;
  }

  Serial.print("[wifi] "); Serial.print(WiFi.SSID());
  Serial.print("  IP: "); Serial.println(WiFi.localIP());
}

void syncTime() {
  configTime(0, 0, "pool.ntp.org", "time.google.com");
  unsigned long t = millis();
  while (time(nullptr) < 1600000000UL) {
    if (millis() - t > 15000UL) { Serial.println("[ntp] saat ayarlanamadi"); return; }
    delay(300);
  }
  Serial.print("[ntp] hazir: "); Serial.println((uint32_t)time(nullptr));
}

// -----------------------------------------------------------------------------
// Kayit
// -----------------------------------------------------------------------------
bool registerDevice() {
  auto client = makeClient(); HTTPClient http;
  String url = serverUrl("/api/devices/register");
  if (!http.begin(*client, url)) return false;
  http.addHeader("Content-Type", "application/json");
  String payload = String("{\"device_id\":\"") + deviceId() +
    "\",\"chip_id\":\"" + chipIdHex() +
    "\",\"bootstrap_secret\":\"" + cfg.bootstrap +
    "\",\"firmware_version\":\"" + FIRMWARE_VERSION +
    // Config'teki ilk slot degil, GERCEKTEN bagli oldugumuz ag bildirilir:
    // yedege dusuldugunde panelde hangi hattan geldigi gorunsun.
    "\",\"wifi_ssid\":\"" + WiFi.SSID() +
    "\",\"wifi_rssi\":" + String(WiFi.RSSI()) + "}";
  int code = http.POST(payload);
  String body = http.getString();
  http.end();

  Serial.print("[kayit] HTTP "); Serial.println(code);
  if (code == 401) { lcdShow("Kayit HATA", "bootstrap sir"); return false; }
  if (code != 200 && code != 201) return false;

  String secret = jsonString(body, "device_secret");
  if (secret.length() == 0) {
    Serial.println("[kayit] Sunucu sir vermedi (zaten onayli?). Panelden sil.");
    lcdShow("Kayit gerekli", "Panelden sil");
    return false;
  }
  secret.toCharArray(cfg.secret, sizeof(cfg.secret));
  cfgSave();
  Serial.println("[kayit] OK, sir EEPROM'a yazildi. Onay bekleniyor.");
  lcdShow("Kayit tamam", "Onay bekleniyor");
  return true;
}

// -----------------------------------------------------------------------------
// Imzali POST
// -----------------------------------------------------------------------------
//
// Kanonik metin sunucudaki buildCanonical ile BIREBIR ayni olmali:
//   device_id \n timestamp \n nonce \n body
// Govde yeniden serilestirilmeden, gonderilen ham metin imzalanir.
int signedPost(const char *path, const String &body, String &resp) {
  auto client = makeClient(); HTTPClient http;
  String ts = String((uint32_t)time(nullptr));
  String nonce = makeNonce();
  String sig = hmacSha256Hex(String(cfg.secret), deviceId() + "\n" + ts + "\n" + nonce + "\n" + body);

  if (!http.begin(*client, serverUrl(path))) return -1;
  http.addHeader("Content-Type", "application/json");
  http.addHeader("X-Device-Id", deviceId());
  http.addHeader("X-Timestamp", ts);
  http.addHeader("X-Nonce", nonce);
  http.addHeader("X-Signature", sig);
  int code = http.POST(body);
  resp = http.getString();
  http.end();
  return code;
}

// -----------------------------------------------------------------------------
// Heartbeat + komut kuyrugu
// -----------------------------------------------------------------------------
//
// Cihaz kart okutulmasa da duzenli olarak sunucuya ugrar. Iki faydasi var:
// panel "en son ne zaman gorundu" bilgisini alir, ve panelden birakilan
// komutlari 30 saniye icinde tesliim aliriz. OTA'nin 10 dakikalik periyodunu
// beklemeden "simdi guncelle" diyebilmemizin yolu bu.
void pollCommands() {
  lastHeartbeat = millis();

  String body = String("{\"firmware_version\":\"") + FIRMWARE_VERSION +
                "\",\"wifi_ssid\":\"" + WiFi.SSID() +
                "\",\"wifi_rssi\":" + String(WiFi.RSSI()) + "}";
  String resp;
  int code = signedPost("/api/devices/commands", body, resp);

  if (code != 200) {
    // Onay bekleyen cihaz 403 alir; bu bir hata degil, normal durum.
    if (code != 403) { Serial.print("[komut] HTTP "); Serial.println(code); }
    return;
  }

  // Sunucunun bildirdigi araliklari uygula. Sinirlar cihaz tarafinda da
  // kontrol ediliyor: bozuk ya da kotu niyetli bir deger cihazi saniyede bir
  // istek atar hale getirmemeli.
  long hb = jsonNumber(resp, "heartbeat_seconds", 0);
  if (hb >= 30 && hb <= 3600) heartbeatMs = (unsigned long)hb * 1000UL;
  long ota = jsonNumber(resp, "ota_check_seconds", 0);
  if (ota >= 300 && ota <= 86400) otaCheckMs = (unsigned long)ota * 1000UL;

  // Tek komut tipimiz var; tam bir JSON ayristiricisi yerine tipin adini
  // ariyoruz. Yeni komut tipleri eklenirse burasi gercek bir parser ister.
  if (resp.indexOf("CHECK_UPDATE") >= 0) {
    Serial.println("[komut] CHECK_UPDATE alindi, guncelleme kontrol ediliyor.");
    checkOta(true);
  }
}

// -----------------------------------------------------------------------------
// Kart okutma -> imzali scan
// -----------------------------------------------------------------------------
void sendScan(const String &uid) {
  String body = String("{\"uid\":\"") + uid + "\",\"firmware_version\":\"" + FIRMWARE_VERSION + "\"}";
  String resp;
  int code = signedPost("/api/devices/scan", body, resp);

  if (code == 200) {
    String action = jsonString(resp, "action");
    String message = jsonString(resp, "message");
    String staff = jsonString(resp, "staff_name");
    Serial.print("  SONUC: "); Serial.print(action);
    Serial.print(" | "); Serial.println(message);
    lcdShow(message, staff.length() ? staff : action);
  } else if (code == 403) { lcdShow("Onay bekliyor", "Panelden onayla"); Serial.println("[scan] 403 onay bekliyor"); }
  else if (code == 401)   { lcdShow("Imza hatasi", "Saat/sir?"); Serial.println("[scan] 401 imza"); }
  else { lcdShow("Sunucu hatasi", String("HTTP ") + code); Serial.print("[scan] HTTP "); Serial.println(code); }

  resultShownAt = millis(); idleShown = false;
}

String readCardUid() {
  if (!rfid.PICC_IsNewCardPresent() || !rfid.PICC_ReadCardSerial()) return "";
  String uid; uid.reserve(rfid.uid.size * 2);
  for (byte i = 0; i < rfid.uid.size; i++) {
    if (rfid.uid.uidByte[i] < 0x10) uid += "0";
    uid += String(rfid.uid.uidByte[i], HEX);
  }
  uid.toUpperCase();
  rfid.PICC_HaltA(); rfid.PCD_StopCrypto1();
  return uid;
}

// -----------------------------------------------------------------------------
// OTA: GitHub'dan surum kontrol -> indir -> flashla
// -----------------------------------------------------------------------------
void checkOta(bool forced) {
  if (WiFi.status() != WL_CONNECTED) return;
  lastOtaCheck = millis();

  // GitHub public depo; sertifika dogrulamasi yapmiyoruz (setInsecure). MITM
  // riski var ama binary GitHub'da; ilerde sertifika pinlemesi eklenebilir.
  WiFiClientSecure client;
  client.setInsecure();
  client.setBufferSizes(1024, 1024);

  String base = String("https://github.com/") + OTA_OWNER + "/" + OTA_REPO + "/releases/latest/download";

  HTTPClient http;
  http.begin(client, base + "/manifest.json");
  int code = http.GET();
  if (code != 200) {
    Serial.print("[ota] manifest alinamadi HTTP "); Serial.println(code);
    http.end();
    if (forced) lcdShow("OTA", "manifest yok");
    return;
  }
  String manifest = http.getString();
  http.end();

  String latest = jsonString(manifest, "version");
  Serial.print("[ota] yuklu="); Serial.print(FIRMWARE_VERSION);
  Serial.print("  son="); Serial.println(latest);

  if (latest.length() == 0 || latest == FIRMWARE_VERSION) {
    if (forced) lcdShow("OTA", "guncel");
    return;
  }

  Serial.println("[ota] Yeni surum var, indiriliyor...");
  lcdShow("Guncelleniyor", latest);

  ESPhttpUpdate.rebootOnUpdate(true);
  t_httpUpdate_return ret = ESPhttpUpdate.update(client, base + "/firmware.bin");
  if (ret == HTTP_UPDATE_FAILED) {
    Serial.print("[ota] HATA: "); Serial.println(ESPhttpUpdate.getLastErrorString());
    lcdShow("OTA HATA", "tekrar denenecek");
  }
  // Basarili olursa cihaz yeniden baslar; buraya donmez.
}

// -----------------------------------------------------------------------------
void setup() {
  Serial.begin(115200);
  delay(200);
  EEPROM.begin(EEPROM_SIZE);
  cfgLoad();

  Wire.begin(LCD_SDA, LCD_SCL);
  lcd.init(); lcd.backlight();
  lcdShow("Kartli Giris", FIRMWARE_VERSION);

  Serial.println("\n=================================");
  Serial.print(" Kartli Giris  "); Serial.println(FIRMWARE_VERSION);
  Serial.print(" Cihaz: "); Serial.println(deviceId());
  Serial.println("=================================");

  SPI.begin();
  rfid.PCD_Init();

  if (!cfgValid()) {
    Serial.println("[setup] Config yok. Seri porttan kurulum yap:");
    Serial.println("  SETUP ssid|sifre|host|port|bootstrap");
    lcdShow("Kurulum gerekli", "Seri: SETUP ...");
    return;  // loop() SETUP bekleyecek
  }

  connectWiFi();
  syncTime();

  if (strlen(cfg.secret) == 0) {
    Serial.println("[sir] Yok, kayit deneniyor...");
    registerDevice();
  } else {
    Serial.println("[sir] EEPROM'da mevcut.");
  }

  checkOta(false);  // acilista bir kez guncelleme kontrolu
  if (strlen(cfg.secret) > 0) lcdIdle();
}

void loop() {
  static unsigned long lastRegister = 0;

  handleSerial();

  if (!cfgValid()) return;  // kurulum bekleniyor

  if (WiFi.status() != WL_CONNECTED) { connectWiFi(); return; }

  if (strlen(cfg.secret) == 0) {
    if (millis() - lastRegister > REGISTER_RETRY_MS) { lastRegister = millis(); registerDevice(); }
    return;
  }

  if (millis() - lastHeartbeat > heartbeatMs) pollCommands();
  if (millis() - lastOtaCheck > otaCheckMs) checkOta(false);

  if (!idleShown && millis() - resultShownAt > RESULT_HOLD_MS) lcdIdle();

  String uid = readCardUid();
  if (uid.length() == 0) return;
  if (uid == lastUid && millis() - lastUidAt < SAME_CARD_BLOCK_MS) return;
  lastUid = uid; lastUidAt = millis();

  Serial.print("[kart] "); Serial.println(uid);
  sendScan(uid);
}
