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
//   - 16x2 I2C LCD'de sonuc (adres acilista otomatik bulunur)
//   - Heartbeat + panel komut kuyrugu (CHECK_UPDATE); araliklar sunucudan
//   - OTA: hedef surumu panel belirler, binary GitHub'dan iner
//   - WiFi listesi panelden gonderilebilir (APPLY_SETTINGS)
//   - Internet yokken okutmalar flash'ta birikir, baglanti gelince yuklenir
//
// -----------------------------------------------------------------------------
// KABLOLAMA (mevcut mimari)
//   RC522: SDA/SS->D8(GPIO15) SCK->D5 MOSI->D7 MISO->D6 RST->D3(GPIO0) 3.3V GND
//   LCD  : SDA->D2(GPIO4) SCL->D1(GPIO5) VCC->5V(VIN) GND  (16x2)
//   LCD adresi: PROVISION_LCD_ADDR ile secilir, 0 ise otomatik taranir.
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
#include <LittleFS.h>
#include <memory>
#include <SPI.h>
#include <Wire.h>
#include <MFRC522.h>
#include <LiquidCrystal_I2C.h>
#include <bearssl/bearssl_hmac.h>
#include <time.h>

#define FIRMWARE_VERSION "0.15.0"

// =============================================================================
// FABRIKA AYARLARI  (opsiyonel)
// =============================================================================
//
// Bu blok BOS oldugunda cihaz acilista SETUP bekler ve yayinlanan .bin sirsiz
// kalir. Panel "Kurulum" bolumunde doldurulmus bir kopya uretir; o kopyayi
// yukleyen cihaz seri porta hic dokunmadan kendini kaydeder.
//
// DOLDURULMUS KOPYAYI DEPOYA COMMIT ETME: icinde WiFi sifreleri ve kayit sirri
// bulunur. Ayni sebeple ondan derlenen .bin de herkese acik paylasilmamali.
//
// Aglar "ssid|sifre;ssid|sifre" bicimindedir; bu yuzden ne ag adi ne sifre
// '|' veya ';' icerebilir (panel bunu zaten engelliyor).
#define PROVISION_WIFI   ""
#define PROVISION_HOST   ""
#define PROVISION_PORT   443
#define PROVISION_SECRET ""

// LCD I2C adresi. 0 = otomatik tara (0x20..0x27 ve 0x38..0x3F).
// Modulun adresini biliyorsan yazmak taramayi atlatir ve acilisi hizlandirir;
// bilmiyorsan 0 birak, cihaz kendi bulur ve seri porta yazar.
#define PROVISION_LCD_ADDR 0

// --- RC522 ---
static const uint8_t RC522_SS = 15, RC522_RST = 0;   // D8, D3
MFRC522 rfid(RC522_SS, RC522_RST);

// --- LCD ---
// LCD adresi SABIT DEGIL: I2C arka yuzeydeki PCF8574 ureticiye gore 0x27 ya
// da 0x3F adresinde olur. Sabit yazmak, yanlis moduldeki cihazda arka isigin
// yanip hicbir sey yazmamasina yol aciyordu; acilista veri yolunu tariyoruz.
static LiquidCrystal_I2C *lcd = nullptr;
static uint8_t lcdAddr = 0;
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
  // Yuklu firmware'e gomulu fabrika ayarlarinin ozeti. Yeni bir kopya
  // yuklendiginde (ornegin bir ag eklenmis) bu deger tutmaz ve ayarlar
  // yeniden uygulanir. Ayni kopya tekrar acildiginda tutar, boylece
  // panelden gonderilen degisiklikler her acilista ezilmez.
  uint32_t provisionHash;
};

static Config cfg;
static const int EEPROM_SIZE = sizeof(Config) + 8;
static ESP8266WiFiMulti wifiMulti;

bool cfgValid() {
  for (int i = 0; i < 4; i++) if (cfg.magic[i] != CFG_MAGIC[i]) return false;
  return true;
}

// FNV-1a: kisa ve carpisma ihtimali bu kullanim icin fazlasiyla dusuk.
uint32_t provisionHash() {
  uint32_t h = 2166136261UL;
  String all = String(PROVISION_WIFI) + "|" + PROVISION_HOST + "|" +
               String(PROVISION_PORT) + "|" + PROVISION_SECRET;
  for (size_t i = 0; i < all.length(); i++) {
    h ^= (uint8_t)all[i];
    h *= 16777619UL;
  }
  return h;
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
// Panelin dagitilmasini istedigi surum ve binary adresi. Heartbeat cevabindan
// dolar; bos ise sunucu henuz bir surum aktif etmemis demektir.
static String targetVersion = "";
static String targetUrl = "";
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

// epoch -> "2026-07-28T12:34:56Z". Sunucu ISO 8601 bekliyor.
String isoFromEpoch(uint32_t epoch) {
  time_t t = (time_t)epoch;
  struct tm *g = gmtime(&t);
  char buf[24];
  snprintf(buf, sizeof(buf), "%04d-%02d-%02dT%02d:%02d:%02dZ",
           g->tm_year + 1900, g->tm_mon + 1, g->tm_mday, g->tm_hour, g->tm_min, g->tm_sec);
  return String(buf);
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

// I2C veri yolunu tarar ve LCD adresini bulur.
//
// Once bilinen iki adresi deniyoruz; bulunamazsa yolda cevap veren ilk cihazi
// LCD kabul ediyoruz. Tarama sonucu seri porta yaziliyor: ekran calismadiginda
// "hic cihaz yok" (kablo) ile "adres farkli" (modul) ayrimini yapmanin baska
// yolu yok.
uint8_t findLcdAddress() {
  // Hat durumunu TESHIS icin okuyoruz, karar icin degil. Bazi moduller
  // acilista hatti bir an asagi cekiyor; buna bakip taramayi tumden atlamak
  // saglam bir ekrani gorunmez yapiyordu.
  pinMode(LCD_SDA, INPUT_PULLUP);
  pinMode(LCD_SCL, INPUT_PULLUP);
  Serial.print("[i2c] SDA="); Serial.print(digitalRead(LCD_SDA) ? "H" : "L");
  Serial.print(" SCL="); Serial.println(digitalRead(LCD_SCL) ? "H" : "L");

  Wire.begin(LCD_SDA, LCD_SCL);
  // Uzun/kotu kablolarda 100 kHz, varsayilan 400 kHz'den daha toleransli.
  Wire.setClock(100000);

  // Adres elle verilmisse once onu deniyoruz. Cevap vermezse taramaya
  // devam ediyoruz: yanlis bir secim yuzunden ekranin tumden kaybolmasi,
  // birkac milisaniyelik taramadan daha kotu.
  if (PROVISION_LCD_ADDR != 0) {
    Wire.beginTransmission((uint8_t)PROVISION_LCD_ADDR);
    if (Wire.endTransmission() == 0) {
      Serial.print("[lcd] Secilen adres 0x"); Serial.println(PROVISION_LCD_ADDR, HEX);
      return (uint8_t)PROVISION_LCD_ADDR;
    }
    Serial.print("[lcd] Secilen adres 0x"); Serial.print(PROVISION_LCD_ADDR, HEX);
    Serial.println(" cevap vermedi, taraniyor.");
  }

  // LCD arka yuzeyleri iki cip ailesinden birini kullanir:
  //   PCF8574  -> 0x20..0x27
  //   PCF8574A -> 0x38..0x3F
  // Yalnizca 0x27 ve 0x3F'e bakmak, A3-A0 jumperlari lehimli modulleri
  // gormuyordu. Butun adres alanini taramak yerine bu 16 adresi yokluyoruz:
  // teshis icin yeterince genis, acilisi kilitlemeyecek kadar dar.
  uint8_t hit = 0;
  for (uint8_t addr = 0x20; addr <= 0x3F; addr++) {
    if (addr > 0x27 && addr < 0x38) continue;
    Wire.beginTransmission(addr);
    if (Wire.endTransmission() == 0) {
      Serial.print("[i2c] cihaz: 0x"); Serial.println(addr, HEX);
      if (!hit) hit = addr;
    }
  }

  if (hit) {
    Serial.print("[lcd] Adres 0x"); Serial.println(hit, HEX);
    return hit;
  }

  Serial.println("[lcd] I2C'de ekran yok. Kontrol sirasi:");
  Serial.println("      1) VCC 5V (VIN) pinine bagli mi? 3V3 yetmez.");
  Serial.println("      2) SDA->D2, SCL->D1, GND ortak mi?");
  Serial.println("      3) Arka yuzeydeki kontrast potunu cevir.");
  return 0;
}

// -----------------------------------------------------------------------------
// LCD
// -----------------------------------------------------------------------------
void lcdShow(const String &l1, const String &l2) {
  // Ekran bulunamadiysa cihaz calismaya devam etmeli; kart okuma ve kayit
  // LCD'ye bagli degil, yalnizca geri bildirim kaybolur.
  if (!lcd) return;
  lcd->clear();
  lcd->setCursor(0, 0); lcd->print(l1.substring(0, 16));
  lcd->setCursor(0, 1); lcd->print(l2.substring(0, 16));
}
// Ikinci satir baglanti durumunu tasiyor: cevrimdisiyken kullanici kart
// okutmaya devam edebilmeli ama kaydin anlik islenmedigini bilmeli.
void lcdIdle() {
  bool online = WiFi.status() == WL_CONNECTED;
  lcdShow("Kart okutun", online ? "" : "Internet yok");
  idleShown = true;
}

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

// Derleme aninda gomulu fabrika ayarlarini EEPROM'a yazar.
void applyProvisioning() {
  // Cihaz sirrini KORUYORUZ. Silseydik cihaz yeniden kayit denerdi, sunucu ise
  // zaten kayitli bir cihaza yeni sir vermiyor; cihaz "panelden sil" ekraninda
  // takilir ve elle mudahale gerekirdi.
  char keepSecret[97];
  memcpy(keepSecret, cfg.secret, sizeof(keepSecret));

  memset(&cfg, 0, sizeof(cfg));
  memcpy(cfg.secret, keepSecret, sizeof(cfg.secret));

  String list = PROVISION_WIFI;
  uint8_t slot = 0;
  int start = 0;
  while (slot < WIFI_SLOTS && start < (int)list.length()) {
    int sep = list.indexOf(';', start);
    String pair = sep < 0 ? list.substring(start) : list.substring(start, sep);
    int bar = pair.indexOf('|');
    String ssid = bar < 0 ? pair : pair.substring(0, bar);
    String pass = bar < 0 ? "" : pair.substring(bar + 1);
    ssid.trim();
    if (ssid.length() > 0) {
      ssid.toCharArray(cfg.nets[slot].ssid, sizeof(cfg.nets[slot].ssid));
      pass.toCharArray(cfg.nets[slot].pass, sizeof(cfg.nets[slot].pass));
      slot++;
    }
    if (sep < 0) break;
    start = sep + 1;
  }

  String(PROVISION_HOST).toCharArray(cfg.serverHost, sizeof(cfg.serverHost));
  cfg.serverPort = PROVISION_PORT;
  String(PROVISION_SECRET).toCharArray(cfg.bootstrap, sizeof(cfg.bootstrap));
  cfg.provisionHash = provisionHash();
  cfgSave();

  Serial.print("[setup] Fabrika ayarlari uygulandi: ");
  Serial.print(slot); Serial.print(" ag, host "); Serial.println(cfg.serverHost);
  lcdShow("Kurulum", "yapiliyor...");
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
// Cevrimdisi tampon
// -----------------------------------------------------------------------------
//
// Internet yokken okutmalar flash'a yaziliyor, baglanti gelince topluca
// gonderiliyor. Cihaz GIRIS mi CIKIS mi oldugunu KENDI karar vermiyor: ham
// okutmayi saklayip karari sunucuya birakiyor. Aksi halde cevrimdisi verilen
// kararlarla sunucudaki gecmis catisirdi.
//
// Satir bicimi:  <kimlik>,<epoch>,<millis>,<uid>
// epoch 0 ise okutma aninda saat kurulu degildi; o kayit gonderilirken
// millis farkindan geriye hesaplaniyor.
static const char *BUFFER_PATH = "/scans.csv";
// Flash'i doldurmamak icin ust sinir. Asildiginda EN ESKI kayitlar yerine
// yenileri yazilmiyor: eski kayitlar zaten olmus olaylar, yeni okutma
// kullanicinin tekrar deneyebilecegi bir sey.
static const size_t BUFFER_MAX_BYTES = 32768;
static bool fsReady = false;

// Her acilista degisen kimlik. Yeniden baslatma sonrasi millis sifirlandigi
// icin, onceki oturumdan kalan kayitlarin zamani millis ile hesaplanamaz.
static uint32_t bootId = 0;

void bufferInit() {
  fsReady = LittleFS.begin();
  if (!fsReady) {
    // Fabrikadan cikan kartta dosya sistemi bicimlendirilmemis olur; ilk
    // acilista bir kez bicimlendiriyoruz.
    Serial.println("[tampon] Dosya sistemi bicimlendiriliyor...");
    fsReady = LittleFS.format() && LittleFS.begin();
  }
  if (!fsReady) {
    Serial.println("[tampon] LittleFS acilamadi; cevrimdisi kayit yapilamaz.");
    return;
  }
  bootId = RANDOM_REG32;
  File f = LittleFS.open(BUFFER_PATH, "r");
  if (f) { Serial.print("[tampon] "); Serial.print(f.size()); Serial.println(" byte bekliyor."); f.close(); }
}

void bufferAppend(const String &uid) {
  if (!fsReady) return;

  File check = LittleFS.open(BUFFER_PATH, "r");
  size_t size = check ? check.size() : 0;
  if (check) check.close();
  if (size > BUFFER_MAX_BYTES) {
    Serial.println("[tampon] Dolu, kayit atlandi.");
    lcdShow("Hafiza dolu", "Yetkiliye bildir");
    return;
  }

  uint32_t now = (uint32_t)time(nullptr);
  // 1.6 milyar oncesi bir deger saatin hic kurulmadigini gosterir.
  if (now < 1600000000UL) now = 0;

  File f = LittleFS.open(BUFFER_PATH, "a");
  if (!f) { Serial.println("[tampon] Dosya acilamadi."); return; }
  f.print(bootId, HEX); f.print("-"); f.print(millis(), HEX); f.print(",");
  f.print(now); f.print(","); f.print(millis()); f.print(","); f.println(uid);
  f.close();

  Serial.print("[tampon] Kaydedildi: "); Serial.println(uid);
}

/**
 * Tamponu sunucuya yukler.
 *
 * Yukleme basarili olursa dosya siliniyor. Kismen basarili olursa dosyayi
 * OLDUGU GIBI birakiyoruz: sunucu ayni kimligi ikinci kez yok sayacagi icin
 * tekrar gondermek zarar vermez, ama kaybetmek geri alinamaz.
 */
// Her loop turunda cagriliyor ama isi seyrek yapiyor: dosyayi saniyede
// binlerce kez acmak flash'i bosuna yorar ve kart okumayi yavaslatir.
static const unsigned long FLUSH_INTERVAL_MS = 15000UL;

// Tamponun basindaki `sent` satiri atar, kalani korur.
//
// LittleFS'te dosyanin basindan silme yok; kalani gecici dosyaya yazip yer
// degistiriyoruz. Once gecici dosyayi tamamlayip sonra asili silmemizin
// sebebi, bu sirada elektrik giderse kayitlarin durmasi.
void dropSentLines(uint16_t sent) {
  File src = LittleFS.open(BUFFER_PATH, "r");
  if (!src) return;

  for (uint16_t i = 0; i < sent && src.available(); i++) src.readStringUntil('\n');

  if (!src.available()) { src.close(); LittleFS.remove(BUFFER_PATH); return; }

  File tmp = LittleFS.open("/scans.tmp", "w");
  if (!tmp) { src.close(); return; }

  while (src.available()) {
    String line = src.readStringUntil('\n');
    line.trim();
    if (line.length() > 0) tmp.println(line);
  }
  src.close();
  tmp.close();

  LittleFS.remove(BUFFER_PATH);
  LittleFS.rename("/scans.tmp", BUFFER_PATH);
  Serial.println("[tampon] Kalan kayitlar korundu, sonraki turda gonderilecek.");
}

void bufferFlush() {
  static unsigned long lastFlush = 0;
  if (!fsReady || WiFi.status() != WL_CONNECTED || strlen(cfg.secret) == 0) return;
  if (millis() - lastFlush < FLUSH_INTERVAL_MS) return;
  lastFlush = millis();

  if (!LittleFS.exists(BUFFER_PATH)) return;

  File f = LittleFS.open(BUFFER_PATH, "r");
  if (!f) return;
  if (f.size() == 0) { f.close(); LittleFS.remove(BUFFER_PATH); return; }

  Serial.println("[tampon] Yukleniyor...");
  lcdShow("Kayitlar", "yukleniyor...");

  uint32_t nowEpoch = (uint32_t)time(nullptr);
  String json = "{\"events\":[";
  uint16_t count = 0;

  while (f.available() && count < 50) {
    String line = f.readStringUntil('\n');
    line.trim();
    if (line.length() == 0) continue;

    int c1 = line.indexOf(','), c2 = line.indexOf(',', c1 + 1), c3 = line.indexOf(',', c2 + 1);
    if (c1 < 0 || c2 < 0 || c3 < 0) continue;

    String id = line.substring(0, c1);
    uint32_t epoch = (uint32_t)line.substring(c1 + 1, c2).toInt();
    unsigned long at = (unsigned long)line.substring(c2 + 1, c3).toInt();
    String uid = line.substring(c3 + 1);

    // Saat okutma aninda kuruluysa onu kullaniyoruz. Degilse ve kayit BU
    // oturumdansa millis farkindan geriye hesapliyoruz. Ikisi de yoksa zaman
    // gondermiyoruz; sunucu varis anini kullanir ve bunu bilerek kabul
    // ediyoruz: yaklasik bir zaman, hic kayit olmamasindan iyidir.
    String timeField = "";
    if (epoch > 0) {
      timeField = String(",\"event_time\":\"") + isoFromEpoch(epoch) + "\"";
    } else if (id.startsWith(String(bootId, HEX) + "-") && nowEpoch > 1600000000UL) {
      uint32_t back = (uint32_t)((millis() - at) / 1000UL);
      timeField = String(",\"event_time\":\"") + isoFromEpoch(nowEpoch - back) + "\"";
    }

    if (count > 0) json += ",";
    json += "{\"uid\":\"" + uid + "\",\"event_id\":\"" + id +
            "\",\"firmware_version\":\"" + FIRMWARE_VERSION + "\"" + timeField + "}";
    count++;
  }
  f.close();

  if (count == 0) { LittleFS.remove(BUFFER_PATH); return; }
  json += "]}";

  String resp;
  int code = signedPost("/api/devices/scan/batch", json, resp);

  if (code == 200) {
    Serial.print("[tampon] "); Serial.print(count); Serial.println(" kayit yuklendi.");
    // Yalnizca GONDERILEN satirlari dusuyoruz. Dosyanin tamamini silmek,
    // 50'den fazla kayit birikmisse gonderilmeyenleri de yok ederdi; uzun bir
    // kesintiden sonra tam da en cok kayit varken vuran bir hata olurdu.
    dropSentLines(count);
    lcdShow("Kayitlar", "yuklendi");
  } else {
    Serial.print("[tampon] Yukleme basarisiz HTTP "); Serial.println(code);
  }
  resultShownAt = millis(); idleShown = false;
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

// Sunucudan gelen "wifi":[{"ssid":"..","password":".."}] listesini EEPROM'a yazar.
//
// Liste BOSSA hicbir sey yapmiyoruz. Aksi halde panelde ag tanimlamayi unutmus
// biri "Karta yolla" dedigi anda cihaz butun aglarini kaybeder ve bir daha
// baglanamaz; boyle bir hatanin bedeli cihazi sokup USB'ye takmak olur.
void applyWifiFromJson(const String &body) {
  int listStart = body.indexOf("\"wifi\":[");
  if (listStart < 0) { Serial.println("[wifi] Listede ag yok, degisiklik yapilmadi."); return; }

  WifiNet parsed[WIFI_SLOTS];
  memset(parsed, 0, sizeof(parsed));
  uint8_t count = 0;

  int cursor = listStart;
  while (count < WIFI_SLOTS) {
    int ssidAt = body.indexOf("\"ssid\":\"", cursor);
    if (ssidAt < 0) break;
    int ssidEnd = body.indexOf('"', ssidAt + 8);
    if (ssidEnd < 0) break;
    String ssid = body.substring(ssidAt + 8, ssidEnd);

    String pass = "";
    int passAt = body.indexOf("\"password\":\"", ssidEnd);
    // Sifre alani bir SONRAKI ssid'den once gelmeli; yoksa o ag sifresizdir.
    int nextSsid = body.indexOf("\"ssid\":\"", ssidEnd);
    if (passAt >= 0 && (nextSsid < 0 || passAt < nextSsid)) {
      int passEnd = body.indexOf('"', passAt + 12);
      if (passEnd >= 0) pass = body.substring(passAt + 12, passEnd);
    }

    if (ssid.length() > 0) {
      ssid.toCharArray(parsed[count].ssid, sizeof(parsed[count].ssid));
      pass.toCharArray(parsed[count].pass, sizeof(parsed[count].pass));
      count++;
    }
    cursor = ssidEnd + 1;
  }

  if (count == 0) { Serial.println("[wifi] Ayristirilabilir ag yok, degisiklik yapilmadi."); return; }

  memcpy(cfg.nets, parsed, sizeof(cfg.nets));
  cfgSave();

  Serial.print("[wifi] "); Serial.print(count); Serial.println(" ag panelden guncellendi:");
  for (uint8_t i = 0; i < count; i++) { Serial.print("   - "); Serial.println(cfg.nets[i].ssid); }

  // Bagli oldugumuz ag listeden cikmis olabilir; bir sonraki kopmada
  // yeni liste zaten devreye girer, simdi baglantiyi kesmiyoruz.
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

  // Hedef surum bilgisi. Sunucu aktif surum secmemisse alanlar hic gelmez;
  // o durumda eski degeri korumak yerine temizliyoruz ki panelden aktif surum
  // kaldirildiginda cihaz eski hedefi kurmaya calismasin.
  targetVersion = jsonString(resp, "firmware_version");
  targetUrl = jsonString(resp, "firmware_url");

  // Panelden gonderilen ag listesini uygula.
  if (resp.indexOf("APPLY_SETTINGS") >= 0) {
    Serial.println("[komut] APPLY_SETTINGS alindi.");
    applyWifiFromJson(resp);
  }

  // Tam bir JSON ayristiricisi yerine komut tipinin adini ariyoruz; iki tip
  // icin yeterli. Uctan fazla komut tipi olursa burasi gercek bir parser ister.
  if (resp.indexOf("CHECK_UPDATE") >= 0) {
    Serial.println("[komut] CHECK_UPDATE alindi, guncelleme kontrol ediliyor.");
    checkOta(true);
  }
}

// -----------------------------------------------------------------------------
// Kart okutma -> imzali scan
// -----------------------------------------------------------------------------
void sendScan(const String &uid) {
  // Internet yokken sunucuya sormanin anlami yok: dogrudan tampona.
  if (WiFi.status() != WL_CONNECTED) {
    bufferAppend(uid);
    lcdShow("Kaydedildi", "Internet yok");
    resultShownAt = millis(); idleShown = false;
    return;
  }

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
  else {
    // Sunucuya ulasilamadi (kopuk hat, DNS, zaman asimi). Kayit kaybolmasin:
    // tampona alip baglanti duzelince yolluyoruz. 401/403 bunun disinda
    // tutuluyor cunku onlar tekrar denemekle duzelmez.
    if (code < 0 || code >= 500) {
      bufferAppend(uid);
      lcdShow("Kaydedildi", "Sunucu yok");
    } else {
      lcdShow("Sunucu hatasi", String("HTTP ") + code);
    }
    Serial.print("[scan] HTTP "); Serial.println(code);
  }

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
// Hedef surumu PANEL belirler, GitHub'in "en son"u degil.
//
// Fark pratikte su: en son release'e bakan bir cihaz hatali bir surum
// yayinlandiginda geri donemez, cunku yayinlanmis tag geri alinamaz. Karar
// panelde oldugunda "onceki surume don" tek tik. Binary yine GitHub'da duruyor.
//
// Hedef bilgisi heartbeat cevabindan geliyor; hic heartbeat yapilmadiysa
// (ornegin acilistaki ilk kontrol) hedef bos olur ve guncelleme atlanir.
void checkOta(bool forced) {
  if (WiFi.status() != WL_CONNECTED) return;
  lastOtaCheck = millis();

  if (targetVersion.length() == 0 || targetUrl.length() == 0) {
    Serial.println("[ota] Sunucu bir surum aktif etmemis, atlaniyor.");
    if (forced) lcdShow("OTA", "aktif surum yok");
    return;
  }

  Serial.print("[ota] yuklu="); Serial.print(FIRMWARE_VERSION);
  Serial.print("  hedef="); Serial.println(targetVersion);

  // Esitse is yok. Farkliysa indiriyoruz: hedef daha ESKI bir surum de
  // olabilir, geri alma boyle calisiyor.
  if (targetVersion == FIRMWARE_VERSION) {
    if (forced) lcdShow("OTA", "guncel");
    return;
  }

  Serial.println("[ota] Surum farkli, indiriliyor...");
  lcdShow("Guncelleniyor", targetVersion);

  // Sertifika dogrulamasi yok; binary'nin butunlugunu ESPhttpUpdate zaten
  // flash yazarken kontrol ediyor, uydurma bir dosya cihazi acmaz.
  WiFiClientSecure client;
  client.setInsecure();
  client.setBufferSizes(1024, 1024);

  ESPhttpUpdate.rebootOnUpdate(true);
  // GitHub asset adresi indirmeyi baska bir konuma yonlendiriyor.
  ESPhttpUpdate.followRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
  t_httpUpdate_return ret = ESPhttpUpdate.update(client, targetUrl);
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

  // Wire.begin findLcdAddress icinde, hat kontrolunden sonra cagriliyor.
  lcdAddr = findLcdAddress();
  if (lcdAddr) {
    lcd = new LiquidCrystal_I2C(lcdAddr, 16, 2);
    lcd->init();
    lcd->backlight();
  }
  lcdShow("Kartli Giris", FIRMWARE_VERSION);

  Serial.println("\n=================================");
  Serial.print(" Kartli Giris  "); Serial.println(FIRMWARE_VERSION);
  Serial.print(" Cihaz: "); Serial.println(deviceId());
  Serial.println("=================================");

  SPI.begin();
  rfid.PCD_Init();
  bufferInit();

  // Fabrika ayarlari doluysa iki durumda uygulaniyor: cihazda hic config
  // yoksa, ya da YUKLENEN KOPYA degismisse (ozet tutmuyorsa). Ikincisi
  // "panelden kodu al, yukle, bitsin" akisini mumkun kiliyor: ag eklediginde
  // yeni kopyayi yuklemek yetiyor.
  //
  // Ayni kopya tekrar acildiginda ozet tuttugu icin hicbir sey yapilmiyor;
  // boylece panelden gonderilen ag degisiklikleri her acilista ezilmiyor.
  if (strlen(PROVISION_HOST) > 0 && strlen(PROVISION_WIFI) > 0 &&
      (!cfgValid() || cfg.provisionHash != provisionHash())) {
    Serial.println(cfgValid() ? "[setup] Gomulu ayarlar degismis, uygulaniyor."
                              : "[setup] Config yok, gomulu ayarlar uygulaniyor.");
    applyProvisioning();
  }

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

  // Once birikmis kayitlar: heartbeat'ten once bosaltmak, panelde
  // cihazin cevrimici gorunmesiyle kayitlarin gelmesi arasindaki farki kapatir.
  bufferFlush();

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
