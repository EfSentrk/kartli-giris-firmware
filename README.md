# Kartli Giris - NodeMCU Firmware

RFID kartli giris-cikis sistemi icin ESP8266 (NodeMCU) firmware'i.

Bu depo **public**'tir ve icinde **hicbir sir yoktur**. WiFi bilgisi, sunucu
adresi ve bootstrap sirri derleme aninda degil, cihazda seri porttan bir kez
girilir ve EEPROM'da saklanir. Yayinlanan `firmware.bin` bu yuzden guvenle
paylasilabilir.

## OTA (Over-The-Air) guncelleme

`kartli_giris/kartli_giris.ino` icindeki `FIRMWARE_VERSION` degistirilip `main`
dalina push edildiginde:

1. GitHub Actions firmware'i derler,
2. `firmware.bin` + `manifest.json` iceren bir Release yayinlar,
3. Sahadaki cihazlar acilista ve periyodik olarak en son surumu kontrol edip
   yeni surum varsa kendini gunceller.

Manifest her zaman su sabit adreste bulunur:
`https://github.com/EfSentrk/kartli-giris-firmware/releases/latest/download/manifest.json`

## Cihaz ilk kurulumu

Arduino IDE / arduino-cli ile bir kez USB'den yukledikten sonra, Seri
Monitor'de (115200) tek satirla kur:

```
SETUP <ssid>|<sifre>|<sunucu_ip>|<port>|<bootstrap_secret>
```

Diger komutlar: `INFO` (ayarlari goster), `RESET` (config sil), `OTA` (elle
guncelleme kontrolu).

## Kablolama

| RC522 | NodeMCU | | LCD I2C | NodeMCU |
|-------|---------|---|---------|---------|
| SDA/SS | D8 (GPIO15) | | SDA | D2 (GPIO4) |
| SCK | D5 (GPIO14) | | SCL | D1 (GPIO5) |
| MOSI | D7 (GPIO13) | | VCC | 5V |
| MISO | D6 (GPIO12) | | GND | GND |
| RST | D3 (GPIO0) | | | |
| 3.3V | 3V3 (5V VERME) | | | |
| GND | GND | | | |

D8->GND ve D3->3V3 arasina 10k dirensler acilis stabilitesi icin onerilir.

## Kutuphaneler

- MFRC522 (1.4.12)
- LiquidCrystal I2C (1.1.2)
- ESP8266 Arduino core (3.1.2)
