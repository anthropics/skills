#!/bin/bash
# iOS PACKAGE GATE - inspects a signed .ipa/.app as an ARTIFACT, not as build output.
#
# WHY: "ARCHIVE SUCCEEDED" DOES NOT PROVE the package is signed. Measured: a build
# printed `** ARCHIVE SUCCEEDED **` and the bundle was `code object is not signed at all`.
# So this gate opens the package and measures the artifact itself.
#
# Usage: package-gate.sh <path.ipa|path.app> [options]
# Exit code: 0 = all gates PASS, 1 = at least one FAIL (usable as a CI gate)
set -o pipefail
HEDEF="${1:?usage: package-gate.sh <path.ipa|path.app> [options]}"
BEKLENEN_BUNDLE=""; BEKLENEN_AD=""; BEKLENEN_SURUM=""; TEST_VEKTOR_DESENI=""; BEKLENEN_IZIN=""
shift || true
while [ $# -gt 0 ]; do
  case "$1" in
    --expect-bundle) BEKLENEN_BUNDLE="${2:-}"; shift 2 ;;
    --expect-name)     BEKLENEN_AD="${2:-}";     shift 2 ;;
    --expect-version)  BEKLENEN_SURUM="${2:-}";  shift 2 ;;
    --test-vectors)     TEST_VEKTOR_DESENI="${2:-}"; shift 2 ;;
    --permissions)            BEKLENEN_IZIN="${2:-}";      shift 2 ;;
    *) echo "unknown option: $1"; exit 2 ;;
  esac
done
SONUC=0
GECEN=0; DUSEN=0

ol() { # ol <ad> <kosul-ciktisi: PASS/FAIL> <ham>
  if [ "$2" = "PASS" ]; then GECEN=$((GECEN+1)); printf '  PASS  %-34s %s\n' "$1" "$3"
  else DUSEN=$((DUSEN+1)); SONUC=1; printf '  FAIL  %-34s %s\n' "$1" "$3"; fi
}

CALISMA=$(mktemp -d)
temizle() { rm -rf "$CALISMA"; }
trap temizle EXIT

case "$HEDEF" in
  *.ipa) unzip -q "$HEDEF" -d "$CALISMA/x" || { echo "could not unzip ipa"; exit 2; }
         APP=$(find "$CALISMA/x/Payload" -maxdepth 1 -name "*.app" | head -1) ;;
  *.app) APP="$HEDEF" ;;
  *) echo "unsupported target: $HEDEF"; exit 2 ;;
esac
[ -d "$APP" ] || { echo "app bundle not found"; exit 2; }
PL="$APP/Info.plist"
echo "PACKAGE GATE - $(basename "$HEDEF")"
echo "  bundle: $(basename "$APP") · $(du -sk "$APP" | awk '{print $1}') KB"

# 1) IMZA VAR MI ve DAGITIM IMZASI MI
IMZA=$(codesign -dvv "$APP" 2>&1)
if printf '%s' "$IMZA" | grep -q "code object is not signed at all"; then
  ol "signature present" FAIL "NOT SIGNED AT ALL"
else
  ol "signature present" PASS "present"
  YETKILI=$(printf '%s' "$IMZA" | grep -m1 "^Authority=" | sed 's/^Authority=//')
  case "$YETKILI" in
    *Distribution*) ol "distribution signature" PASS "$YETKILI" ;;
    *) ol "distribution signature" FAIL "$YETKILI (NOT a distribution identity)" ;;
  esac
fi

# 2) IMZA BUTUNLUGU
if codesign --verify --deep --strict "$APP" >/dev/null 2>&1; then
  ol "signature integrity" PASS "valid on disk + designated requirement"
else
  ol "signature integrity" FAIL "$(codesign --verify --deep --strict "$APP" 2>&1 | tail -1)"
fi

# 3) ENTITLEMENTS — get-task-allow KAPALI (acik olani App Store kabul etmez)
ENT=$(codesign -d --entitlements :- "$APP" 2>/dev/null | plutil -p - 2>/dev/null)
GTA=$(printf '%s' "$ENT" | grep -m1 "get-task-allow" | awk -F'=> ' '{print $2}')
[ "$GTA" = "false" ] && ol "get-task-allow disabled" PASS "false" || ol "get-task-allow disabled" FAIL "${GTA:-YOK}"
BRA=$(printf '%s' "$ENT" | grep -m1 "beta-reports-active" | awk -F'=> ' '{print $2}')
[ "$BRA" = "true" ] && ol "beta-reports-active" PASS "true (TestFlight)" || ol "beta-reports-active" FAIL "${BRA:-YOK}"

# 4) GOMULU PROFIL — cihaz listesi OLMAMALI (App Store profili)
PROF="$APP/embedded.mobileprovision"
if [ -f "$PROF" ]; then
  PD=$(security cms -D -i "$PROF" 2>/dev/null | plutil -p - 2>/dev/null)
  AD=$(printf '%s' "$PD" | grep -m1 '"Name"' | sed 's/.*=> //')
  if printf '%s' "$PD" | grep -q "ProvisionedDevices"; then
    ol "profile: no device list" FAIL "ProvisionedDevices PRESENT -> development profile $AD"
  else
    ol "profile: no device list" PASS "$AD"
  fi
else
  ol "embedded profile" FAIL "embedded.mobileprovision MISSING"
fi

# 5) MIMARI — arm64
MIM=$(lipo -info "$APP/$(/usr/libexec/PlistBuddy -c 'Print :CFBundleExecutable' "$PL" 2>/dev/null)" 2>/dev/null | sed 's/.*: //')
case "$MIM" in *arm64*) ol "architecture arm64" PASS "$MIM" ;; *) ol "architecture arm64" FAIL "${MIM:-unreadable}" ;; esac

# 6) SURUM ALANLARI
SV=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleShortVersionString' "$PL" 2>/dev/null)
BV=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleVersion' "$PL" 2>/dev/null)
BID=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleIdentifier' "$PL" 2>/dev/null)
AD2=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleDisplayName' "$PL" 2>/dev/null)
if [ -n "$SV" ] && [ -n "$BV" ]; then
  if [ -n "$BEKLENEN_SURUM" ] && [ "$SV" != "$BEKLENEN_SURUM" ]; then
    ol "version fields" FAIL "$SV ($BV) — expected $BEKLENEN_SURUM"
  else
    ol "version fields" PASS "$SV ($BV)"
  fi
else
  ol "version fields" FAIL "kisa='$SV' build='$BV'"
fi
# PROJE SABITI DEGIL PARAMETRE: expected display name --expect-name ile verilir.
if [ -n "$BEKLENEN_AD" ]; then
  [ "$AD2" = "$BEKLENEN_AD" ] && ol "display name" PASS "$AD2" || ol "display name" FAIL "'$AD2' != '$BEKLENEN_AD'"
else
  [ -n "$AD2" ] && ol "display name present" PASS "$AD2" || ol "display name present" FAIL "CFBundleDisplayName EMPTY"
fi
if [ -n "$BEKLENEN_BUNDLE" ]; then
  [ "$BID" = "$BEKLENEN_BUNDLE" ] && ol "bundle identifier" PASS "$BID" || ol "bundle identifier" FAIL "$BID != $BEKLENEN_BUNDLE"
else
  ol "bundle identifier" PASS "$BID (expected verilmedi)"
fi

# 7) GIZLILIK MANIFESTI pakette OLMALI
[ -f "$APP/PrivacyInfo.xcprivacy" ] && ol "privacy manifest" PASS "PrivacyInfo.xcprivacy present" \
  || ol "privacy manifest" FAIL "PrivacyInfo.xcprivacy MISSING"

# 8) IKON pakette OLMALI
if [ -f "$APP/Assets.car" ] || ls "$APP"/AppIcon*.png >/dev/null 2>&1; then
  ol "app icon" PASS "$(ls "$APP" | grep -cE 'Assets.car|AppIcon.*png') artifact(s)"
else
  ol "app icon" FAIL "neither Assets.car nor AppIcon*.png"
fi

# 9) IZIN METINLERI — BEYAN EDILENLERLE SINIRLI OLMALI
#
# PROJE SABITI GOMULMEZ (duzeltildi 2026-10-09, FARKLI PROJEDE OLCULEN YANLIS ALARM).
# Ilk surum Ürün A'den gelmisti ve "mikrofon/kamera/konum/rehber izni HIC OLMAMALI" diyordu;
# bu Ürün A icin dogru (akis izin istemiyor) ama ORTAK kural DEGIL. Ürün B paketinde kapi
# kirmizi yandi: NSMicrophoneUsageDescription + NSPhotoLibraryUsageDescription vardi ve
# IKISI DE MESRU (urun kararı: "kendi sesini koy" + "karakterine yuz ver").
# Yani kapi urune kendi varsayimini yaziyordu.
#
# Artik kural su: --permissions ile BEYAN EDILEN izinler beklenir; beyan edilmeyen bir izin
# metni cikarsa KIRMIZI (gercek risk: sessizce eklenen izin). --permissions verilmezse yalnız
# BILGI basilir, hukum verilmez.
MEVCUT_IZIN=$(plutil -p "$PL" 2>/dev/null | grep -oE "NS[A-Za-z]+UsageDescription" | sort -u)
if [ -n "$BEKLENEN_IZIN" ]; then
  FAZLA=""
  for i in $MEVCUT_IZIN; do
    case ",$BEKLENEN_IZIN," in *",$i,"*) ;; *) FAZLA="$FAZLA $i" ;; esac
  done
  [ -z "$FAZLA" ] && ol "permissions match declaration" PASS "$(echo $MEVCUT_IZIN | tr '\n' ' ')" \
    || ol "permissions match declaration" FAIL "UNDECLARED:$FAZLA"
elif [ -n "$MEVCUT_IZIN" ]; then
  printf '  BILGI %-34s %s\n' "permission strings (no declaration given)" "$(echo $MEVCUT_IZIN | tr '\n' ' ')"
else
  ol "no permission strings" PASS "0"
fi

# 9b) TEST VEKTORLERI / FIXTURE PAKETTE OLMAMALI (Ürün B'tan gelen kapi, 2026-10)
# Gerekce: altin file(s)lari, seed vektorleri ve fixture'lar gelistirmede paketin icine
# kopyalanabiliyor; magazaya giden ikili onlari TASIMAMALI (hem boyut hem sizinti).
if [ -n "$TEST_VEKTOR_DESENI" ]; then
  BULUNAN=$(find "$APP" \( -name "$TEST_VEKTOR_DESENI" \) 2>/dev/null | wc -l | tr -d ' ')
  [ "$BULUNAN" = "0" ] && ol "no test vectors in bundle" PASS "pattern '$TEST_VEKTOR_DESENI' -> 0 file(s)" \
    || ol "no test vectors in bundle" FAIL "$BULUNAN file(s) ('$TEST_VEKTOR_DESENI')"
fi

# 10) IHRACAT BEYANI, KAYNAKLA TUTARLI OLMALI
BEYAN=$(/usr/libexec/PlistBuddy -c 'Print :ITSAppUsesNonExemptEncryption' "$PL" 2>/dev/null)
KOK="$(cd "$(dirname "$0")/.." && pwd)"
# KAYNAK AGACI: proje dizin adlari GOMULU DEGIL. Varsayilan olarak depo kokundeki tum
# .swift file(s)lari taranir; GATE_SOURCE_PATHS ile daraltilabilir.
KAYNAK_YOLLARI="${GATE_SOURCE_PATHS:-$KOK}"
SIFRELEME=$(grep -rlE --include=*.swift "SymmetricKey|AES\.|ChaCha|\.seal\(|sealedBox|SecKeyCreate" \
  $KAYNAK_YOLLARI 2>/dev/null | wc -l | tr -d ' ')
if [ "$SIFRELEME" = "0" ]; then
  [ "$BEYAN" = "false" ] && ol "export declaration (no encryption)" PASS "false · kaynakta sifreleme API'si 0 file(s)" \
    || ol "export declaration (no encryption)" FAIL "beyan='$BEYAN' but source has no encryption -> must be false"
else
  [ "$BEYAN" = "false" ] && ol "export declaration" FAIL "declared false BUT source has $SIFRELEME file(s)da sifreleme API'si present" \
    || ol "export declaration" PASS "beyan='$BEYAN' · $SIFRELEME file(s)da sifreleme API'si"
fi

echo "  --> PASS=$GECEN FAIL=$DUSEN"
[ "$SONUC" = "0" ] && echo "** PACKAGE GATE CLEAN **" || echo "** PACKAGE GATE RED **"
exit $SONUC
