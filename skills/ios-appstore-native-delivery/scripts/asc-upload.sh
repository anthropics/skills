#!/bin/bash
# App Store Connect upload chain: validate -> upload -> processing -> internal group -> tester.
#
# Each stage is proven SEPARATELY, because "uploaded", "VALID" and "reachable by the internal
# group" are THREE DIFFERENT STATES and collapsing them is how a release gets reported as done
# while nobody can install it. Installing on a device is a fourth thing this script never does.
#
# No blind retry: if a stage fails the script classifies it and STOPS. It never re-uploads the
# same binary, because that burns a build number and hides the original error.
#
# Credentials come from the environment, with NO built-in default. A default would both leak an
# account identifier into a shared file and make the script silently look for the wrong key on
# someone else's machine.
#   export ASC_KEY_ID=<Key ID>
#   export ASC_P8=<full path to AuthKey_<KeyID>.p8>     # chmod 600
#   export ASC_ISSUER=<Issuer ID>                       # or ASC_ISSUER_KEYCHAIN=<service>
#
# Usage: asc-upload.sh <path.ipa> <bundle-id>
set -o pipefail
IPA="${1:?usage: asc-upload.sh <path.ipa> <bundle-id>}"
BUNDLE="${2:?bundle id is required - no project constant is embedded in this script}"
HERE="$(cd "$(dirname "$0")" && pwd)"
KEY_ID="${ASC_KEY_ID:?ASC_KEY_ID must be set (App Store Connect API Key ID)}"
P8="${ASC_P8:?ASC_P8 must be set (full path to the .p8 file)}"
if [ -z "${ASC_ISSUER:-}" ]; then
  SERVICE="${ASC_ISSUER_KEYCHAIN:?set ASC_ISSUER, or ASC_ISSUER_KEYCHAIN to read it from the keychain}"
  ASC_ISSUER="$(security find-generic-password -s "$SERVICE" -w 2>/dev/null)"
fi
export ASC_ISSUER ASC_KEY_ID="$KEY_ID" ASC_P8="$P8"
[ -f "$IPA" ] || { echo "ipa not found: $IPA"; exit 2; }
[ -f "$P8" ]  || { echo "ASC key not found: $P8"; exit 2; }
[ -n "$ASC_ISSUER" ] || { echo "issuer is empty (keychain service: ${ASC_ISSUER_KEYCHAIN:-not given})"; exit 2; }

api() { python3 "$HERE/asc-request.py" "$@"; }
stage() { printf '\n== %s ==\n' "$1"; }

# altool looks for the key under ./private_keys. The secret is NOT copied - it is symlinked.
WORK=$(mktemp -d); mkdir -p "$WORK/private_keys"
ln -sf "$P8" "$WORK/private_keys/AuthKey_$KEY_ID.p8"
trap 'rm -rf "$WORK"' EXIT

# Version/build/bundle are read from THE PACKAGE ITSELF, never typed into a report by hand.
TMPAPP=$(mktemp -d); unzip -q "$IPA" -d "$TMPAPP"
APP=$(find "$TMPAPP/Payload" -maxdepth 1 -name '*.app' | head -1)
SHORT=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleShortVersionString' "$APP/Info.plist")
BUILD=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleVersion' "$APP/Info.plist")
PKG_BUNDLE=$(/usr/libexec/PlistBuddy -c 'Print :CFBundleIdentifier' "$APP/Info.plist")
rm -rf "$TMPAPP"
echo "package: $PKG_BUNDLE $SHORT ($BUILD) · sha256=$(shasum -a 256 "$IPA" | awk '{print $1}')"
[ "$PKG_BUNDLE" = "$BUNDLE" ] || { echo "FAIL  package bundle ($PKG_BUNDLE) != expected ($BUNDLE)"; exit 2; }

stage "0) App Store Connect app record"
APP_ID=$(api GET "/v1/apps?filter%5BbundleId%5D=$BUNDLE&fields%5Bapps%5D=bundleId,name" 2>/dev/null \
  | python3 -c "import sys,json
chunks=sys.stdin.read().split(chr(10),1)
try:
  data=(json.loads(chunks[1]).get('data') or [])
  print(data[0]['id'] if data else '')
except Exception: print('')")
if [ -z "$APP_ID" ]; then
  cat <<'MISSING'
FAIL  No App Store Connect app record exists for this bundle id.
      The API CANNOT create one:
        POST /v1/apps -> 403 "The resource 'apps' does not allow 'CREATE'."
      Until the record exists, altool reports
        "Cannot determine the Apple ID from Bundle ID ... (19)"
      which reads like a signing failure and is routinely misdiagnosed as one.

      HUMAN STEP (web UI, ~1 minute):
        appstoreconnect.com -> Apps -> + -> New App
        Platform iOS · Name <product name> · Primary Language <language>
        Bundle ID <this bundle> · SKU <unique sku> · User Access Full Access

      Re-run this script with the SAME ipa once the record exists.
MISSING
  exit 3
fi
echo "PASS  app id = $APP_ID"

stage "1) validate"
cd "$WORK" || exit 2
if xcrun altool --validate-app -f "$IPA" -t ios --apiKey "$KEY_ID" --apiIssuer "$ASC_ISSUER" 2>&1 \
   | tee "$WORK/validate.log" | grep -qE "No errors validating"; then
  echo "PASS  validation clean"
else
  echo "FAIL  validation failed - raw output:"; grep -iE "error" "$WORK/validate.log" | sort -u | head -8; exit 4
fi

stage "2) upload"
if xcrun altool --upload-app -f "$IPA" -t ios --apiKey "$KEY_ID" --apiIssuer "$ASC_ISSUER" 2>&1 \
   | tee "$WORK/upload.log" | grep -qE "No errors uploading|UPLOAD SUCCEEDED"; then
  echo "PASS  upload accepted (this is NOT 'VALID' - Apple processing is a separate state)"
else
  echo "FAIL  upload failed - raw output:"; grep -iE "error" "$WORK/upload.log" | sort -u | head -8; exit 5
fi
cd "$HERE" || exit 2

stage "3) Apple processing (bounded poll: at most 30 x 30s = 15 min)"
STATE=""; BUILD_ID=""
for i in $(seq 1 30); do
  OUT=$(api GET "/v1/builds?filter%5Bapp%5D=$APP_ID&filter%5BpreReleaseVersion.version%5D=$BUILD&limit=5&fields%5Bbuilds%5D=version,processingState" 2>/dev/null \
    | tail -n +2 | python3 -c "import sys,json
try:
  data=(json.load(sys.stdin).get('data') or [])
  print((data[0]['id']+' '+data[0]['attributes'].get('processingState','?')) if data else ' ')
except Exception: print(' ')")
  BUILD_ID=$(echo "$OUT" | awk '{print $1}'); STATE=$(echo "$OUT" | awk '{print $2}')
  echo "  poll $i/30: build=${BUILD_ID:-none} state=${STATE:-none}"
  [ "$STATE" = "VALID" ] && break
  [ "$STATE" = "INVALID" ] && { echo "FAIL  processingState=INVALID - classify and fix; NO blind retry"; exit 6; }
  sleep 30
done
[ "$STATE" = "VALID" ] || { echo "FAIL  not VALID within 15 min (last: ${STATE:-none}) - NOT_VERIFIED, no re-upload"; exit 6; }
echo "PASS  processingState = VALID · build id = $BUILD_ID"

stage "4) export-compliance flag (409 is harmless if the toolchain already set it)"
api PATCH "/v1/builds/$BUILD_ID" "{\"data\":{\"type\":\"builds\",\"id\":\"$BUILD_ID\",\"attributes\":{\"usesNonExemptEncryption\":false}}}" 2>/dev/null | head -3

stage "5) internal beta group (internal groups skip Apple beta review)"
GID=$(api GET "/v1/apps/$APP_ID/betaGroups?limit=20&fields%5BbetaGroups%5D=name,isInternalGroup" 2>/dev/null | tail -n +2 \
  | python3 -c "import sys,json
try:
  for d in (json.load(sys.stdin).get('data') or []):
    if d['attributes'].get('isInternalGroup'): print(d['id']); break
except Exception: pass")
if [ -z "$GID" ]; then
  GROUP_NAME="${BETA_GROUP_NAME:-$BUNDLE internal}"
  GID=$(api POST "/v1/betaGroups" "{\"data\":{\"type\":\"betaGroups\",\"attributes\":{\"name\":\"$GROUP_NAME\",\"isInternalGroup\":true},\"relationships\":{\"app\":{\"data\":{\"type\":\"apps\",\"id\":\"$APP_ID\"}}}}}" 2>/dev/null | tail -n +2 \
    | python3 -c "import sys,json
try: print(json.load(sys.stdin)['data']['id'])
except Exception: print('')")
  [ -n "$GID" ] && echo "PASS  internal group created: $GID" || { echo "FAIL  could not create internal group"; exit 7; }
else
  echo "PASS  reusing existing internal group: $GID"
fi

stage "6) assign build to the group"
api POST "/v1/betaGroups/$GID/relationships/builds" "{\"data\":[{\"type\":\"builds\",\"id\":\"$BUILD_ID\"}]}" >/dev/null 2>&1
# The reverse read (/builds/<id>/betaGroups) lags; verify from the GROUP's own build list.
LINKED=$(api GET "/v1/betaGroups/$GID/builds?limit=20&fields%5Bbuilds%5D=version" 2>/dev/null | grep -c "\"$BUILD_ID\"")
[ "${LINKED:-0}" -ge 1 ] && echo "PASS  build visible in the group" || { echo "FAIL  build NOT visible in the group"; exit 8; }

stage "7) tester - identity is READ, never guessed"
WHO=$(api GET "/v1/users?limit=50&fields%5Busers%5D=username,firstName,lastName,roles" 2>/dev/null | tail -n +2 \
  | python3 -c "import sys,json
try:
  for d in (json.load(sys.stdin).get('data') or []):
    a=d['attributes']
    if 'ACCOUNT_HOLDER' in (a.get('roles') or []):
      print(a.get('username',''), (a.get('firstName') or 'Account'), (a.get('lastName') or 'Holder')); break
except Exception: pass")
EMAIL=$(echo "$WHO" | awk '{print $1}'); FIRST=$(echo "$WHO" | awk '{print $2}'); LAST=$(echo "$WHO" | awk '{print $3}')
if [ -z "$EMAIL" ]; then
  echo "FAIL  no ACCOUNT_HOLDER found in /v1/users - tester NOT added (nothing was guessed)"; exit 9
fi
echo "PASS  tester identity read: $(echo "$EMAIL" | sed 's/\(...\).*@/\1***@/') ($FIRST $LAST, ACCOUNT_HOLDER)"
PRESENT=$(api GET "/v1/betaGroups/$GID/betaTesters?limit=50&fields%5BbetaTesters%5D=email" 2>/dev/null | grep -c "$EMAIL")
if [ "${PRESENT:-0}" -ge 1 ]; then
  echo "PASS  tester already in the group"
else
  api POST "/v1/betaTesters" "{\"data\":{\"type\":\"betaTesters\",\"attributes\":{\"email\":\"$EMAIL\",\"firstName\":\"$FIRST\",\"lastName\":\"$LAST\"},\"relationships\":{\"betaGroups\":{\"data\":[{\"type\":\"betaGroups\",\"id\":\"$GID\"}]}}}}" >/dev/null 2>&1
  CONFIRM=$(api GET "/v1/betaGroups/$GID/betaTesters?limit=50&fields%5BbetaTesters%5D=email" 2>/dev/null | grep -c "$EMAIL")
  [ "${CONFIRM:-0}" -ge 1 ] && echo "PASS  tester added and CONFIRMED BY READING BACK" \
    || { echo "FAIL  tester not added (read-back found nothing)"; exit 9; }
fi

stage "8) final verification - re-read the group's build list"
api GET "/v1/betaGroups/$GID/builds?limit=20&fields%5Bbuilds%5D=version,processingState" 2>/dev/null | tail -n +2 | head -40
echo ""
echo "NOT DONE BY THIS SCRIPT: installing from TestFlight onto a device."
echo "Internal groups have no public join link - do not invent one."
