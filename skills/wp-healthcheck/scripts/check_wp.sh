#!/usr/bin/env bash
# check_wp.sh — WordPress site healthcheck (external / public-information only).
#
# 使い方:
#   bash scripts/check_wp.sh <url> [--output <file>]
#
# 例:
#   bash scripts/check_wp.sh https://n-pc.jp
#   bash scripts/check_wp.sh https://example.com --output /tmp/report.md
#
# 依存: bash, curl, jq, awk, sed, grep, mktemp, date

set -euo pipefail

# ------------------------------------------------------------
# 引数パース
# ------------------------------------------------------------
URL=""
OUTPUT=""

while [ $# -gt 0 ]; do
  case "$1" in
    --output)
      OUTPUT="${2:-}"
      shift 2
      ;;
    --help|-h)
      sed -n '1,15p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    http://*|https://*)
      URL="$1"
      shift
      ;;
    *)
      echo "Error: unknown argument or invalid URL: $1" >&2
      echo "URL must start with http:// or https://" >&2
      exit 2
      ;;
  esac
done

if [ -z "$URL" ]; then
  echo "Usage: $0 <url> [--output <file>]" >&2
  exit 2
fi

# 末尾スラッシュ正規化
URL="${URL%/}"

# ------------------------------------------------------------
# 依存チェック
# ------------------------------------------------------------
for cmd in curl jq awk sed grep mktemp date; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "Error: required command '$cmd' is not installed." >&2
    exit 1
  fi
done

# ------------------------------------------------------------
# 作業ディレクトリ準備（trap で必ず削除）
# ------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
WORK_DIR="$(mktemp -d -t wp-healthcheck.XXXXXX)"
trap 'rm -rf "$WORK_DIR"' EXIT

# ------------------------------------------------------------
# 公開メタデータ取得
# ------------------------------------------------------------
bash "$SCRIPT_DIR/fetch_wp_meta.sh" "$URL" "$WORK_DIR"

# ------------------------------------------------------------
# 解析ユーティリティ
# ------------------------------------------------------------

# findings.tsv に1行追加
add_finding() {
  # $1 key, $2 status, $3 summary, $4 detail(pipe-separated)
  printf '%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "${4:-}" >> "$WORK_DIR/findings.tsv"
}

# HTML本文存在チェック
HTML="$WORK_DIR/index.html"
HEADERS="$WORK_DIR/index.headers"

if [ ! -s "$HTML" ]; then
  add_finding "wp_version"     "UNKNOWN" "Top page could not be fetched." ""
  add_finding "theme"          "UNKNOWN" "Top page could not be fetched." ""
  add_finding "ssl_cert"       "UNKNOWN" "Site unreachable; TLS not evaluated." ""
  add_finding "sec_headers"    "UNKNOWN" "No headers received." ""
  add_finding "robots_sitemap" "UNKNOWN" "Site unreachable." ""
  add_finding "response_time"  "UNKNOWN" "Site unreachable." ""
  add_finding "api_surface"    "UNKNOWN" "Site unreachable." ""
  add_finding "plugins"        "UNKNOWN" "Site unreachable." ""
  bash "$SCRIPT_DIR/format_report.sh" "$WORK_DIR" "$URL" > "${OUTPUT:-/dev/stdout}"
  if [ -n "$OUTPUT" ]; then
    echo "Report written to: $OUTPUT" >&2
  fi
  exit 0
fi

# ------------------------------------------------------------
# 1. WordPress version
# ------------------------------------------------------------
WP_VERSION=""
WP_VERSION=$(grep -Eio '<meta[^>]*name=["'"'"']generator["'"'"'][^>]*content=["'"'"']WordPress[^"'"'"']*' "$HTML" \
  | head -1 \
  | sed -E 's/.*WordPress[[:space:]]+([0-9][0-9.]*).*/\1/' \
  | head -1 || true)

README_STATUS=$(cat "$WORK_DIR/readme.status" 2>/dev/null || echo "000")
WPJSON_STATUS=$(cat "$WORK_DIR/wpjson.status" 2>/dev/null || echo "000")

WPJSON_NAME=""
if [ "$WPJSON_STATUS" = "200" ] && [ -s "$WORK_DIR/wpjson.body" ]; then
  WPJSON_NAME=$(jq -r '.name // empty' "$WORK_DIR/wpjson.body" 2>/dev/null || echo "")
fi

# 判定
WP_DETAIL=""
if [ -n "$WP_VERSION" ]; then
  MAJOR=$(echo "$WP_VERSION" | cut -d. -f1)
  MINOR=$(echo "$WP_VERSION" | cut -d. -f2)
  WP_DETAIL="Detected version: ${WP_VERSION}"
  if [ "$README_STATUS" = "200" ]; then
    WP_DETAIL="${WP_DETAIL}|/readme.html is publicly accessible (status 200) — typical of long-unmaintained installs."
    WP_STATUS="CRITICAL"
    WP_SUMMARY="WordPress ${WP_VERSION} detected; /readme.html is exposed."
  elif [ "$MAJOR" -lt 6 ] 2>/dev/null; then
    WP_STATUS="CRITICAL"
    WP_SUMMARY="WordPress ${WP_VERSION} is significantly outdated (< 6.0)."
  elif [ "$MAJOR" -eq 6 ] && [ "$MINOR" -lt 4 ] 2>/dev/null; then
    WP_STATUS="WARNING"
    WP_SUMMARY="WordPress ${WP_VERSION} is older than the recent stable line (>= 6.4)."
  else
    WP_STATUS="OK"
    WP_SUMMARY="WordPress ${WP_VERSION} appears reasonably current."
  fi
else
  WP_DETAIL="generator meta absent or stripped"
  if [ "$README_STATUS" = "200" ]; then
    WP_STATUS="WARNING"
    WP_SUMMARY="Version not detected, but /readme.html is publicly accessible."
    WP_DETAIL="${WP_DETAIL}|/readme.html status: 200"
  elif [ "$WPJSON_STATUS" = "200" ] && [ -n "$WPJSON_NAME" ]; then
    WP_STATUS="UNKNOWN"
    WP_SUMMARY="Version unknown; REST API confirms WordPress (site name: ${WPJSON_NAME})."
    WP_DETAIL="${WP_DETAIL}|/wp-json/ name: ${WPJSON_NAME}"
  else
    WP_STATUS="UNKNOWN"
    WP_SUMMARY="No WordPress fingerprint detected on the front page."
  fi
fi
add_finding "wp_version" "$WP_STATUS" "$WP_SUMMARY" "$WP_DETAIL"

# ------------------------------------------------------------
# 2. Active theme
# ------------------------------------------------------------
THEME=$(grep -Eo '/wp-content/themes/[a-zA-Z0-9_-]+/' "$HTML" \
  | head -1 \
  | sed -E 's|/wp-content/themes/([^/]+)/|\1|' || true)

if [ -n "$THEME" ]; then
  add_finding "theme" "OK" "Active theme: ${THEME}" "Theme path detected from HTML."
else
  add_finding "theme" "UNKNOWN" "Theme could not be detected from HTML." "Possible causes: full-page caching strips theme paths, or non-WordPress site."
fi

# ------------------------------------------------------------
# 3. SSL / TLS
# ------------------------------------------------------------
SSL_VERBOSE="$WORK_DIR/ssl.verbose"
SSL_STATUS="UNKNOWN"
SSL_SUMMARY="HTTPS not used or certificate not parsed."
SSL_DETAIL=""

case "$URL" in
  https://*)
    if [ -s "$SSL_VERBOSE" ]; then
      ISSUER=$(grep -E 'issuer:' "$SSL_VERBOSE" | head -1 | sed -E 's/.*issuer:[[:space:]]*//' || true)
      EXPIRE_LINE=$(grep -E 'expire date:' "$SSL_VERBOSE" | head -1 | sed -E 's/.*expire date:[[:space:]]*//' || true)
      START_LINE=$(grep -E 'start date:' "$SSL_VERBOSE" | head -1 | sed -E 's/.*start date:[[:space:]]*//' || true)
      SUBJECT=$(grep -E 'subject:' "$SSL_VERBOSE" | head -1 | sed -E 's/.*subject:[[:space:]]*//' || true)
      VERIFY_OK=$(grep -E 'SSL certificate verify ok' "$SSL_VERBOSE" || true)

      if [ -n "$EXPIRE_LINE" ]; then
        # 例: "Jul  5 23:29:05 2026 GMT" を "2026-07-05 23:29:05" に整形してから epoch化
        # macOS の date -j は %Z や 1桁日のパースが弱いので前段で正規化する
        EXPIRE_EPOCH=""
        # GNU date が使える環境なら一発で済ませる
        if date -d "$EXPIRE_LINE" '+%s' >/dev/null 2>&1; then
          EXPIRE_EPOCH=$(date -d "$EXPIRE_LINE" '+%s')
        else
          # macOS BSD date 用の正規化: "Mon  D HH:MM:SS YYYY ZZZ" → "YYYY-MM-DD HH:MM:SS"
          NORM=$(echo "$EXPIRE_LINE" | tr -s ' ')
          MON_NAME=$(echo "$NORM" | awk '{print $1}')
          DAY=$(echo "$NORM" | awk '{print $2}')
          TIME_PART=$(echo "$NORM" | awk '{print $3}')
          YEAR=$(echo "$NORM" | awk '{print $4}')
          MON_NUM=""
          case "$MON_NAME" in
            Jan) MON_NUM="01" ;; Feb) MON_NUM="02" ;; Mar) MON_NUM="03" ;;
            Apr) MON_NUM="04" ;; May) MON_NUM="05" ;; Jun) MON_NUM="06" ;;
            Jul) MON_NUM="07" ;; Aug) MON_NUM="08" ;; Sep) MON_NUM="09" ;;
            Oct) MON_NUM="10" ;; Nov) MON_NUM="11" ;; Dec) MON_NUM="12" ;;
          esac
          if [ -n "$MON_NUM" ] && [ -n "$DAY" ] && [ -n "$YEAR" ] && [ -n "$TIME_PART" ]; then
            # 2桁ゼロパディング
            DAY_PAD=$(printf '%02d' "$DAY" 2>/dev/null || echo "$DAY")
            ISO="${YEAR}-${MON_NUM}-${DAY_PAD} ${TIME_PART}"
            # 証明書時刻はUTCなので TZ=UTC で評価
            if EPOCH_TRY=$(TZ=UTC date -j -f '%Y-%m-%d %H:%M:%S' "$ISO" '+%s' 2>/dev/null); then
              EXPIRE_EPOCH="$EPOCH_TRY"
            fi
          fi
        fi

        NOW_EPOCH=$(date '+%s')
        if [ -n "$EXPIRE_EPOCH" ]; then
          DAYS_LEFT=$(( (EXPIRE_EPOCH - NOW_EPOCH) / 86400 ))
          if [ "$DAYS_LEFT" -lt 0 ]; then
            SSL_STATUS="CRITICAL"
            SSL_SUMMARY="Certificate has expired (${DAYS_LEFT} days)."
          elif [ "$DAYS_LEFT" -lt 30 ]; then
            SSL_STATUS="WARNING"
            SSL_SUMMARY="Certificate expires in ${DAYS_LEFT} days."
          else
            SSL_STATUS="OK"
            SSL_SUMMARY="Certificate valid for ${DAYS_LEFT} more days."
          fi
          SSL_DETAIL="Subject: ${SUBJECT}|Issuer: ${ISSUER}|Valid from: ${START_LINE}|Expires: ${EXPIRE_LINE}|Days remaining: ${DAYS_LEFT}"
        else
          SSL_STATUS="UNKNOWN"
          SSL_SUMMARY="Could not parse certificate expiry date."
          SSL_DETAIL="Raw expire date string: ${EXPIRE_LINE}"
        fi
      fi

      if [ -z "$VERIFY_OK" ] && [ "$SSL_STATUS" != "CRITICAL" ]; then
        # verify ok 行が無く、かつ critical でないなら警告
        if grep -qE 'self.signed|certificate verify failed|hostname.*does not match' "$SSL_VERBOSE"; then
          SSL_STATUS="CRITICAL"
          SSL_SUMMARY="Certificate verification failed."
        fi
      fi
    fi
    ;;
  *)
    SSL_STATUS="CRITICAL"
    SSL_SUMMARY="Site is served over plain HTTP."
    SSL_DETAIL="HTTPS is required for modern WordPress sites (SEO, login security, browser warnings)."
    ;;
esac

add_finding "ssl_cert" "$SSL_STATUS" "$SSL_SUMMARY" "$SSL_DETAIL"

# ------------------------------------------------------------
# 4. Security headers
# ------------------------------------------------------------
header_present() {
  # ヘッダ名（大小無視）が存在するか
  grep -iE "^${1}:" "$HEADERS" >/dev/null 2>&1
}

PRESENT_HEADERS=""
MISSING_HEADERS=""
COUNT_PRESENT=0

for h in "X-Frame-Options" "X-Content-Type-Options" "Strict-Transport-Security" "Content-Security-Policy" "Referrer-Policy"; do
  if header_present "$h"; then
    PRESENT_HEADERS="${PRESENT_HEADERS}${h} "
    COUNT_PRESENT=$((COUNT_PRESENT + 1))
  else
    MISSING_HEADERS="${MISSING_HEADERS}${h} "
  fi
done

if [ "$COUNT_PRESENT" -ge 4 ]; then
  SEC_STATUS="OK"
elif [ "$COUNT_PRESENT" -ge 2 ]; then
  SEC_STATUS="WARNING"
else
  SEC_STATUS="CRITICAL"
fi

SEC_SUMMARY="${COUNT_PRESENT} of 5 recommended security headers present."
SEC_DETAIL="Present: ${PRESENT_HEADERS:-none}|Missing: ${MISSING_HEADERS:-none}"
add_finding "sec_headers" "$SEC_STATUS" "$SEC_SUMMARY" "$SEC_DETAIL"

# ------------------------------------------------------------
# 5. robots.txt and sitemap
# ------------------------------------------------------------
ROBOTS_STATUS=$(cat "$WORK_DIR/robots.status" 2>/dev/null || echo "000")
SITEMAP_STATUS=$(cat "$WORK_DIR/sitemap.status" 2>/dev/null || echo "000")
SITEMAP_URL=$(cat "$WORK_DIR/sitemap.url" 2>/dev/null || echo "")

ROBOTS_OK=0
SITEMAP_OK=0

[ "$ROBOTS_STATUS" = "200" ] && [ -s "$WORK_DIR/robots.body" ] && ROBOTS_OK=1
[ "$SITEMAP_STATUS" = "200" ] && SITEMAP_OK=1

if [ "$ROBOTS_OK" = "1" ] && [ "$SITEMAP_OK" = "1" ]; then
  RS_STATUS="OK"
  RS_SUMMARY="Both robots.txt and sitemap are present."
elif [ "$ROBOTS_OK" = "1" ] || [ "$SITEMAP_OK" = "1" ]; then
  RS_STATUS="WARNING"
  RS_SUMMARY="One of robots.txt / sitemap is missing or unreachable."
else
  RS_STATUS="CRITICAL"
  RS_SUMMARY="Neither robots.txt nor sitemap is reachable."
fi

RS_DETAIL="robots.txt status: ${ROBOTS_STATUS}|sitemap URL tried: ${SITEMAP_URL}|sitemap status: ${SITEMAP_STATUS}"
add_finding "robots_sitemap" "$RS_STATUS" "$RS_SUMMARY" "$RS_DETAIL"

# ------------------------------------------------------------
# 6. Response time
# ------------------------------------------------------------
TIME_TOTAL=$(cat "$WORK_DIR/time_total" 2>/dev/null || echo "0")
# 小数比較は awk で
TIME_STATUS=$(awk -v t="$TIME_TOTAL" 'BEGIN {
  if (t+0 == 0) print "UNKNOWN";
  else if (t+0 < 1.5) print "OK";
  else if (t+0 < 3.0) print "WARNING";
  else print "CRITICAL";
}')
TIME_SUMMARY="Top page time_total: ${TIME_TOTAL}s"
add_finding "response_time" "$TIME_STATUS" "$TIME_SUMMARY" "Single-sample measurement; treat as indicative only."

# ------------------------------------------------------------
# 7. Public API surface
# ------------------------------------------------------------
XMLRPC_STATUS=$(cat "$WORK_DIR/xmlrpc.status" 2>/dev/null || echo "000")
WPCRON_STATUS=$(cat "$WORK_DIR/wpcron.status" 2>/dev/null || echo "000")

# xmlrpc 判定
case "$XMLRPC_STATUS" in
  403|404|410)  XMLRPC_VERDICT="OK (disabled, status ${XMLRPC_STATUS})"; XMLRPC_LEVEL=0 ;;
  405)          XMLRPC_VERDICT="WARNING (default WordPress, GET returns 405)"; XMLRPC_LEVEL=1 ;;
  200)          XMLRPC_VERDICT="CRITICAL (xmlrpc.php served on GET — verify it is intentional)"; XMLRPC_LEVEL=2 ;;
  *)            XMLRPC_VERDICT="UNKNOWN (status ${XMLRPC_STATUS})"; XMLRPC_LEVEL=-1 ;;
esac

# wp-json 判定
case "$WPJSON_STATUS" in
  200) WPJSON_VERDICT="OK (REST API reachable)"; WPJSON_LEVEL=0 ;;
  401|403) WPJSON_VERDICT="OK (REST API restricted, status ${WPJSON_STATUS})"; WPJSON_LEVEL=0 ;;
  404) WPJSON_VERDICT="WARNING (REST API not found)"; WPJSON_LEVEL=1 ;;
  5*) WPJSON_VERDICT="CRITICAL (REST API server error, status ${WPJSON_STATUS})"; WPJSON_LEVEL=2 ;;
  *) WPJSON_VERDICT="UNKNOWN (status ${WPJSON_STATUS})"; WPJSON_LEVEL=-1 ;;
esac

# wp-cron 判定
case "$WPCRON_STATUS" in
  200|404) WPCRON_VERDICT="OK (status ${WPCRON_STATUS})"; WPCRON_LEVEL=0 ;;
  5*) WPCRON_VERDICT="WARNING (server error, status ${WPCRON_STATUS})"; WPCRON_LEVEL=1 ;;
  000) WPCRON_VERDICT="CRITICAL (timeout)"; WPCRON_LEVEL=2 ;;
  *) WPCRON_VERDICT="OK (status ${WPCRON_STATUS})"; WPCRON_LEVEL=0 ;;
esac

# 最大レベルで集約
MAX_LEVEL=$XMLRPC_LEVEL
[ "$WPJSON_LEVEL" -gt "$MAX_LEVEL" ] && MAX_LEVEL=$WPJSON_LEVEL
[ "$WPCRON_LEVEL" -gt "$MAX_LEVEL" ] && MAX_LEVEL=$WPCRON_LEVEL

case "$MAX_LEVEL" in
  2)  API_STATUS="CRITICAL" ;;
  1)  API_STATUS="WARNING" ;;
  0)  API_STATUS="OK" ;;
  *)  API_STATUS="UNKNOWN" ;;
esac

API_SUMMARY="xmlrpc / wp-json / wp-cron probed."
API_DETAIL="xmlrpc.php: ${XMLRPC_VERDICT}|/wp-json/: ${WPJSON_VERDICT}|wp-cron.php: ${WPCRON_VERDICT}"
add_finding "api_surface" "$API_STATUS" "$API_SUMMARY" "$API_DETAIL"

# ------------------------------------------------------------
# 8. Plugin fingerprints + known-issue match
# ------------------------------------------------------------
# Limitation: detects only plugins that emit `/wp-content/plugins/<slug>/` paths
# in the front-end HTML. Plugins active only in the WordPress admin (SEO meta
# managers, caching plugins, backup plugins, security plugins, etc.) leave no
# fingerprint on the public site and cannot be detected from outside. Treat the
# resulting count as a lower bound, not a complete plugin inventory.
#
# HTML から plugin slug を全部抽出（重複排除）
PLUGIN_SLUGS=$(grep -Eo '/wp-content/plugins/[a-zA-Z0-9_-]+/' "$HTML" \
  | sed -E 's|/wp-content/plugins/([^/]+)/|\1|' \
  | sort -u || true)

# 既知脆弱性プラグインリスト（checklist.md に対応）
KNOWN_VULN="wp-file-manager revslider wp-statistics duplicator loginizer elementor all-in-one-seo-pack wpforms-lite contact-form-7 ninja-forms updraftplus wpbakery-page-builder mailpoet wp-super-cache social-warfare"

FOUND_VULN=""
DETECTED_LIST=""
PLUGIN_COUNT=0

if [ -n "$PLUGIN_SLUGS" ]; then
  while IFS= read -r slug; do
    [ -z "$slug" ] && continue
    PLUGIN_COUNT=$((PLUGIN_COUNT + 1))
    DETECTED_LIST="${DETECTED_LIST}${slug} "
    for vuln in $KNOWN_VULN; do
      if [ "$slug" = "$vuln" ]; then
        FOUND_VULN="${FOUND_VULN}${slug} "
      fi
    done
  done <<EOF
$PLUGIN_SLUGS
EOF
fi

PLUGIN_NOTE="Note: Plugins active only in the WordPress admin (SEO, cache, backup, security tools) typically leave no front-end fingerprint and cannot be detected from outside."

if [ "$PLUGIN_COUNT" -eq 0 ]; then
  PLUGIN_STATUS="UNKNOWN"
  PLUGIN_SUMMARY="No plugin paths detected in HTML."
  PLUGIN_DETAIL="Possible causes: full-page caching, plugins with no front-end assets, or non-WordPress site.|${PLUGIN_NOTE}"
elif [ -n "$FOUND_VULN" ]; then
  PLUGIN_STATUS="WARNING"
  PLUGIN_SUMMARY="Plugins with historical CVEs detected: ${FOUND_VULN}"
  PLUGIN_DETAIL="Front-end visible plugins (${PLUGIN_COUNT}): ${DETECTED_LIST}|${PLUGIN_NOTE}|Action: verify each flagged plugin is up to date. Versions cannot be determined externally."
else
  PLUGIN_STATUS="OK"
  PLUGIN_SUMMARY="${PLUGIN_COUNT} front-end visible plugin(s) detected; none on the known-issue list."
  PLUGIN_DETAIL="Front-end visible plugins (${PLUGIN_COUNT}): ${DETECTED_LIST}|${PLUGIN_NOTE}"
fi
add_finding "plugins" "$PLUGIN_STATUS" "$PLUGIN_SUMMARY" "$PLUGIN_DETAIL"

# ------------------------------------------------------------
# レポート出力
# ------------------------------------------------------------
if [ -n "$OUTPUT" ]; then
  bash "$SCRIPT_DIR/format_report.sh" "$WORK_DIR" "$URL" > "$OUTPUT"
  echo "Report written to: $OUTPUT" >&2
else
  bash "$SCRIPT_DIR/format_report.sh" "$WORK_DIR" "$URL"
fi
