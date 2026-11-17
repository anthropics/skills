#!/usr/bin/env bash
# fetch_wp_meta.sh — fetch WordPress public metadata for a given site.
# 使い方: fetch_wp_meta.sh <base_url> <work_dir>
#
# 取得物（work_dir 配下に保存）:
#   index.html       トップページのHTML
#   index.headers    トップページのレスポンスヘッダ
#   readme.status    /readme.html のHTTPステータス
#   wpjson.body      /wp-json/ のレスポンスボディ
#   wpjson.status    /wp-json/ のHTTPステータス
#   xmlrpc.status    /xmlrpc.php のHTTPステータス
#   wpcron.status    /wp-cron.php のHTTPステータス
#   robots.body      /robots.txt のレスポンスボディ
#   robots.status    /robots.txt のHTTPステータス
#   sitemap.status   /sitemap.xml or /wp-sitemap.xml のHTTPステータス
#   sitemap.url      実際に200を返したサイトマップURL
#   ssl.verbose      curl -vI の出力（証明書情報含む）
#   time_total       トップページの応答秒数

set -euo pipefail

BASE_URL="${1:-}"
WORK_DIR="${2:-}"

if [ -z "$BASE_URL" ] || [ -z "$WORK_DIR" ]; then
  echo "Usage: $0 <base_url> <work_dir>" >&2
  exit 2
fi

# 末尾スラッシュを削る（正規化）
BASE_URL="${BASE_URL%/}"

CURL_OPTS_COMMON="--silent --show-error --connect-timeout 10 --max-time 30 --location --user-agent wp-healthcheck-skill/0.1"

# 1. トップページ取得（HTML本文 + ヘッダ + 応答時間）
curl $CURL_OPTS_COMMON \
  -o "$WORK_DIR/index.html" \
  -D "$WORK_DIR/index.headers" \
  -w '%{time_total}' \
  "$BASE_URL/" > "$WORK_DIR/time_total" 2>"$WORK_DIR/index.error" || true

# 2. /readme.html ステータスのみ
curl $CURL_OPTS_COMMON \
  -o /dev/null \
  -w '%{http_code}' \
  -I "$BASE_URL/readme.html" > "$WORK_DIR/readme.status" 2>/dev/null || echo "000" > "$WORK_DIR/readme.status"

# 3. /wp-json/ 本文+ステータス
curl $CURL_OPTS_COMMON \
  -o "$WORK_DIR/wpjson.body" \
  -w '%{http_code}' \
  "$BASE_URL/wp-json/" > "$WORK_DIR/wpjson.status" 2>/dev/null || echo "000" > "$WORK_DIR/wpjson.status"

# 4. /xmlrpc.php ステータス（GETで判定）
curl $CURL_OPTS_COMMON \
  -o /dev/null \
  -w '%{http_code}' \
  "$BASE_URL/xmlrpc.php" > "$WORK_DIR/xmlrpc.status" 2>/dev/null || echo "000" > "$WORK_DIR/xmlrpc.status"

# 5. /wp-cron.php ステータス（HEADで判定）
curl $CURL_OPTS_COMMON \
  -o /dev/null \
  -w '%{http_code}' \
  -I "$BASE_URL/wp-cron.php" > "$WORK_DIR/wpcron.status" 2>/dev/null || echo "000" > "$WORK_DIR/wpcron.status"

# 6. robots.txt
curl $CURL_OPTS_COMMON \
  -o "$WORK_DIR/robots.body" \
  -w '%{http_code}' \
  "$BASE_URL/robots.txt" > "$WORK_DIR/robots.status" 2>/dev/null || echo "000" > "$WORK_DIR/robots.status"

# 7. sitemap（/sitemap.xml → だめなら /wp-sitemap.xml）
SITEMAP_URL="$BASE_URL/sitemap.xml"
SITEMAP_STATUS=$(curl $CURL_OPTS_COMMON -o /dev/null -w '%{http_code}' -I "$SITEMAP_URL" 2>/dev/null || echo "000")
if [ "$SITEMAP_STATUS" != "200" ]; then
  SITEMAP_URL="$BASE_URL/wp-sitemap.xml"
  SITEMAP_STATUS=$(curl $CURL_OPTS_COMMON -o /dev/null -w '%{http_code}' -I "$SITEMAP_URL" 2>/dev/null || echo "000")
fi
echo "$SITEMAP_STATUS" > "$WORK_DIR/sitemap.status"
echo "$SITEMAP_URL" > "$WORK_DIR/sitemap.url"

# 8. SSL/TLS情報（HTTPSの場合のみ意味がある。curl -vI で取得）
case "$BASE_URL" in
  https://*)
    # curl -vI は標準エラーに証明書情報を出すので 2>&1 でキャプチャ
    curl -vI --connect-timeout 10 --max-time 30 \
      --user-agent wp-healthcheck-skill/0.1 \
      "$BASE_URL/" > /dev/null 2> "$WORK_DIR/ssl.verbose" || true
    ;;
  *)
    : > "$WORK_DIR/ssl.verbose"
    ;;
esac

exit 0
