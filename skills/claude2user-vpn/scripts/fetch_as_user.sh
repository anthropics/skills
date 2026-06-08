#!/usr/bin/env bash
# Fetch a URL with browser-equivalent HTTP headers from the user's local
# machine. Use when the agent's default fetch returns errors or empty content
# on a public URL that the user could open in their own browser.
#
# Usage:
#   fetch_as_user.sh <url> [output_path]
#
# Defaults to /tmp/fetch_<hash>.html if no output path given. Prints the path
# on success so callers can pipe it through pup/jq/BeautifulSoup/etc.
set -euo pipefail

URL="${1:?usage: fetch_as_user.sh <url> [out]}"
OUT="${2:-/tmp/fetch_$(echo "$URL" | shasum -a 256 | cut -c1-12).html}"

UA='Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15'

curl -sL --max-time 20 --compressed \
  -A "$UA" \
  -H 'Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8' \
  -H 'Accept-Language: en-US,en;q=0.9' \
  -H 'sec-ch-ua: "Not_A Brand";v="8", "Chromium";v="120"' \
  -H 'sec-ch-ua-mobile: ?0' \
  -H 'sec-ch-ua-platform: "macOS"' \
  -H 'sec-fetch-dest: document' \
  -H 'sec-fetch-mode: navigate' \
  -H 'sec-fetch-site: none' \
  -H 'sec-fetch-user: ?1' \
  -H 'upgrade-insecure-requests: 1' \
  -o "$OUT" \
  -w 'HTTP %{http_code}  size=%{size_download}  url=%{url_effective}\n' \
  "$URL" >&2

if [ ! -s "$OUT" ]; then
  echo "ERROR: empty response" >&2
  exit 1
fi
echo "$OUT"
