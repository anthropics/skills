#!/usr/bin/env bash
# Sweep a list of URLs through both fetch methods and print a status matrix.
# Useful for periodically re-testing the site_gating.md snapshot.
#
# Usage:
#   site_test.sh url1 url2 ...
#   echo -e "https://a.com\nhttps://b.com" | site_test.sh -
set -euo pipefail

SKILL_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

if [ "${1:-}" = "-" ]; then
  mapfile -t URLS
else
  URLS=("$@")
fi

UA='Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15'

printf '%-60s  %-8s  %-8s\n' "URL" "default" "browser-UA"
printf '%-60s  %-8s  %-8s\n' "---" "-------" "----------"

for url in "${URLS[@]}"; do
  default_code=$(curl -sLI --max-time 10 -o /dev/null -w '%{http_code}' "$url" 2>&1 || echo "ERR")
  ua_code=$(curl -sLI --max-time 10 -A "$UA" -o /dev/null -w '%{http_code}' "$url" 2>&1 || echo "ERR")
  printf '%-60s  %-8s  %-8s\n' "${url:0:60}" "$default_code" "$ua_code"
done
