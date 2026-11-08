#!/usr/bin/env bash
# 0-references.sh — Reference asset upload pre-stage
#
# Adopted from Sean Claude's UGC pipeline (https://theseanclaude.substack.com/p/how-i-turned-claude-code-into-a-full).
# Their insight: upload character.png + product.png to a CDN BEFORE generation,
# then inject the URLs as image_urls into NanoBanana / Kling prompts. This gives
# brand-locked face + product consistency across all 18 hero frames vs text-only descriptions.
#
# Reads from the brand's reference dirs (under $FUTRGROUP_BRAND_HOME):
#   $FUTRGROUP_BRAND_HOME/<brand>/references/character/*.{png,jpg,jpeg,webp}
#   $FUTRGROUP_BRAND_HOME/<brand>/references/product/*.{png,jpg,jpeg,webp}
#   $FUTRGROUP_BRAND_HOME/<brand>/characters/*                      (alt path)
#   $FUTRGROUP_BRAND_HOME/<brand>/assets/logo/*.png                 (logo path)
# Plus optional --character-dir / --product-dir overrides.
# Default $FUTRGROUP_BRAND_HOME = $HOME/.futrgroup/brands
#
# Uploads via _fal-kling.sh's upload chain (fal_client → catbox.moe → uguu.se).
#
# Writes:
#   workdir/0-references/refs.json   (URLs by category)
#   workdir/0-references/manifest.md (human-readable summary)

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Capture --character-dir / --product-dir BEFORE _args.sh consumes them.
# _args.sh's catch-all *) shift would otherwise eat these.
CHARACTER_DIR="" PRODUCT_DIR=""
ORIG_ARGS=("$@")
FILTERED_ARGS=()
i=0
while [ $i -lt ${#ORIG_ARGS[@]} ]; do
  arg="${ORIG_ARGS[$i]}"
  case "$arg" in
    --character-dir)  CHARACTER_DIR="${ORIG_ARGS[$((i+1))]}"; i=$((i+2)) ;;
    --product-dir)    PRODUCT_DIR="${ORIG_ARGS[$((i+1))]}";   i=$((i+2)) ;;
    *)                FILTERED_ARGS+=("$arg"); i=$((i+1)) ;;
  esac
done
set -- "${FILTERED_ARGS[@]:-}"
. "$SD/_args.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
[ -z "$BRAND" ]   && { echo "missing --brand" >&2; exit 1; }
OUT="$WORKDIR/0-references"
mkdir -p "$OUT"

FUTRGROUP_BRAND_HOME="${FUTRGROUP_BRAND_HOME:-$HOME/.futrgroup/brands}"

# Discover reference dirs (best-effort, take first match)
discover_dir() {
  local kind="$1" candidate
  for candidate in \
    "$FUTRGROUP_BRAND_HOME/$BRAND/references/$kind" \
    "$FUTRGROUP_BRAND_HOME/$BRAND/${kind}s" \
    "$FUTRGROUP_BRAND_HOME/$BRAND/$kind"; do
    if [ -d "$candidate" ]; then echo "$candidate"; return 0; fi
  done
  return 1
}

[ -z "$CHARACTER_DIR" ] && CHARACTER_DIR=$(discover_dir character || true)
[ -z "$PRODUCT_DIR" ]   && PRODUCT_DIR=$(discover_dir product || true)

echo "[0-references] character_dir: ${CHARACTER_DIR:-<none>}"
echo "[0-references] product_dir:   ${PRODUCT_DIR:-<none>}"

# Source the upload helper from _fal-kling.sh (refactor-target candidate later)
FK="$SD/_fal-kling.sh"
if [ ! -x "$FK" ]; then
  echo "[0-references] _fal-kling.sh not found at $FK" >&2
  exit 1
fi

# Inline minimal upload (mirrors the cascade in _fal-kling.sh)
upload_one() {
  local file="$1" url=""
  url=$(python3 -c "
import os, sys
key = os.environ.get('FAL_API_KEY') or os.environ.get('FAL_KEY','')
os.environ['FAL_KEY']=key
try:
    import fal_client
    print(fal_client.upload_file(sys.argv[1]))
except Exception:
    pass
" "$file" 2>/dev/null)
  if [ -n "$url" ] && [[ "$url" =~ ^https?:// ]]; then echo "$url"; return 0; fi

  url=$(curl -sS --max-time 30 -F "reqtype=fileupload" -F "fileToUpload=@$file" \
    https://catbox.moe/user/api.php 2>/dev/null)
  if [ -n "$url" ] && [[ "$url" =~ ^https?:// ]]; then echo "$url"; return 0; fi

  url=$(curl -sS --max-time 30 -F "files[]=@$file" https://uguu.se/upload 2>/dev/null | \
    python3 -c "import json,sys; d=json.load(sys.stdin); print(d['files'][0]['url'])" 2>/dev/null)
  if [ -n "$url" ] && [[ "$url" =~ ^https?:// ]]; then echo "$url"; return 0; fi

  return 1
}

# FAL_API_KEY expected from caller env (no auto-source from external paths)
if [ -z "${FAL_API_KEY:-}" ]; then
  echo "[0-references] WARNING: FAL_API_KEY not set — fal_client upload will be skipped, only catbox/uguu fallbacks will fire" >&2
fi

# Upload up to 3 character + 3 product references (avoid spamming CDN on huge dirs)
character_urls="[]"
product_urls="[]"

upload_dir_to_array() {
  local dir="$1" max="${2:-3}"
  local urls=()
  if [ -d "$dir" ]; then
    local i=0
    for f in "$dir"/*.{png,jpg,jpeg,webp}; do
      [ -f "$f" ] || continue
      [ $i -ge "$max" ] && break
      url=$(upload_one "$f")
      if [ -n "$url" ]; then
        urls+=("$url")
        echo "  ✓ $(basename "$f") → $url" >&2
        i=$((i+1))
      else
        echo "  ✗ $(basename "$f") upload failed" >&2
      fi
    done
  fi
  if [ ${#urls[@]} -eq 0 ]; then
    echo '[]'
  else
    printf '%s\n' "${urls[@]}" | jq -R . | jq -s .
  fi
}

if [ -n "$CHARACTER_DIR" ]; then
  echo "[0-references] uploading character refs..."
  character_urls=$(upload_dir_to_array "$CHARACTER_DIR" 3)
fi
if [ -n "$PRODUCT_DIR" ]; then
  echo "[0-references] uploading product refs..."
  product_urls=$(upload_dir_to_array "$PRODUCT_DIR" 3)
fi

# Write refs.json
jq -n --argjson c "$character_urls" --argjson p "$product_urls" \
      --arg brand "$BRAND" --arg t "$(date -u +%FT%TZ)" \
  '{brand: $brand, generated_at: $t, character_urls: $c, product_urls: $p}' \
  > "$OUT/refs.json"

# Manifest for humans
cat > "$OUT/manifest.md" <<EOF
# References — $BRAND ($(date +%F))

## Character refs ($(echo "$character_urls" | jq 'length'))
$(echo "$character_urls" | jq -r '.[] | "- \(.)"')

## Product refs ($(echo "$product_urls" | jq 'length'))
$(echo "$product_urls" | jq -r '.[] | "- \(.)"')

## How downstream stages use this
- Stage 3 (3-frames.sh): inject \`character_urls[0]\` as NanoBanana \`reference_image\` for face consistency
- Stage 4 (4-animate.sh): inject \`product_urls[0]\` as Kling \`image_url\` for product placement
- Future: train Higgsfield Soul ID from 3+ character refs (\$3 one-time)
EOF

C_COUNT=$(echo "$character_urls" | jq 'length')
P_COUNT=$(echo "$product_urls" | jq 'length')
echo "[0-references] OK → $OUT/"
echo "  character: $C_COUNT URLs"
echo "  product:   $P_COUNT URLs"
exit 0
