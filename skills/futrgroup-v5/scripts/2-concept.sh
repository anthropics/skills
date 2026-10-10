#!/usr/bin/env bash
# 2-concept.sh — Compose ad concept (uses marketing-studio-clone) + ChatGPT 18-prompt framework
# v0.2: live OpenAI Chat Completion call to populate concept.json
#
# Writes:
#   workdir/2-concept/composed-prefix.txt
#   workdir/2-concept/concept.json          (LIVE from OpenAI in v0.2; STUB if no key)
#   workdir/2-concept/voice-direction.txt
#   workdir/2-concept/suno-prompt.txt
#
# DEPS: marketing-studio-clone (optional sibling), OPENAI_API_KEY (env var)

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SD/_args.sh"
. "$SD/_siblings.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
OUT="$WORKDIR/2-concept"
mkdir -p "$OUT"

# Source preference: manual brief.md (Sean Claude pattern — human-authored creative direction)
# falls back to NotebookLM auto-extracted factset (default Zennith path)
MANUAL_BRIEF="$WORKDIR/0-brief/brief.md"
FACTSET="$WORKDIR/1-research/factset.md"

if [ -f "$MANUAL_BRIEF" ]; then
  echo "[2-concept] using MANUAL brief.md (overrides NotebookLM factset)"
  FACTSET="$MANUAL_BRIEF"
fi

[ -f "$FACTSET" ] || { echo "[2-concept] missing source: $MANUAL_BRIEF or factset.md" >&2; exit 1; }

PRODUCT_NAME="$(grep -m1 -E '^# ' "$FACTSET" | sed 's/^# *//; s/ *$//' || echo "$BRAND product")"

# ── Stage 2.1: marketing-studio-clone composition (optional sibling) ──
if [ -n "$FUTRGROUP_MSCLONE_SH" ] && [ -x "$FUTRGROUP_MSCLONE_SH" ]; then
  USER_PROMPT="$(cat "$FACTSET" | head -c 800) Style anchor: $STYLE."
  "$FUTRGROUP_MSCLONE_SH" \
    --brand "$BRAND" --product "$PRODUCT_NAME" --hook "$HOOK" --setting "$SETTING" \
    --avatar "$AVATAR" --mode "$MODE" --user-prompt "$USER_PROMPT" \
    > "$OUT/composed-prefix.txt"
  echo "[2-concept] prefix via marketing-studio-clone → $OUT/composed-prefix.txt ($(wc -w < "$OUT/composed-prefix.txt" | tr -d ' ') words)"
else
  echo "[FUTRGROUP] WARNING: marketing-studio-clone not configured (FUTRGROUP_MSCLONE_SH) — using simple composed prefix" >&2
  cat > "$OUT/composed-prefix.txt" <<EOF
Mode: $MODE | Brand: $BRAND | Product: $PRODUCT_NAME | Style anchor: $STYLE.
$(head -c 600 "$FACTSET")
EOF
fi

# ── Stage 2.2: OpenAI Chat Completion → 18-prompt framework ──
OPENAI_KEY="${OPENAI_API_KEY:-}"

if [ -n "$OPENAI_KEY" ] && command -v curl >/dev/null 2>&1 && command -v jq >/dev/null 2>&1; then
  echo "[2-concept] calling OpenAI gpt-5.5 (or fallback gpt-4-turbo) for 18-prompt framework..."

  # Build the canonical Franky Shaw prompt
  FACTSET_BODY="$(head -c 3000 "$FACTSET")"
  PREFIX_BODY="$(head -c 2500 "$OUT/composed-prefix.txt")"

  SYSTEM_PROMPT="You are an expert AI ad concept writer. You write NanoBanana Pro image prompts and Kling 3.0 video prompts for high-CTR Facebook video ads. Output STRICT JSON only — no prose, no markdown fences."

  USER_PROMPT_FULL=$(jq -nR --arg fs "$FACTSET_BODY" --arg pf "$PREFIX_BODY" --arg style "$STYLE" --arg brand "$BRAND" --arg product "$PRODUCT_NAME" '
    "I need you to create a 60 second NanoBananaPro prompt sequence for a " + $style + " ad encompassing what " + $product + " (brand: " + $brand + ") showcases. Output 18 numbered NanoBanana image prompts that follow a 5-beat psych spine: (1) Emotional Hook, (2) Problem Visualization, (3) Scientific Mechanism, (4) Visible Benefit, (5) Product Authority. Frame chain MUST be linked: P_n+1 must be visually adjacent to P_n so a Kling 3.0 transition between them feels seamless. Cultivate for high CTR Facebook video ad. Optimize for vertical 9:16 16:9 1:1 versatility.\n\n" +
    "Marketing Studio composed prefix:\n" + $pf + "\n\n" +
    "Product factset (from NotebookLM):\n" + $fs + "\n\n" +
    "Output JSON shape EXACTLY:\n" +
    "{\n" +
    "  \"concept_name\": string (e.g. \"The Architecture of Glow\"),\n" +
    "  \"style_note\": string,\n" +
    "  \"five_beat_spine\": [{\"beat\":1,\"name\":\"Emotional Hook\",\"prompt\":string}, ...5 entries],\n" +
    "  \"image_prompts_p1_to_p18\": [{\"id\":\"P01\",\"prompt\":string}, ...18 entries],\n" +
    "  \"voice_over_script_60s\": string,\n" +
    "  \"voice_emphasis_phrases\": [string, ...3-5 entries],\n" +
    "  \"suno_music_prompt\": string,\n" +
    "  \"facebook_ad_strategy\": {\"thumb_stopping_hook\":string, \"satisfaction_factor\":string, \"direct_claim\":string}\n" +
    "}"
  ')

  PAYLOAD=$(jq -n --arg sys "$SYSTEM_PROMPT" --argjson user "$USER_PROMPT_FULL" '{
    model: "gpt-4-turbo",
    response_format: {type: "json_object"},
    temperature: 0.7,
    max_tokens: 4000,
    messages: [
      {role:"system", content:$sys},
      {role:"user", content:$user}
    ]
  }')

  RESPONSE=$(curl -sS https://api.openai.com/v1/chat/completions \
    -H "Authorization: Bearer $OPENAI_KEY" \
    -H "Content-Type: application/json" \
    --data "$PAYLOAD" \
    --max-time 120 2>&1)

  CONTENT=$(echo "$RESPONSE" | jq -r '.choices[0].message.content // empty' 2>/dev/null)
  if [ -n "$CONTENT" ]; then
    echo "$CONTENT" > "$OUT/concept.json"
    # Validate it's parseable
    if jq empty "$OUT/concept.json" 2>/dev/null; then
      N_PROMPTS=$(jq '.image_prompts_p1_to_p18 | length' "$OUT/concept.json" 2>/dev/null || echo 0)
      echo "[2-concept] OpenAI returned $N_PROMPTS image prompts ✓"
    else
      echo "[2-concept] OpenAI returned non-JSON, falling back to stub" >&2
      CONTENT=""
    fi
  fi

  if [ -z "$CONTENT" ]; then
    ERR=$(echo "$RESPONSE" | jq -r '.error.message // "unknown"' 2>/dev/null)
    echo "[2-concept] OpenAI call failed: $ERR — writing stub" >&2
    OPENAI_KEY=""  # force stub branch below
  fi
fi

# ── Fallback stub if no OpenAI key or call failed ──
if [ ! -f "$OUT/concept.json" ]; then
  echo "[2-concept] writing stub concept.json (no OPENAI_API_KEY or call failed)" >&2
  cat > "$OUT/concept.json" <<EOF
{
  "concept_name": "TODO — wire OpenAI key",
  "style_note": "$STYLE",
  "five_beat_spine": [
    {"beat":1,"name":"Emotional Hook","prompt":"TODO P1"},
    {"beat":2,"name":"Problem Visualization","prompt":"TODO P5-P7"},
    {"beat":3,"name":"Scientific Mechanism","prompt":"TODO P8-P10"},
    {"beat":4,"name":"Visible Benefit","prompt":"TODO P11-P14"},
    {"beat":5,"name":"Product Authority","prompt":"TODO P15-P18"}
  ],
  "image_prompts_p1_to_p18": [
    {"id":"P01","prompt":"TODO"},{"id":"P02","prompt":"TODO"},{"id":"P03","prompt":"TODO"},
    {"id":"P04","prompt":"TODO"},{"id":"P05","prompt":"TODO"},{"id":"P06","prompt":"TODO"},
    {"id":"P07","prompt":"TODO"},{"id":"P08","prompt":"TODO"},{"id":"P09","prompt":"TODO"},
    {"id":"P10","prompt":"TODO"},{"id":"P11","prompt":"TODO"},{"id":"P12","prompt":"TODO"},
    {"id":"P13","prompt":"TODO"},{"id":"P14","prompt":"TODO"},{"id":"P15","prompt":"TODO"},
    {"id":"P16","prompt":"TODO"},{"id":"P17","prompt":"TODO"},{"id":"P18","prompt":"TODO"}
  ],
  "voice_over_script_60s": "TODO",
  "voice_emphasis_phrases": ["TODO"],
  "suno_music_prompt": "TODO",
  "facebook_ad_strategy": {"thumb_stopping_hook":"TODO","satisfaction_factor":"TODO","direct_claim":"TODO"}
}
EOF
fi

# ── Stage 2.3: extract sub-artifacts ──
# Voice direction (canonical Pixar-style — adapted to brand)
cat > "$OUT/voice-direction.txt" <<EOF
ElevenLabs Voice Engineering Prompt — Voice Style Direction:

"Warm, whimsical cinematic narration inspired by Pixar animated films. The voice should sound intelligent, calm, and slightly playful with a gentle sense of wonder. Speak clearly with natural pacing and emotional warmth, as if telling a beautiful story about $BRAND. The tone should feel premium and inspiring like an Apple keynote mixed with a Pixar narrator. Slight softness in delivery, subtle smiles in the voice, and thoughtful pauses for emotional impact. The narrator should sound trustworthy, elegant, and curious. Avoid sounding like a commercial announcer. Instead, sound like a thoughtful storyteller."

Voice flavor bullets:
- slight wonder/curiosity
- gentle pauses
- subtle smile in the voice
- calm confidence like a narrator from a Pixar short

Pacing: smooth and relaxed with occasional pauses.
EOF
# Append emphasis phrases from concept.json if present
if command -v jq >/dev/null 2>&1; then
  jq -r '.voice_emphasis_phrases // [] | "Emphasize: \"" + (.|join("\", \"")) + "\""' "$OUT/concept.json" >> "$OUT/voice-direction.txt" 2>/dev/null
fi
echo "" >> "$OUT/voice-direction.txt"
echo "(Paste this BEFORE the script in ElevenLabs voice-design / v3.)" >> "$OUT/voice-direction.txt"

# Append the actual VO script from concept.json
if command -v jq >/dev/null 2>&1; then
  VO_SCRIPT="$(jq -r '.voice_over_script_60s // empty' "$OUT/concept.json" 2>/dev/null)"
  if [ -n "$VO_SCRIPT" ] && [ "$VO_SCRIPT" != "TODO" ]; then
    {
      echo ""
      echo "---"
      echo "Voice-Over Script (60s):"
      echo ""
      echo "$VO_SCRIPT"
    } >> "$OUT/voice-direction.txt"
  fi
fi

# Suno prompt — pull from concept.json or fallback
SUNO=""
if command -v jq >/dev/null 2>&1; then
  SUNO="$(jq -r '.suno_music_prompt // empty' "$OUT/concept.json" 2>/dev/null)"
fi
if [ -z "$SUNO" ] || [ "$SUNO" = "TODO" ]; then
  SUNO="I need a whimsical custom Suno song made for this $STYLE ad. Calm but tailored to a Pixar-style advertisement. Fun, whimsical, lighthearted, with sophistication and minimal elegance. 60 seconds. No vocals."
fi
echo "$SUNO" > "$OUT/suno-prompt.txt"

echo "[2-concept] OK"
echo "  composed-prefix.txt"
echo "  concept.json ($([ -n "${CONTENT:-}" ] && echo "LIVE from OpenAI" || echo "stub"))"
echo "  voice-direction.txt"
echo "  suno-prompt.txt"
exit 0
