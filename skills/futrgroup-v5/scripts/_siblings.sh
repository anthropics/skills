#!/usr/bin/env bash
# _siblings.sh — Sibling-skill resolver (sourced by stage scripts)
#
# For each sibling skill, resolve a script path in this order:
#   1. Env var FUTRGROUP_<SKILL>_SH (caller-supplied)
#   2. $FUTRGROUP_SIBLINGS_HOME/<skill>/scripts/<entry>.sh
#   3. (no fallback — variable left empty, caller falls back to stub)
#
# Emits a single one-line WARNING to stderr if a sibling is unresolved AND
# the caller marks it as required-for-full-functionality. Stage scripts
# choose whether to fail or stub.
#
# Defaults: $FUTRGROUP_SIBLINGS_HOME=$HOME/.futrgroup/siblings (override per machine).
#
# Resolved vars (caller can read):
#   FUTRGROUP_NOTEBOOKLM_SH       — stage 1
#   FUTRGROUP_MSCLONE_SH          — stage 2 (marketing-studio-clone/scripts/compose.sh)
#   FUTRGROUP_MUAPI_IMG_SH        — stage 3
#   FUTRGROUP_MUAPI_I2V_SH        — stage 4
#   FUTRGROUP_MUAPI_MUSIC_SH      — stage 6
#   FUTRGROUP_VIDEO_GEN_SH        — stage 4 (FAL Kling wrapper)
#   FUTRGROUP_VOICEOVER_SH        — stage 5
#   FUTRGROUP_MCSLA_SH            — stage 4 prompt builder
#   FUTRGROUP_HIGGSFIELD_GEN_SH   — stage 3 (Soul ID)
#   FUTRGROUP_HIGGSFIELD_I2V_SH   — stage 4
#   FUTRGROUP_HIGGSFIELD_VIRALITY_SH — post-stage 7
#   FUTRGROUP_AD_ID_MINT_SH       — pre-stage 3
#   FUTRGROUP_CARDFLIP_SH         — stage 4 QA
#   FUTRGROUP_GODAUDIT_SH         — post-stage 7
#   FUTRGROUP_REMOTION_SH         — stage 7
#   FUTRGROUP_HYPERFRAMES_SH      — stage 7
#   FUTRGROUP_TOPAZ_BIN           — stage 7 (tvai / tvai-cli)

FUTRGROUP_SIBLINGS_HOME="${FUTRGROUP_SIBLINGS_HOME:-$HOME/.futrgroup/siblings}"

# resolve_sibling <var_name> <skill_name> <relative_entry>
# Sets the named var to first available path; leaves empty if none.
_fg_resolve_sibling() {
  local var_name="$1" skill="$2" entry="$3"
  # 1. caller-supplied env override
  local current
  eval "current=\${$var_name:-}"
  if [ -n "$current" ] && [ -x "$current" ]; then
    return 0
  fi
  # 2. siblings home convention
  local candidate="$FUTRGROUP_SIBLINGS_HOME/$skill/scripts/$entry"
  if [ -x "$candidate" ]; then
    eval "$var_name=\"$candidate\""
    return 0
  fi
  # 3. Not resolved — leave empty
  eval "$var_name=\"\""
  return 1
}

# Resolve all siblings (silent — callers decide whether to warn/fail)
_fg_resolve_sibling FUTRGROUP_NOTEBOOKLM_SH        notebooklm-research      run.sh
_fg_resolve_sibling FUTRGROUP_MSCLONE_SH           marketing-studio-clone   compose.sh
_fg_resolve_sibling FUTRGROUP_MCSLA_SH             mcsla-prompt-builder     mcsla-build.sh
_fg_resolve_sibling FUTRGROUP_MUAPI_IMG_SH         muapi                    img.sh
_fg_resolve_sibling FUTRGROUP_MUAPI_I2V_SH         muapi                    i2v.sh
_fg_resolve_sibling FUTRGROUP_MUAPI_MUSIC_SH       muapi                    create-music.sh
_fg_resolve_sibling FUTRGROUP_VIDEO_GEN_SH         video-gen                video-gen.sh
_fg_resolve_sibling FUTRGROUP_VOICEOVER_SH         ai-voiceover             gen.sh
_fg_resolve_sibling FUTRGROUP_HIGGSFIELD_GEN_SH    higgsfield-cli           soul-gen.sh
_fg_resolve_sibling FUTRGROUP_HIGGSFIELD_I2V_SH    higgsfield-cli           i2v.sh
_fg_resolve_sibling FUTRGROUP_HIGGSFIELD_VIRALITY_SH higgsfield-cli         virality.sh
_fg_resolve_sibling FUTRGROUP_AD_ID_MINT_SH        unified-intel            ad-id-mint.sh
_fg_resolve_sibling FUTRGROUP_CARDFLIP_SH          video-card-flip-detector detect.sh
_fg_resolve_sibling FUTRGROUP_GODAUDIT_SH          god-mode-audit           god-audit.sh
_fg_resolve_sibling FUTRGROUP_REMOTION_SH          remotion-renderer        remotion-render.sh
_fg_resolve_sibling FUTRGROUP_HYPERFRAMES_SH       hyperframes-render       hyperframes-render.sh

# Topaz: a bin, not a sibling skill. Read $FUTRGROUP_TOPAZ_BIN or auto-detect.
if [ -z "${FUTRGROUP_TOPAZ_BIN:-}" ]; then
  FUTRGROUP_TOPAZ_BIN="$(command -v tvai-cli 2>/dev/null || command -v tvai 2>/dev/null || echo "")"
fi

# Emit a one-line missing-sibling summary if FUTRGROUP_VERBOSE=1
if [ "${FUTRGROUP_VERBOSE:-0}" = "1" ]; then
  for v in NOTEBOOKLM_SH MSCLONE_SH MCSLA_SH MUAPI_IMG_SH MUAPI_I2V_SH MUAPI_MUSIC_SH \
           VIDEO_GEN_SH VOICEOVER_SH HIGGSFIELD_GEN_SH HIGGSFIELD_I2V_SH AD_ID_MINT_SH \
           CARDFLIP_SH GODAUDIT_SH REMOTION_SH HYPERFRAMES_SH; do
    eval "val=\${FUTRGROUP_${v}:-}"
    if [ -z "$val" ]; then
      echo "[FUTRGROUP] missing sibling: FUTRGROUP_${v} (stub will be used)" >&2
    fi
  done
fi
