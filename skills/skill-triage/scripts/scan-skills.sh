#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# shellcheck shell=bash
#
# scan-skills.sh — emit name|source|description for every installed skill.
# Source = personal | plugin:<plugin-name> | project
# One line per skill, pipe-delimited, description trimmed to 280 chars.
# Cache is per-UID under ${XDG_CACHE_HOME:-$HOME/.cache}/skill-triage/.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scan-skills.sh [--refresh] [--help]

  --refresh    Bust the cache and rescan from disk.
  --help, -h   Show this message.

Scans personal (~/.claude/skills), plugin (~/.claude/plugins/cache/*),
and project (.claude/skills) skill directories for SKILL.md files.
Emits one line per skill: name|source|description.
EOF
}

REFRESH=0
for arg in "$@"; do
  case "$arg" in
    -h|--help) usage; exit 0 ;;
    --refresh) REFRESH=1 ;;
    "") ;;
    *) echo "scan-skills.sh: unknown flag: $arg" >&2; usage >&2; exit 2 ;;
  esac
done

umask 077
CACHE_DIR="${XDG_CACHE_HOME:-$HOME/.cache}/skill-triage"
mkdir -p "$CACHE_DIR"
CACHE="$CACHE_DIR/cache.${UID:-$(id -u)}.psv"
TTL=600

if (( REFRESH == 0 )) && [[ -f "$CACHE" ]]; then
  mtime=$(stat -f %m "$CACHE" 2>/dev/null || stat -c %Y "$CACHE" 2>/dev/null || echo "")
  if [[ -n "$mtime" ]]; then
    age=$(( $(date +%s) - mtime ))
    if (( age < TTL )); then
      cat "$CACHE"
      exit 0
    fi
  fi
fi

# Parse only the YAML frontmatter block (between leading --- delimiters).
# Strips quotes, trims whitespace, joins folded blocks, sanitizes pipe chars.
emit() {
  local path="$1" source="$2"
  [[ -f "$path" && -r "$path" ]] || return 0
  local name desc
  name=$(awk '
    BEGIN { fm=0 }
    /^---[[:space:]]*$/ { fm++; if (fm==2) exit; next }
    fm==1 && /^name:/ {
      sub(/^name:[[:space:]]*/,"");
      gsub(/^["'"'"']|["'"'"']$/,"");
      print; exit
    }
  ' "$path")
  desc=$(awk '
    BEGIN { fm=0; mode=0 }
    /^---[[:space:]]*$/ { fm++; if (fm==2) exit; next }
    fm!=1 { next }
    /^description:[[:space:]]*[|>][-+0-9]*[[:space:]]*$/ { mode=1; next }
    /^description:/ {
      sub(/^description:[[:space:]]*/,"");
      gsub(/^["'"'"']|["'"'"']$/,"");
      print; exit
    }
    mode && /^[a-zA-Z_][a-zA-Z0-9_.-]*:/ { exit }
    mode { gsub(/^[[:space:]]+/,""); printf "%s ", $0 }
  ' "$path" | tr -d '\n\r' | tr '|' '/' | tr -s ' ' | cut -c1-280)
  [[ -z "$name" ]] && return 0
  printf '%s|%s|%s\n' "$name" "$source" "$desc"
}

scan_dir() {
  local root="$1" source="$2"
  [[ -d "$root" ]] || return 0
  while IFS= read -r -d '' f; do
    emit "$f" "$source"
  done < <(find "$root" -maxdepth 6 -name SKILL.md -print0 2>/dev/null)
}

TMP_OUT="$(mktemp "${CACHE}.XXXXXX")"
trap 'rm -f "$TMP_OUT"' EXIT INT TERM

{
  scan_dir "$HOME/.claude/skills" "personal"
  if [[ -d "$HOME/.claude/plugins/cache" ]]; then
    for plugin_root in "$HOME"/.claude/plugins/cache/*/; do
      [[ -d "$plugin_root" ]] || continue
      pname=$(basename "$plugin_root")
      scan_dir "$plugin_root" "plugin:$pname"
    done
  fi
  scan_dir ".claude/skills" "project"
} | sort -u > "$TMP_OUT"

mv -f "$TMP_OUT" "$CACHE"
trap - EXIT INT TERM
cat "$CACHE"
