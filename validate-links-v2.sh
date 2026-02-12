#!/usr/bin/env bash
# validate-links-v2.sh - Kompletní validace odkazů v markdown souborech
# Created: 2026-02-12
# Author: m4p1x
# Purpose: Kontrola broken links (markdown i plain text) v Anthropic skills repo

set -euo pipefail

# Barvy pro output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
TOTAL_FILES=0
TOTAL_LINKS=0
BROKEN_LINKS=0
VALID_LINKS=0

# Base directory
REPO_DIR="/var/home/mpx/Git/OpenCode/skills"

# Array pro broken links
declare -A BROKEN_FILES

echo "═══════════════════════════════════════════════════════"
echo " 🔍 Validace markdown odkazů v Anthropic Skills v2"
echo "═══════════════════════════════════════════════════════"
echo ""

# Najdi všechny .md soubory
mapfile -t MD_FILES < <(find "$REPO_DIR" -name "*.md" -type f | sort)

TOTAL_FILES=${#MD_FILES[@]}
echo "📄 Nalezeno markdown souborů: $TOTAL_FILES"
echo ""

# Funkce pro kontrolu existence souboru
check_link() {
    local MD_FILE="$1"
    local LINK="$2"
    local LINK_TYPE="$3"  # "markdown" nebo "plaintext"
    
    # Odstraň anchor (#section)
    local LINK_PATH="${LINK%%#*}"
    
    # Skip prázdné odkazy nebo pure anchory
    if [ -z "$LINK_PATH" ] || [[ "$LINK_PATH" == "#"* ]]; then
        return 0  # valid
    fi
    
    # Resolve absolutní/relativní cestu
    local TARGET
    if [[ "$LINK_PATH" == /* ]]; then
        # Absolutní cesta (od repo root)
        TARGET="$REPO_DIR$LINK_PATH"
    else
        # Relativní cesta (od aktuálního souboru)
        local DIR=$(dirname "$MD_FILE")
        TARGET="$DIR/$LINK_PATH"
    fi
    
    # Normalizuj cestu (resolve ../ a ./)
    TARGET=$(realpath -m "$TARGET" 2>/dev/null || echo "$TARGET")
    
    # Zkontroluj existenci
    if [ ! -e "$TARGET" ]; then
        local REL_PATH="${MD_FILE#$REPO_DIR/}"
        if [ -z "${BROKEN_FILES[$REL_PATH]:-}" ]; then
            echo -e "${YELLOW}📝 $REL_PATH${NC}"
            BROKEN_FILES[$REL_PATH]=1
        fi
        echo -e "  ${RED}✗ BROKEN ($LINK_TYPE):${NC} $LINK"
        BROKEN_LINKS=$((BROKEN_LINKS + 1))
        return 1
    else
        VALID_LINKS=$((VALID_LINKS + 1))
        return 0
    fi
}

# Pro každý markdown soubor
for MD_FILE in "${MD_FILES[@]}"; do
    
    # === 1. Markdown linky [text](path) ===
    mapfile -t MD_LINKS < <(
        grep -oP '\[([^\]]+)\]\((?!http|mailto:)([^)]+)\)' "$MD_FILE" 2>/dev/null | \
        grep -oP '\((?!http|mailto:)\K[^)]+' || true
    )
    
    for LINK in "${MD_LINKS[@]}"; do
        [ -z "$LINK" ] && continue
        TOTAL_LINKS=$((TOTAL_LINKS + 1))
        check_link "$MD_FILE" "$LINK" "markdown"
    done
    
    # === 2. Plain text odkazy na .md soubory ===
    # Hledáme: "see FILE.md", "read FILE.md", "check FILE.md" atd.
    # Pattern: uppercase nebo lowercase .md soubory zmíněné v textu
    mapfile -t PLAIN_LINKS < <(
        grep -oP '(?:see|read|check|in|from|to|refer to|described in|found in)\s+\K[A-Za-z0-9_-]+\.md\b' "$MD_FILE" 2>/dev/null || true
    )
    
    for LINK in "${PLAIN_LINKS[@]}"; do
        [ -z "$LINK" ] && continue
        TOTAL_LINKS=$((TOTAL_LINKS + 1))
        check_link "$MD_FILE" "$LINK" "plaintext"
    done
    
    # === 3. Relative path odkazy ===
    # Hledáme: references/file.md, scripts/script.py atd.
    mapfile -t PATH_LINKS < <(
        grep -oP '(?:^|[^(])\K[a-z0-9_/-]+/[a-z0-9_.-]+\.(md|py|sh|js|ts)\b' "$MD_FILE" 2>/dev/null || true
    )
    
    for LINK in "${PATH_LINKS[@]}"; do
        [ -z "$LINK" ] && continue
        # Skip if it's part of URL
        [[ "$LINK" =~ ^http ]] && continue
        TOTAL_LINKS=$((TOTAL_LINKS + 1))
        check_link "$MD_FILE" "$LINK" "path"
    done
done

# Separator mezi broken a summary
if [ $BROKEN_LINKS -gt 0 ]; then
    echo ""
fi

# Summary
echo "═══════════════════════════════════════════════════════"
echo " 📊 SUMMARY"
echo "───────────────────────────────────────────────────────"
echo "📄 Zkontrolované soubory: $TOTAL_FILES"
echo "🔗 Celkem odkazů:         $TOTAL_LINKS"
echo -e "${GREEN}✓ Validní odkazy:${NC}         $VALID_LINKS"
echo -e "${RED}✗ Broken odkazy:${NC}          $BROKEN_LINKS"
echo "═══════════════════════════════════════════════════════"

if [ $BROKEN_LINKS -eq 0 ]; then
    echo -e "${GREEN}🎉 Všechny odkazy jsou validní!${NC}"
    exit 0
else
    echo -e "${RED}⚠️  Nalezeny broken odkazy!${NC}"
    exit 1
fi
