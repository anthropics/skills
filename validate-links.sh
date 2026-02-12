#!/usr/bin/env bash
# validate-links.sh - Validace odkazů v markdown souborech
# Created: 2026-02-12
# Author: m4p1x
# Purpose: Kontrola broken links v markdown souborech Anthropic skills repo

set -euo pipefail

# Barvy pro output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Counters
TOTAL_FILES=0
TOTAL_LINKS=0
BROKEN_LINKS=0
VALID_LINKS=0

# Base directory
REPO_DIR="/var/home/mpx/Git/OpenCode/skills"

echo "═══════════════════════════════════════════════════════"
echo " 🔍 Validace markdown odkazů v Anthropic Skills"
echo "═══════════════════════════════════════════════════════"
echo ""

# Najdi všechny .md soubory
mapfile -t MD_FILES < <(find "$REPO_DIR" -name "*.md" -type f | sort)

TOTAL_FILES=${#MD_FILES[@]}
echo "📄 Nalezeno markdown souborů: $TOTAL_FILES"
echo ""

# Pro každý markdown soubor
for MD_FILE in "${MD_FILES[@]}"; do
    # Získej relativní cestu pro lepší čitelnost
    REL_PATH="${MD_FILE#$REPO_DIR/}"
    
    # Extrahuj všechny markdown odkazy typu [text](path)
    # Ignoruj http/https URL a mailto: linky, zajímají nás jen lokální soubory
    mapfile -t LINKS < <(grep -oP '\[([^\]]+)\]\((?!http|mailto:)([^)]+)\)' "$MD_FILE" 2>/dev/null | grep -oP '\((?!http|mailto:)\K[^)]+' || true)
    
    if [ ${#LINKS[@]} -eq 0 ] || [ -z "${LINKS[0]}" ]; then
        continue
    fi
    
    FILE_HAS_BROKEN=false
    
    for LINK in "${LINKS[@]}"; do
        TOTAL_LINKS=$((TOTAL_LINKS + 1))
        
        # Odstraň anchor (#section)
        LINK_PATH="${LINK%%#*}"
        
        # Skip prázdné odkazy nebo anchory
        if [ -z "$LINK_PATH" ] || [[ "$LINK_PATH" == "#"* ]]; then
            VALID_LINKS=$((VALID_LINKS + 1))
            continue
        fi
        
        # Resolve absolutní/relativní cestu
        if [[ "$LINK_PATH" == /* ]]; then
            # Absolutní cesta (od repo root)
            TARGET="$REPO_DIR$LINK_PATH"
        else
            # Relativní cesta (od aktuálního souboru)
            DIR=$(dirname "$MD_FILE")
            TARGET="$DIR/$LINK_PATH"
        fi
        
        # Normalizuj cestu (resolve ../ a ./)
        TARGET=$(realpath -m "$TARGET" 2>/dev/null || echo "$TARGET")
        
        # Zkontroluj existenci
        if [ ! -e "$TARGET" ]; then
            if [ "$FILE_HAS_BROKEN" = false ]; then
                echo -e "${YELLOW}📝 $REL_PATH${NC}"
                FILE_HAS_BROKEN=true
            fi
            echo -e "  ${RED}✗ BROKEN:${NC} $LINK"
            BROKEN_LINKS=$((BROKEN_LINKS + 1))
        else
            VALID_LINKS=$((VALID_LINKS + 1))
        fi
    done
    
    if [ "$FILE_HAS_BROKEN" = true ]; then
        echo ""
    fi
done

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
