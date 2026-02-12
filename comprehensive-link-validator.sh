#!/usr/bin/env bash
# comprehensive-link-validator.sh - Kompletní validace všech odkazů v markdown
# Created: 2026-02-12
# Author: m4p1x
# Purpose: Najít všechny broken odkazy v Anthropic skills repo

set -euo pipefail

# Barvy
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

REPO_DIR="/var/home/mpx/Git/OpenCode/skills"
REPORT_FILE="$REPO_DIR/link-validation-report.txt"

# Counters
TOTAL_MD_FILES=0
TOTAL_ISSUES=0

# Arrays pro výsledky (inicializuj prázdné)
CASE_MISMATCHES=()
BROKEN_LINKS=()
WARNINGS=()

echo "═══════════════════════════════════════════════════════" | tee "$REPORT_FILE"
echo " 🔍 COMPREHENSIVE LINK VALIDATION" | tee -a "$REPORT_FILE"
echo " Anthropic Skills Repository" | tee -a "$REPORT_FILE"
echo "═══════════════════════════════════════════════════════" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"
echo "⏰ Started: $(date '+%Y-%m-%d %H:%M:%S')" | tee -a "$REPORT_FILE"
echo "📂 Directory: $REPO_DIR" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"

# Najdi všechny .md soubory
mapfile -t MD_FILES < <(find "$REPO_DIR" -name "*.md" -type f | sort)
TOTAL_MD_FILES=${#MD_FILES[@]}

echo "📄 Found $TOTAL_MD_FILES markdown files" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"
echo "───────────────────────────────────────────────────────" | tee -a "$REPORT_FILE"
echo " SCANNING FOR ISSUES..." | tee -a "$REPORT_FILE"
echo "───────────────────────────────────────────────────────" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"

# Pro každý markdown soubor
for MD_FILE in "${MD_FILES[@]}"; do
    REL_PATH="${MD_FILE#$REPO_DIR/}"
    DIR=$(dirname "$MD_FILE")
    
    # Skip THIRD_PARTY_NOTICES.md (obsahuje email odkazy)
    if [[ "$REL_PATH" == "THIRD_PARTY_NOTICES.md" ]]; then
        continue
    fi
    
    # === KONTROLA 1: Markdown odkazy [text](file.md) ===
    while IFS= read -r LINE; do
        # Extrahuj markdown linky (ignoruj http/https/mailto)
        PATTERN='\[([^\]]+)\]\(([^)]+)\)'
        if [[ "$LINE" =~ $PATTERN ]]; then
            LINK="${BASH_REMATCH[2]}"
            
            # Skip URL a mailto odkazy
            [[ "$LINK" =~ ^https?:// ]] && continue
            [[ "$LINK" =~ ^mailto: ]] && continue
            
            # Skip pure anchors
            [[ "$LINK" =~ ^# ]] && continue
            
            # Odstraň anchor z cesty
            LINK_PATH="${LINK%%#*}"
            [ -z "$LINK_PATH" ] && continue
            
            # Resolve cestu
            if [[ "$LINK_PATH" == /* ]]; then
                TARGET="$REPO_DIR$LINK_PATH"
            else
                TARGET="$DIR/$LINK_PATH"
            fi
            
            TARGET=$(realpath -m "$TARGET" 2>/dev/null || echo "$TARGET")
            
            # Zkontroluj existenci
            if [ ! -e "$TARGET" ]; then
                TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
                BROKEN_LINKS+=("❌ BROKEN LINK in $REL_PATH")
                BROKEN_LINKS+=("   Link: [$LINK_PATH]")
                BROKEN_LINKS+=("   Target: $TARGET")
                BROKEN_LINKS+=("")
            fi
        fi
    done < "$MD_FILE"
    
    # === KONTROLA 2: Plain text odkazy na .md soubory ===
    # Hledáme: "see FILE.md", "read FILE.md" atd.
    mapfile -t PLAIN_REFS < <(grep -oE '\b[A-Z][A-Z_-]*\.md\b' "$MD_FILE" 2>/dev/null || true)
    
    for REF in "${PLAIN_REFS[@]}"; do
        [ -z "$REF" ] && continue
        
        # Skip common files
        [[ "$REF" == "README.md" ]] && continue
        [[ "$REF" == "SKILL.md" ]] && continue
        [[ "$REF" == "LICENSE.md" ]] && continue
        
        # Zkontroluj existenci (case-sensitive)
        if [ ! -f "$DIR/$REF" ]; then
            # Zkus lowercase variantu
            LOWER_REF=$(echo "$REF" | tr '[:upper:]' '[:lower:]')
            
            if [ -f "$DIR/$LOWER_REF" ]; then
                TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
                CASE_MISMATCHES+=("⚠️  CASE MISMATCH in $REL_PATH")
                CASE_MISMATCHES+=("   Reference: $REF (UPPERCASE)")
                CASE_MISMATCHES+=("   Actual file: $LOWER_REF (lowercase)")
                CASE_MISMATCHES+=("")
            else
                # Zkontroluj jestli je to v code bloku (example)
                # Jednoduchá heuristika: pokud je soubor skill-creator, pravděpodobně example
                if [[ "$REL_PATH" =~ skill-creator ]]; then
                    WARNINGS+=("ℹ️  POTENTIAL EXAMPLE in $REL_PATH")
                    WARNINGS+=("   Reference: $REF (may be documentation example)")
                    WARNINGS+=("")
                else
                    TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
                    BROKEN_LINKS+=("❌ MISSING FILE in $REL_PATH")
                    BROKEN_LINKS+=("   Reference: $REF")
                    BROKEN_LINKS+=("   Expected location: $DIR/$REF")
                    BROKEN_LINKS+=("")
                fi
            fi
        fi
    done
done

# === VÝPIS VÝSLEDKŮ ===
echo "" | tee -a "$REPORT_FILE"
echo "═══════════════════════════════════════════════════════" | tee -a "$REPORT_FILE"
echo " 📊 VALIDATION RESULTS" | tee -a "$REPORT_FILE"
echo "═══════════════════════════════════════════════════════" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"

# Case Mismatches
if [ "${#CASE_MISMATCHES[@]}" -gt 0 ]; then
    echo -e "${YELLOW}⚠️  CASE MISMATCHES FOUND:${NC}" | tee -a "$REPORT_FILE"
    echo "───────────────────────────────────────────────────────" | tee -a "$REPORT_FILE"
    for LINE in "${CASE_MISMATCHES[@]}"; do
        echo "$LINE" | tee -a "$REPORT_FILE"
    done
    echo "" | tee -a "$REPORT_FILE"
fi

# Broken Links
if [ "${#BROKEN_LINKS[@]}" -gt 0 ]; then
    echo -e "${RED}❌ BROKEN LINKS FOUND:${NC}" | tee -a "$REPORT_FILE"
    echo "───────────────────────────────────────────────────────" | tee -a "$REPORT_FILE"
    for LINE in "${BROKEN_LINKS[@]}"; do
        echo "$LINE" | tee -a "$REPORT_FILE"
    done
    echo "" | tee -a "$REPORT_FILE"
fi

# Warnings
if [ "${#WARNINGS[@]}" -gt 0 ]; then
    echo -e "${BLUE}ℹ️  WARNINGS (Documentation Examples):${NC}" | tee -a "$REPORT_FILE"
    echo "───────────────────────────────────────────────────────" | tee -a "$REPORT_FILE"
    for LINE in "${WARNINGS[@]}"; do
        echo "$LINE" | tee -a "$REPORT_FILE"
    done
    echo "" | tee -a "$REPORT_FILE"
fi

# Summary
echo "═══════════════════════════════════════════════════════" | tee -a "$REPORT_FILE"
echo " 📈 SUMMARY" | tee -a "$REPORT_FILE"
echo "───────────────────────────────────────────────────────" | tee -a "$REPORT_FILE"
echo "📄 Scanned files:     $TOTAL_MD_FILES" | tee -a "$REPORT_FILE"
echo "❌ Total issues:      $TOTAL_ISSUES" | tee -a "$REPORT_FILE"
echo "⚠️  Case mismatches:  $((${#CASE_MISMATCHES[@]} / 4))" | tee -a "$REPORT_FILE"
echo "❌ Broken links:      $((${#BROKEN_LINKS[@]} / 4))" | tee -a "$REPORT_FILE"
echo "ℹ️  Warnings:         $((${#WARNINGS[@]} / 3))" | tee -a "$REPORT_FILE"
echo "═══════════════════════════════════════════════════════" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"
echo "⏰ Completed: $(date '+%Y-%m-%d %H:%M:%S')" | tee -a "$REPORT_FILE"
echo "📄 Report saved: $REPORT_FILE" | tee -a "$REPORT_FILE"
echo "" | tee -a "$REPORT_FILE"

if [ $TOTAL_ISSUES -eq 0 ]; then
    echo -e "${GREEN}✅ No critical issues found!${NC}" | tee -a "$REPORT_FILE"
    exit 0
else
    echo -e "${RED}⚠️  Found $TOTAL_ISSUES issue(s) that need attention${NC}" | tee -a "$REPORT_FILE"
    exit 1
fi
