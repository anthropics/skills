#!/usr/bin/env bash
set -euo pipefail

echo "═══════════════════════════════════════════════════════════"
echo "🔍 VALIDACE SKUTEČNÝCH ODKAZŮ (bez příkladů)"
echo "═══════════════════════════════════════════════════════════"
echo ""

issues=0

# Extrahuj všechny markdown odkazy (kromě skill-creator)
grep -rn '\[.*\](.*\.md)' --include="*.md" . | grep -v "skills/skill-creator" | while IFS=: read -r file line_num content; do
    # Extrahuj všechny odkazy z řádku
    echo "$content" | grep -oP '\]\(\K[^)]+\.md(?=\))' | while read -r link; do
        # Přeskoč URL odkazy
        [[ "$link" =~ ^https?:// ]] && continue
        [[ "$link" =~ ^mailto: ]] && continue
        
        # Získej adresář zdrojového souboru
        dir_path=$(dirname "$file")
        
        # Normalizuj link path
        if [[ "$link" == ./* ]]; then
            target="${dir_path}/${link#./}"
        elif [[ "$link" == /* ]]; then
            target=".${link}"
        else
            target="${dir_path}/${link}"
        fi
        
        # Normalize path
        target=$(realpath -m "$target" 2>/dev/null || echo "$target")
        
        # Kontrola existence
        if [[ ! -f "$target" ]]; then
            echo "❌ BROKEN LINK:"
            echo "   Soubor: ${file#./}:${line_num}"
            echo "   Link: $link"
            echo "   Očekávaný soubor: $target"
            echo "   Status: NEEXISTUJE"
            echo ""
            ((issues++))
        else
            # Soubor existuje - zkontroluj case sensitivity
            actual_basename=$(basename "$target")
            link_basename=$(basename "$link")
            
            if [[ "$actual_basename" != "$link_basename" ]]; then
                echo "⚠️  CASE MISMATCH:"
                echo "   Soubor: ${file#./}:${line_num}"
                echo "   Link: $link"
                echo "   V linku: $link_basename"
                echo "   Skutečný soubor: $actual_basename"
                echo "   Status: Funguje na case-insensitive FS, selže na Linux/macOS"
                echo ""
                ((issues++))
            else
                echo "✓ OK: ${file#./}:${line_num} → $link"
            fi
        fi
    done
done

echo ""
echo "═══════════════════════════════════════════════════════════"
if [[ $issues -eq 0 ]]; then
    echo "✓ Všechny odkazy jsou validní!"
else
    echo "⚠️  Nalezeno $issues problémů"
fi
echo "═══════════════════════════════════════════════════════════"

exit $issues
