#!/usr/bin/env bash
set -euo pipefail

echo "═══════════════════════════════════════════════════════════"
echo "🔍 FINÁLNÍ VALIDACE - SKUTEČNÉ ODKAZY"
echo "═══════════════════════════════════════════════════════════"
echo ""
echo "Kontroluji Skills s referenčními soubory:"
echo "  - pdf/ (forms.md, reference.md)"
echo "  - pptx/ (editing.md, pptxgenjs.md)"
echo "  - mcp-builder/ (reference/*.md)"
echo ""
echo "-----------------------------------------------------------"

issues=0

# PDF Skill - zkontroluj odkazy na forms.md a reference.md
echo "📄 PDF Skill:"
while IFS=: read -r line_num content; do
    if echo "$content" | grep -q '\[.*\](forms\.md)'; then
        if [[ -f skills/pdf/forms.md ]]; then
            echo "  ✓ Řádek $line_num: [forms.md](forms.md) → OK"
        else
            echo "  ❌ Řádek $line_num: forms.md NEEXISTUJE"
            ((issues++))
        fi
    fi
    
    if echo "$content" | grep -q '\[.*\](reference\.md)'; then
        if [[ -f skills/pdf/reference.md ]]; then
            echo "  ✓ Řádek $line_num: [reference.md](reference.md) → OK"
        else
            echo "  ❌ Řádek $line_num: reference.md NEEXISTUJE"
            ((issues++))
        fi
    fi
done < <(grep -n '\[.*\](.*\.md)' skills/pdf/SKILL.md)

echo ""
echo "📊 PPTX Skill:"
while IFS=: read -r line_num content; do
    if echo "$content" | grep -q '\[.*\](editing\.md)'; then
        if [[ -f skills/pptx/editing.md ]]; then
            echo "  ✓ Řádek $line_num: [editing.md](editing.md) → OK"
        else
            echo "  ❌ Řádek $line_num: editing.md NEEXISTUJE"
            ((issues++))
        fi
    fi
    
    if echo "$content" | grep -q '\[.*\](pptxgenjs\.md)'; then
        if [[ -f skills/pptx/pptxgenjs.md ]]; then
            echo "  ✓ Řádek $line_num: [pptxgenjs.md](pptxgenjs.md) → OK"
        else
            echo "  ❌ Řádek $line_num: pptxgenjs.md NEEXISTUJE"
            ((issues++))
        fi
    fi
done < <(grep -n '\[.*\](.*\.md)' skills/pptx/SKILL.md)

echo ""
echo "🔌 MCP Builder Skill:"
while IFS=: read -r line_num content; do
    # Extrahuj cestu k .md souboru z linku
    link=$(echo "$content" | grep -oP '\]\(\K\./reference/[^)]+\.md(?=\))')
    if [[ -n "$link" ]]; then
        # Odstraň ./ prefix
        file_path="skills/mcp-builder/${link#./}"
        if [[ -f "$file_path" ]]; then
            echo "  ✓ Řádek $line_num: $link → OK"
        else
            echo "  ❌ Řádek $line_num: $file_path NEEXISTUJE"
            ((issues++))
        fi
    fi
done < <(grep -n '\[.*\](.*\.md)' skills/mcp-builder/SKILL.md)

echo ""
echo "═══════════════════════════════════════════════════════════"
if [[ $issues -eq 0 ]]; then
    echo "✅ VÝSLEDEK: Všechny skutečné odkazy jsou validní!"
    echo ""
    echo "Závěr:"
    echo "  • PDF skill používá správné lowercase odkazy"
    echo "  • PPTX skill používá správné lowercase odkazy"
    echo "  • MCP Builder skill používá správné odkazy"
    echo "  • Všechny odkazované soubory existují"
    echo "  • Case sensitivity je v pořádku"
else
    echo "⚠️  VÝSLEDEK: Nalezeno $issues problémů"
fi
echo "═══════════════════════════════════════════════════════════"

exit $issues
