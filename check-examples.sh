#!/usr/bin/env bash
set -euo pipefail

echo "═══════════════════════════════════════════════════════════"
echo "🔍 KONTROLA SKILL-CREATOR - PŘÍKLADY"
echo "═══════════════════════════════════════════════════════════"
echo ""
echo "Skill-creator obsahuje PŘÍKLADY jak psát Skills."
echo "Tyto příklady používají UPPERCASE (FORMS.md, REFERENCE.md)"
echo "což je v ROZPORU s reálnou konvencí lowercase (forms.md)."
echo ""
echo "-----------------------------------------------------------"
echo ""

grep -n '\[.*\](.*\.md)' skills/skill-creator/SKILL.md | while IFS=: read -r line_num content; do
    echo "📝 Řádek $line_num:"
    echo "   $content"
    
    # Extrahuj link
    link=$(echo "$content" | grep -oP '\]\(\K[^)]+\.md(?=\))')
    
    # Zkontroluj case
    if [[ "$link" =~ ^[A-Z] ]]; then
        echo "   ⚠️  UPPERCASE: $link (příklad, ale zavádějící!)"
        
        # Zkontroluj zda soubor skutečně NEEXISTUJE (potvrzení že je to příklad)
        dir_path="skills/skill-creator"
        if [[ ! -f "$dir_path/$link" ]]; then
            echo "   ✓ Soubor neexistuje → potvrzeno že je to PŘÍKLAD"
        else
            echo "   ⚠️  Soubor EXISTUJE → to je problém!"
        fi
    else
        echo "   ✓ lowercase: $link (OK)"
    fi
    echo ""
done

echo "═══════════════════════════════════════════════════════════"
echo "📋 ZÁVĚR:"
echo ""
echo "Skill-creator obsahuje příklady s UPPERCASE odkazy:"
echo "  • [FORMS.md](FORMS.md)"
echo "  • [REFERENCE.md](REFERENCE.md)"
echo "  • [EXAMPLES.md](EXAMPLES.md)"
echo "  • [DOCX-JS.md](DOCX-JS.md)"
echo "  • [REDLINING.md](REDLINING.md)"
echo "  • [OOXML.md](OOXML.md)"
echo ""
echo "Tyto příklady jsou ZAVÁDĚJÍCÍ, protože:"
echo "  ✗ Reálná konvence je lowercase (forms.md, reference.md)"
echo "  ✗ Pravděpodobně způsobily bug v PDF skillu"
echo "  ✗ Mohly by způsobit další bugy v budoucnu"
echo ""
echo "DOPORUČENÍ:"
echo "  Aktualizovat příklady v skill-creator na lowercase"
echo "  aby odpovídaly skutečné konvenci repozitáře."
echo "═══════════════════════════════════════════════════════════"
