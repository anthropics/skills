#!/usr/bin/env bash
set -euo pipefail

# Najde všechny .md soubory a extrahuje z nich odkazy ve formátu:
# 1. Markdown links: [text](file.md)
# 2. Plain text references: "see file.md", "refer to file.md", "check file.md"

echo "═══════════════════════════════════════════════════════════"
echo "🔍 VALIDACE MARKDOWN ODKAZŮ - SKUTEČNÉ vs PŘÍKLADY"
echo "═══════════════════════════════════════════════════════════"
echo ""

total_files=0
total_links=0
broken_links=0
case_issues=0

# Funkce pro určení, zda je kontext "příklad"
is_example_context() {
    local file="$1"
    local line_num="$2"
    local line_content="$3"
    
    # Kontrola zda soubor obsahuje "example", "tutorial", "guide" v názvu nebo obsahu kolem
    if echo "$file" | grep -qi "example\|tutorial\|skill-creator"; then
        # V skill-creator jsou všechny odkazy příklady
        if echo "$file" | grep -q "skill-creator"; then
            return 0
        fi
    fi
    
    # Kontrola kontextu - 2 řádky před a po
    local context_start=$((line_num - 2))
    local context_end=$((line_num + 2))
    [[ $context_start -lt 1 ]] && context_start=1
    
    local context=$(sed -n "${context_start},${context_end}p" "$file")
    
    # Hledej indikátory příkladů
    if echo "$context" | grep -qi "example\|for instance\|e\.g\.\|such as\|template\|sample"; then
        return 0
    fi
    
    # Kontrola, zda je v code blocku
    if echo "$line_content" | grep -q '^\s*```\|^\s*`'; then
        return 0
    fi
    
    return 1
}

# Najdi všechny .md soubory
while IFS= read -r md_file; do
    ((total_files++))
    
    # Relativní cesta od root
    rel_path="${md_file#./}"
    dir_path=$(dirname "$rel_path")
    
    # Extrahuj markdown links: [text](file.md) nebo [text](./file.md)
    line_num=0
    while IFS= read -r line; do
        ((line_num++))
        
        # Najdi všechny markdown links v řádku
        echo "$line" | grep -oP '\[([^\]]+)\]\(([^)]+\.md)\)' | while IFS= read -r match; do
            # Extrahuj cestu z linku
            link_path=$(echo "$match" | sed -n 's/.*(\([^)]*\)).*/\1/p')
            
            # Přeskoč URL odkazy
            [[ "$link_path" =~ ^https?:// ]] && continue
            [[ "$link_path" =~ ^mailto: ]] && continue
            
            ((total_links++))
            
            # Normalizuj cestu
            if [[ "$link_path" == ./* ]]; then
                link_path="${link_path#./}"
            fi
            
            # Určí absolutní cestu k odkazovanému souboru
            if [[ "$link_path" == /* ]]; then
                target_file=".${link_path}"
            else
                target_file="${dir_path}/${link_path}"
            fi
            
            # Normalizuj cestu (resolv ..)
            target_file=$(realpath -m "$target_file" 2>/dev/null || echo "$target_file")
            
            # Kontrola existence (case-sensitive)
            if [[ ! -f "$target_file" ]]; then
                # Zkus case-insensitive
                target_file_lower=$(find "$(dirname "$target_file")" -maxdepth 1 -iname "$(basename "$target_file")" 2>/dev/null | head -1)
                
                if [[ -n "$target_file_lower" && -f "$target_file_lower" ]]; then
                    # Soubor existuje, ale s jiným case
                    if ! is_example_context "$md_file" "$line_num" "$line"; then
                        ((case_issues++))
                        echo "⚠️  CASE MISMATCH (SKUTEČNÝ ODKAZ):"
                        echo "    Soubor: $rel_path:$line_num"
                        echo "    Link: $link_path"
                        echo "    Očekáváno: $target_file"
                        echo "    Existuje jako: $target_file_lower"
                        echo "    Řádek: $line"
                        echo ""
                    else
                        echo "ℹ️  Case mismatch (PŘÍKLAD - OK):"
                        echo "    Soubor: $rel_path:$line_num"
                        echo "    Link: $link_path"
                        echo ""
                    fi
                else
                    # Soubor neexistuje vůbec
                    if ! is_example_context "$md_file" "$line_num" "$line"; then
                        ((broken_links++))
                        echo "❌ BROKEN LINK (SKUTEČNÝ ODKAZ):"
                        echo "    Soubor: $rel_path:$line_num"
                        echo "    Link: $link_path"
                        echo "    Target: $target_file (NEEXISTUJE)"
                        echo "    Řádek: $line"
                        echo ""
                    else
                        echo "ℹ️  Broken link (PŘÍKLAD - OK):"
                        echo "    Soubor: $rel_path:$line_num"
                        echo "    Link: $link_path"
                        echo ""
                    fi
                fi
            fi
        done
    done < "$md_file"
    
done < <(find . -name "*.md" -type f)

echo "═══════════════════════════════════════════════════════════"
echo "📊 STATISTIKA:"
echo "   Soubory: $total_files"
echo "   Celkem odkazů: $total_links"
echo "   Broken links (skutečné): $broken_links"
echo "   Case issues (skutečné): $case_issues"
echo "═══════════════════════════════════════════════════════════"

if [[ $broken_links -gt 0 || $case_issues -gt 0 ]]; then
    exit 1
fi
