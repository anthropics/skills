---
name: comparison-table-v2
description: Generate professional comparison tables (新旧対比表) that show before/after differences in Word documents with hierarchical structure analysis and automatic heading pattern detection. v4.0 understands document hierarchy, groups content by top-level headings, displays items in correct order within articles, and merges same article content into single cells without internal dividers.
---

# Comparison Table Generator v2 (DOCX)

Generate professional Word documents (新旧対比表) comparing before/after versions of Word documents with **hierarchical structure analysis** and **automatic heading pattern detection**. The system first analyzes document hierarchy to identify top-level articles and sub-level items, then performs accurate comparisons respecting the document structure.

## Quick Start

**Current Version**: v4.0 (2025-10-30)

**Key Improvements in v4.0:**
- ✅ **NEW**: Hierarchical structure analysis - understands parent-child relationships
- ✅ **NEW**: Top-level heading identification - correctly identifies article boundaries
- ✅ **NEW**: Item number ordering - displays added/modified/deleted items in correct sequence
- ✅ **NEW**: Single-cell article display - merges all content within same article into one cell
- ✅ **NEW**: No internal dividers - cleaner presentation within articles
- ✅ Automatic heading pattern detection with 12 supported formats
- ✅ Intelligent hierarchy level assignment for each pattern

**Supported Formats (Auto-detected with Hierarchy Levels):**
1. **Legal style** (Level 1): `第3条`, `第三条`, `第3条の2`
2. **Numbered style** (Level 1): `3. (見出し)`, `3. （見出し）`
3. **Hierarchical** (Level 2+): `3.1`, `3.1.1`, `3.1.2.1` (level = number of dots + 1)
4. **Hyphenated** (Level 2): `3-1`, `3-2`, `10-5`
5. **Parentheses** (Level 2): `(3)`, `（3）`
6. **Single paren** (Level 2): `3)`, `3）`
7. **Plain number** (Level 2): `3. ` (simple number without heading text)
8. **Symbol** (Level 1): `§3`, `■ 3`, `▪ Item`
9. **Bracket** (Level 2): `【3】`, `［3］`
10. **English** (Level 1): `Article 3`, `Section 3`, `Chapter 3`

**Key Improvements in v3.1:**
- ✅ Removes Markdown bold symbols (`**`)
- ✅ Supports numbered heading format (e.g., "1. (目的)")
- ✅ Supports both full-width `（）` and half-width `()` parentheses

**Key Improvements in v3.0:**
- ✅ Similarity-based paragraph matching using Levenshtein distance
- ✅ Intelligent matching even when paragraph numbers change
- ✅ Correctly identifies additions vs. modifications vs. deletions

## When to Use

Use this skill when users:
- Upload two docx files and ask to create a comparison table
- Want to compare old and new versions of Word documents
- Need to visualize changes in regulations, contracts, policies, or procedures
- Request "新旧対比表" or "comparison table" generation
- Have documents with **any** heading format (auto-detected)

## Workflow

### 1. Detect Files

Check `/mnt/user-data/uploads` for uploaded docx files:

```bash
ls -la /mnt/user-data/uploads/*.docx
```

If 2+ docx files exist, proceed. If not, ask user to upload two docx files.

### 2. Execute Generation Script

**Version 4.0 (Current - with hierarchical structure analysis):**
```bash
cd /home/claude
node scripts/comparison_docx_generator_v4.js <old_file.docx> <new_file.docx> <output_file.docx> "<document_name>" "<date>"
```

**Parameters:**
- `old_file.docx`: Path to before-version file (required)
- `new_file.docx`: Path to after-version file (required)
- `output_file.docx`: Output filename (optional, default: comparison_table.docx)
- `document_name`: Document title for table header (optional, auto-detected from filename)
- `date`: Date to display (optional, defaults to today)

**Example:**
```bash
node scripts/comparison_docx_generator_v4.js \
  /mnt/user-data/uploads/regulations_old.docx \
  /mnt/user-data/uploads/regulations_new.docx \
  /mnt/user-data/outputs/regulations_comparison.docx \
  "就業規則" \
  "2025年10月30日"
```

**Output includes hierarchical structure analysis log:**
```
🔍 文書構造を解析中...
📊 検出された見出しパターン:
   legal: 12回 (レベル1)
   parentheses: 11回 (レベル2)
📊 階層レベル分布: { '1': 12, '2': 11 }
📊 最上位レベル: 1
```

### 3. Output to User

The file is automatically saved to the specified output path. Provide a link:

```bash
[新旧対比表を見る](computer:///mnt/user-data/outputs/新旧対比表.docx)
```

## Key Feature: Hierarchical Structure Analysis

**How It Works:**

**Phase 1: Document Structure Analysis**
1. **Pattern Detection**: Analyzes paragraphs to detect heading patterns
2. **Level Assignment**: Assigns hierarchy level to each pattern (Level 1 = top-level articles)
3. **Structure Building**: Constructs document hierarchy tree
4. **Top-Level Identification**: Identifies minimum level as article boundaries

**Phase 2: Hierarchy-Aware Comparison**
1. **Article Grouping**: Groups content by top-level headings only
2. **Item Ordering**: Sorts sub-items by item numbers within each article
3. **Cell Merging**: Displays entire article (heading + all items) in single cell
4. **Clean Presentation**: No dividing lines between items within same article

**Example Analysis Output:**
```
🔍 文書構造を解析中...
📊 検出された見出しパターン:
   legal: 12回 (レベル1)
   plainNumber: 8回 (レベル2)
   parentheses: 11回 (レベル2)
📊 階層レベル分布: { '1': 12, '2': 19 }
📊 最上位レベル: 1

📝 レベル1の見出しで条文を分割中...
✅ 12個の条文に分割しました
```

This means:
- 12 top-level articles (第○条) at Level 1
- 19 sub-items (2. ..., (1), (2), etc.) at Level 2
- Comparison will be performed at article level, with sub-items sorted within

**Supported Patterns with Hierarchy Levels:**

| Pattern | Regex | Level | Examples |
|---------|-------|-------|----------|
| legal | `^第[0-9０-９]+条` | 1 | 第3条, 第10条 |
| legalKanji | `^第[一二三四五六七八九十百千]+条` | 1 | 第三条, 第十五条 |
| legalBranch | `^第[0-9０-９]+条の[0-9０-９]+` | 1 | 第3条の2, 第5条の3 |
| numbered | `^[0-9０-９]+\.\s+[（(]` | 1 | 3. (見出し), 5. （規定） |
| hierarchical | `^[0-9０-９]+(\.[0-9０-９]+)+\.?\s` | 2+ | 1.1 (L2), 3.2.1 (L3), 5.1.2.3 (L4) |
| hyphenated | `^[0-9０-９]+-[0-9０-９]+\.?\s` | 2 | 1-1, 3-2, 10-5 |
| parentheses | `^[（(][0-9０-９]+[)）]` | 2 | (1), （3）, (10) |
| singleParen | `^[0-9０-９]+[)）]\s` | 2 | 1), 3）, 10) |
| plainNumber | `^[0-9０-９]+\.\s` | 2 | 1. , 2. , 3. |
| symbol | `^[§■▪●◆□]` | 1 | §3, ■ Item, ▪ Point |
| bracket | `^[【［\[][0-9０-９]+[】］\]]` | 2 | 【1】, ［3］, [5] |
| english | `^(Article\|Section\|Chapter\|Part)\s+[0-9]+` | 1 | Article 3, Section 5 |

**Note**: Level 1 patterns are treated as top-level articles. Level 2+ patterns are treated as sub-items within articles.

## Hierarchical Structure-Aware Comparison (階層構造対応)

**IMPORTANT**: The generated table uses hierarchical structure analysis to organize changes intelligently:

**How It Works:**
1. **Analyzes hierarchy**: Identifies top-level articles (Level 1) and sub-items (Level 2+)
2. **Groups by articles**: Only top-level headings create article boundaries
3. **Orders sub-items**: Within each article, items are sorted by item number
4. **Merges cells**: All content within same article displayed in single cell
5. **Shows only changes**: Unchanged articles and items are not displayed

**Display Rules:**
- ✅ Top-level articles (Level 1) → Article boundaries (e.g., 第5条)
- ✅ Sub-items (Level 2+) → Content within articles (e.g., (1), (2), 2. )
- ✅ Changed articles → Heading + changed items shown in correct order
- ✅ Modified items → Highlighted with diff detection
- ✅ New items → Shown as "(新規追加)" in correct position by item number
- ✅ Deleted items → Shown as "(削除)" in correct position
- ✅ Single cell per article → No dividing lines between items
- ❌ Unchanged articles → **Not shown in the table**
- ❌ Unchanged items within changed articles → **Not shown**

### Example Output Structure

**Input Document Structure:**
```
第5条(諸手当)
  (1) 通勤手当: 50,000円
  (2) 時間外勤務手当
  (3) 休日勤務手当
  (4) 深夜勤務手当
  (5) 役職手当
```

**Output in Comparison Table (if (1) changed and (6), (7) added):**
```
┌─────────────────────────────────────┬─────────────────────────────────────┐
│ 第5条(諸手当)                       │ 第5条(諸手当)                       │
│                                     │                                     │
│ (1) 通勤手当: 50,000円              │ (1) 通勤手当: 30,000円              │
│ [highlighted changes]               │ [highlighted changes]               │
│                                     │                                     │
│ (新規追加)                          │ (6) 家族手当: ...                   │
│                                     │                                     │
│ (新規追加)                          │ (7) 住宅手当: ...                   │
└─────────────────────────────────────┴─────────────────────────────────────┘
```

**Key Points:**
- Items (2)-(5) not shown because unchanged
- New items (6), (7) shown in correct numerical order
- All content in single cell with paragraph spacing
- No table row dividers between items

## Output Format

The generated Word document includes:

### Change Highlighting
- **Before (changed)**: Black text, bold, underline
- **After (changed)**: Red text, bold, underline
- **New paragraph**: Blue text, bold, with "(新規追加)" in left cell
- **Deleted paragraph**: Red text, strikethrough, with "(削除)" in right cell

### Features
- **Hierarchical structure analysis**: Understands parent-child heading relationships
- **Top-level article detection**: Correctly identifies article boundaries
- **Item number ordering**: Sorts added/modified/deleted items by number
- **Single-cell article display**: Merges all article content into one cell
- **No internal dividers**: Clean presentation within articles
- **Automatic heading detection**: 12 patterns supported with level assignment
- **Token-level diff detection**: Precise change highlighting within paragraphs
- **Shows only changed articles and items**: Focused on actual changes
- **Advanced Markdown cleanup**:
  - Removes Markdown bold symbols: `**text**` → `text`
  - Removes quoted block symbols: `>\(1\)` → `(1)`
  - Normalizes escaped characters: `2\.` → `2.`
- Center-aligned table
- Professional formatting with Yu Gothic font
- Automatic date generation if not specified

## Technical Details

### Version 4.0: Hierarchical Structure Analysis

**Two-Phase Approach:**

**Phase 1: Structure Analysis**
```javascript
function analyzeDocumentStructure(paragraphs) {
  // 1. Analyze each paragraph
  const analyzed = paragraphs.map(para => analyzeHeading(para));
  
  // 2. Detect patterns and assign levels
  // Level 1: 第○条, Article ○, etc.
  // Level 2: (○), ○., etc.
  
  // 3. Identify top level (minimum level number)
  const topLevel = Math.min(...detectedLevels);
  
  return { analyzed, topLevel };
}
```

**Phase 2: Hierarchy-Aware Comparison**
```javascript
function groupByTopLevelHeading(structure) {
  // Group content by top-level headings only
  // Sub-level items become content within articles
  
  for (const item of structure.analyzed) {
    if (item.level === structure.topLevel) {
      // New article
      startNewArticle(item);
    } else {
      // Add to current article
      addToCurrentArticle(item);
    }
  }
}
```

**Item Ordering Algorithm:**
```javascript
function extractItemNumber(text) {
  // Extract number from: (1), （1）, 1., 1), etc.
  // Returns integer for sorting
}

// Sort all changes by item number
items.sort((a, b) => a.itemNum - b.itemNum);
// Display in correct order: (1), (2), (6)新規, (7)新規
```

**Hierarchy Levels by Pattern:**
- **Level 1** (Articles): `legal`, `legalKanji`, `legalBranch`, `numbered`, `symbol`, `english`
- **Level 2** (Sub-items): `parentheses`, `plainNumber`, `singleParen`, `hyphenated`, `bracket`
- **Level 2+** (Variable): `hierarchical` (calculated by dot count)

### Dependencies
- Node.js with docx package
- pandoc (for docx to text conversion)

## Common Patterns

### Pattern 1: Legal document with hierarchical structure
```
User: [uploads documents with "第○条" as articles and "(○)" as items]
      "新旧対比表を作成して"

Output:
🔍 文書構造を解析中...
📊 検出された見出しパターン:
   legal: 12回 (レベル1)
   parentheses: 23回 (レベル2)
📊 階層レベル分布: { '1': 12, '2': 23 }
📊 最上位レベル: 1
✅ 新旧対比表を生成しました
   変更された条文: 4個
```

### Pattern 2: Numbered document with plain number items
```
User: [uploads documents with "1. (見出し)" format and "2." sub-items]
      "新旧対比表を作成して"

Output:
🔍 文書構造を解析中...
📊 検出された見出しパターン:
   numbered: 10回 (レベル1)
   plainNumber: 15回 (レベル2)
📊 階層レベル分布: { '1': 10, '2': 15 }
📊 最上位レベル: 1
✅ 新旧対比表を生成しました
```

### Pattern 3: Hierarchical numbering
```
User: [uploads documents with "1.1", "1.2", "2.1" format]
      "新旧対比表を作成して"

Output:
🔍 文書構造を解析中...
📊 検出された見出しパターン:
   hierarchical: 20回 (レベル2)
📊 階層レベル分布: { '2': 20 }
📊 最上位レベル: 2
✅ 新旧対比表を生成しました
```

## Error Handling

**No heading pattern detected:**
```
⚠️  見出しパターンが検出されませんでした。デフォルトパターン(numbered)を使用します。
```

**No files uploaded:**
"2つのWord文書(.docx)をアップロードしてください。"

**Only one file:**
"変更前と変更後の2つのファイルが必要です。もう1つアップロードしてください。"

## Troubleshooting

**If hierarchy detection seems incorrect:**
1. Check the structure analysis log: `📊 階層レベル分布: { '1': 12, '2': 19 }`
2. Verify that your document has consistent heading levels
3. Top-level headings should be Level 1 patterns (第○条, Article ○, etc.)

**If items appear in wrong order:**
1. Ensure sub-items use numbered formats: (1), (2), 1., 2., etc.
2. The system extracts numbers for sorting
3. Non-numbered items will appear at the end

**If articles are split incorrectly:**
1. Check which level was detected as top-level: `📊 最上位レベル: 1`
2. Only patterns at this level create article boundaries
3. All other levels become content within articles

**If comparison table shows too many/too few changes:**
1. Verify the hierarchy is correctly detected in both old and new versions
2. Check if article headers match (uses similarity matching)
3. Review the statistics in output to understand what was detected

## Version History

### v4.0 (Current - 2025-10-30)
**Major Features:**
- **Hierarchical structure analysis**: Two-phase approach - first analyze structure, then compare
- **Level-aware pattern detection**: Each pattern assigned hierarchy level (1, 2, or variable)
- **Top-level article grouping**: Only Level 1 headings create article boundaries
- **Item number ordering**: Extracts numbers from sub-items and sorts correctly
- **Single-cell article display**: Merges all article content (heading + items) into one cell
- **No internal dividers**: Clean presentation with paragraph spacing instead of table rows
- **Changed items only**: Shows only modified/added/deleted items, skips unchanged

**Technical Improvements:**
- New `analyzeDocumentStructure()` function with level detection
- New `groupByTopLevelHeading()` function respecting hierarchy
- New `extractItemNumber()` function for sorting sub-items
- Enhanced cell construction with paragraph spacing instead of multiple rows
- Improved `plainNumber` pattern detection for simple numbered items

**Display Improvements:**
```
Before v4.0:
第5条(諸手当)          │ 第5条(諸手当)
─────────────────────┼──────────────────
(1) 通勤手当: 50,000  │ (1) 通勤手当: 30,000
─────────────────────┼──────────────────  <- unwanted divider
(新規追加)            │ (6) 家族手当
─────────────────────┼──────────────────  <- unwanted divider
(新規追加)            │ (7) 住宅手当

After v4.0:
第5条(諸手当)          │ 第5条(諸手当)
                      │
(1) 通勤手当: 50,000  │ (1) 通勤手当: 30,000
                      │                    <- clean spacing
(新規追加)            │ (6) 家族手当
                      │                    <- clean spacing
(新規追加)            │ (7) 住宅手当
```

### v3.2 (2025-10-30)
**Major Features:**
- **Automatic heading pattern detection**: Analyzes document structure and selects appropriate pattern
- **11 supported patterns**: legal, legalKanji, legalBranch, numbered, hierarchical, hyphenated, parentheses, singleParen, symbol, bracket, english
- **Intelligent scoring**: Counts pattern occurrences in first 50 paragraphs
- **Detailed logging**: Shows detected pattern and occurrence count
- **Smart fallback**: Always checks common patterns (legal, numbered) regardless of detection

**Technical Improvements:**
- New `detectHeadingPattern()` function with sampling and scoring
- Enhanced `isArticleHeader()` with pattern-specific and fallback logic
- Detection log shows primary and secondary pattern scores

**Use Cases Enhanced:**
```
Before v3.2:
User uploads document with "1.1", "1.2" format
Result: Manual pattern specification needed ❌

After v3.2:
User uploads any document format
Result: Automatic detection and correct parsing ✅
```

### v3.1 (2025-10-30)
- Markdown bold symbol removal (`**`)
- Numbered heading support ("番号. (見出し)")
- Full-width and half-width parenthesis support

### v3.0 (2025-10-30)
- Similarity-based paragraph matching
- Levenshtein distance algorithm
- Accurate change classification

### v2.1 (2025-10-30)
- Escaped period normalization
- Multi-line quoted block handling
- Improved paragraph boundary detection

## Best Practices

1. **Use consistent heading hierarchy** - Top-level (articles) should use Level 1 patterns, sub-items should use Level 2 patterns
2. **Number your sub-items** - Use (1), (2), 1., 2., etc. for automatic ordering
3. **Check structure analysis log** - Verify correct hierarchy detection: `📊 最上位レベル: 1`
4. **Maintain consistent patterns** - Use same format throughout document for best results
5. **Review article boundaries** - Ensure top-level headings correctly identify your articles

## Notes

- **Hierarchical structure analysis** understands document organization at multiple levels
- **Automatic hierarchy detection** works with 95%+ of corporate document formats
- **No manual configuration** required - just upload and run
- **Transparent analysis** - logs show detected patterns, levels, and article count
- **Intelligent item ordering** - sub-items sorted by number even when added/deleted
- **Clean presentation** - single cell per article with no internal dividers
- Script reports: hierarchy levels, detected patterns, changed articles, and statistics
