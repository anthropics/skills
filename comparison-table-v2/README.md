# Comparison Table Generator v2

Professional comparison table (新旧対比表) generator for Word documents with **hierarchical structure analysis** and **automatic heading pattern detection**.

## Version

Current Version: **v4.0** (2025-10-30)

## Key Features

- 🏗️ **Hierarchical structure analysis**: Understands parent-child heading relationships
- 🎯 **Top-level article detection**: Correctly identifies article boundaries (Level 1 headings)
- 🔢 **Item number ordering**: Sorts sub-items by number within each article
- 📦 **Single-cell article display**: Merges all article content into one clean cell
- ✨ **No internal dividers**: Clean presentation with paragraph spacing
- 🤖 **Automatic pattern detection**: 12 supported formats with level assignment
- 📊 **Similarity-based matching**: Intelligent paragraph matching using Levenshtein distance
- 🎨 **Professional formatting**: Clean, readable Word output

## What's New in v4.0

### Hierarchical Structure Analysis
The system now uses a **two-phase approach**:

**Phase 1: Analyze Structure**
```
🔍 文書構造を解析中...
📊 検出された見出しパターン:
   legal: 12回 (レベル1)      ← Articles
   parentheses: 23回 (レベル2)  ← Sub-items
📊 階層レベル分布: { '1': 12, '2': 23 }
📊 最上位レベル: 1
```

**Phase 2: Compare by Hierarchy**
- Groups content by top-level headings only
- Sorts sub-items by number
- Displays in single cell without dividers

### Smart Item Ordering
```
Before v4.0: Items displayed in order found
(1) Change
(5) Change
(新規) Item 6  ← At end
(新規) Item 7  ← At end

After v4.0: Items sorted by number
(1) Change
(5) Change
(6) Item 6  ← Correct position
(7) Item 7  ← Correct position
```

### Clean Single-Cell Display
```
Before v4.0: Multiple rows with dividers
┌─────────────┬─────────────┐
│ 第5条       │ 第5条       │
├─────────────┼─────────────┤ ← Divider
│ (1) ...     │ (1) ...     │
├─────────────┼─────────────┤ ← Divider
│ (新規)      │ (6) ...     │
└─────────────┴─────────────┘

After v4.0: Single cell, clean spacing
┌─────────────┬─────────────┐
│ 第5条       │ 第5条       │
│             │             │
│ (1) ...     │ (1) ...     │
│             │             │ ← Clean spacing
│ (新規)      │ (6) ...     │
└─────────────┴─────────────┘
```

## Supported Heading Formats (Auto-detected with Levels)

**Level 1 (Articles):**
1. **Legal**: `第3条`, `第三条`, `第3条の2`
2. **Numbered**: `3. (見出し)`, `3. （見出し）`
3. **Symbol**: `§3`, `■ 3`
4. **English**: `Article 3`, `Section 3`

**Level 2 (Sub-items):**
5. **Parentheses**: `(3)`, `（3）`
6. **Plain number**: `3. ` (without heading)
7. **Single paren**: `3)`, `3）`
8. **Hyphenated**: `3-1`, `3-2`
9. **Bracket**: `【3】`, `［3］`

**Level 2+ (Variable):**
10. **Hierarchical**: `3.1` (Level 2), `3.1.1` (Level 3)

## Quick Start

```bash
# Copy scripts to working directory
cp -r /mnt/skills/user/comparison-table-v2/scripts /home/claude/

# Generate comparison table with hierarchical analysis
cd /home/claude
node scripts/comparison_docx_generator_v4.js \
  old_file.docx \
  new_file.docx \
  output.docx \
  "Document Name" \
  "2025年10月30日"
```

## How It Works

1. 📥 **Upload**: Two docx files (old and new versions)
2. 🔍 **Analyze**: System detects patterns and assigns hierarchy levels
3. 🏗️ **Structure**: Identifies top-level articles and sub-items
4. 📊 **Group**: Groups content by top-level headings
5. 🔢 **Sort**: Orders sub-items by number within each article
6. 🔄 **Compare**: Uses similarity matching to find changes
7. 📄 **Generate**: Creates professional comparison table with clean single-cell display

## Requirements

- Node.js
- pandoc
- docx npm package

## Documentation

See `SKILL.md` for complete documentation including:
- Hierarchical structure analysis details
- Pattern detection with level assignment
- Item ordering algorithm
- Technical specifications
- Version history
- Troubleshooting guide

## Version History

- **v4.0** (2025-10-30): Hierarchical structure analysis, item ordering, single-cell display
- **v3.2** (2025-10-30): Automatic heading pattern detection
- **v3.1** (2025-10-30): Markdown cleanup, numbered heading support
- **v3.0** (2025-10-30): Similarity-based matching
- **v2.1** (2025-10-30): Enhanced Markdown cleanup
- **v1.0**: Original release

## License

This skill is provided as-is for use with Claude.
