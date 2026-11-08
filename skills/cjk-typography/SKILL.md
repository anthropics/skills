---
name: cjk-typography
description: >-
  Enforce CJK (Chinese, Japanese, Korean) typographic rules when generating or editing documents,
  code comments, README files, or any text containing CJK characters. Use this skill whenever
  outputting Chinese, Japanese, or Korean text — including mixed CJK/Latin content. Trigger on
  any writing task involving 中文, 日本語, 한국어, or when the user's locale or language preference
  is CJK. Also apply when reviewing or fixing formatting in existing CJK documents.
license: MIT
---

# CJK Typography Rules

Apply these rules whenever generating or editing text that contains CJK (Chinese, Japanese, Korean) characters. These rules prevent common AI-generated text issues that look unprofessional to native CJK readers.

## 1. Spacing Between CJK and Half-Width Characters

Insert exactly **one space** between CJK characters and adjacent half-width characters (Latin letters, digits, symbols). This is known as "pangu spacing" (盤古之白).

**Rules:**
- CJK + Latin letter: `中文 English 混排` not `中文English混排`
- CJK + number: `共 5 個` not `共5個`
- CJK + inline code: `使用 `npm install` 安裝` not `使用`npm install`安裝`

**Exceptions — no space needed:**
- Between CJK and CJK punctuation: `你好，世界` not `你好 ，世界`
- Between CJK and percent/degree when reading as a unit: `100%` or `36°C` (no space after the number is also acceptable)
- Inside proper nouns that have established no-space conventions

## 2. Punctuation

### Use fullwidth CJK punctuation in CJK sentences

| Use | Don't use | Context |
|-----|-----------|---------|
| `，` | `,` | Chinese comma |
| `。` | `.` | Chinese period |
| `；` | `;` | Chinese semicolon |
| `：` | `:` | Chinese colon |
| `！` | `!` | Chinese exclamation |
| `？` | `?` | Chinese question mark |
| `「」` | `""` | CJK quotation marks (primary) |
| `『』` | `''` | CJK quotation marks (nested) |
| `（）` | `()` | Chinese parentheses in prose |
| `——` | `--` | Chinese em-dash (two consecutive) |
| `……` | `...` | Chinese ellipsis (two consecutive) |

**When to use halfwidth punctuation:**
- Inside code blocks, file paths, URLs, and technical identifiers
- Inside English sentences within a CJK document
- In Markdown syntax elements (lists, links, headings)

### Japanese-specific
- Use `。` and `、` (not `．` and `，`) in standard prose
- Quotation marks: `「」` for primary, `『』` for nested (same as Chinese)

### Korean-specific
- Use halfwidth period `.` and comma `,` in modern Korean (South Korean standard)
- Quotation marks: `""` and `''` are standard; `「」` is also acceptable

## 3. No Consecutive Spaces or Trailing Whitespace

- Never insert multiple consecutive spaces between CJK characters
- Never leave trailing whitespace on lines containing CJK text
- Exception: Markdown indentation for lists and code blocks is fine

## 4. Line Breaks and Paragraph Structure

- Do NOT insert line breaks in the middle of a CJK sentence for "readability" — CJK text does not word-wrap at spaces
- In Markdown, use blank lines between paragraphs, not hard line breaks within paragraphs
- Do not indent the first line of CJK paragraphs (unlike traditional print typography)

## 5. Numbers and Units

- Use halfwidth (ASCII) digits: `2026` not `２０２６`
- Use halfwidth for units commonly written in Latin: `100MB`, `3.5GHz`
- Percentages: `85%` (halfwidth percent sign)
- Currencies: `$100`、`¥500`、`₩10000` — use the appropriate currency symbol

## 6. Mixed-Language Documents

When a document mixes CJK with full English sentences:

- English sentences use English punctuation
- CJK sentences use CJK punctuation
- The punctuation follows the language of the sentence, not the document
- When an English word or phrase is embedded in a CJK sentence, use CJK punctuation for the sentence's own punctuation marks

**Example:**
```
Claude Code 是 Anthropic 推出的 CLI 工具，支援多種程式語言。
The tool supports Python, JavaScript, and more.
他說：「這個 API 很好用。」
```

## 7. Technical Writing Conventions

- Keep technical terms, brand names, and proper nouns in their original form: `GitHub`、`TypeScript`、`Claude Code`
- Do not translate or transliterate widely recognized English technical terms
- File paths, commands, and code remain in halfwidth: `npm install`、`/usr/local/bin`
- Use backtick fences for inline code in Markdown, with pangu spacing around them

## 8. Common AI Mistakes to Avoid

1. **Halfwidth punctuation in CJK sentences** — The most frequent error. Always use fullwidth `，。！？` in Chinese/Japanese prose.
2. **Missing pangu spacing** — `今天是2026年` should be `今天是 2026 年`.
3. **Inconsistent quotation marks** — Don't mix `""` and `「」` within the same CJK document. Pick one style and stick with it.
4. **Random fullwidth letters/digits** — Never use `Ａ` `Ｂ` `１` `２`. Always use halfwidth `A` `B` `1` `2`.
5. **Orphaned punctuation** — CJK punctuation must not appear at the start of a new line (use the previous line's end instead).
6. **Over-translating** — Don't translate `React`、`API`、`CLI` into CJK equivalents when the English term is standard in the field.
