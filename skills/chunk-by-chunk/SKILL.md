---
name: chunk-by-chunk
author: Saimonokuma
date_added: '2026-05-22'
description: Write large outputs in sequential chunks to avoid token limits while delivering maximum quality
when-to-use: When generating any output that could exceed token limits (large documents, code files, analysis reports, variant specs)
user-invocable: true
effort: high
---

# Chunk-by-Chunk Skill

**Purpose:** Prevent token limit failures by splitting large outputs into sequential file writes. Ensures no content is lost, no quality is sacrificed, and the full deliverable is always completed.

---

## ⚠️ SAFE RULES — MANDATORY, NO EXCEPTIONS

```
╔═══════════════════════════════════════════════════════════════════╗
║                                                                   ║
║     "HITTING THE EDGE? DO IT CHUNK BY CHUNK."                     ║
║                                                                   ║
║     This is not a suggestion. This is a SAFE RULE.                ║
║     Whenever you sense the output growing large —                 ║
║     STOP, PLAN, CHUNK, WRITE, VERIFY.                             ║
║                                                                   ║
╚═══════════════════════════════════════════════════════════════════╝
```

### The 5 Safe Rules

**SAFE RULE 1: DETECT EARLY**
> Before generating ANY output, estimate its size. If it could exceed 150 lines
> of markdown or 250 lines of code — activate chunk-by-chunk IMMEDIATELY.
> Don't wait for the error. Anticipate it.

**SAFE RULE 2: NEVER TRUNCATE**
> A truncated deliverable is a FAILED deliverable. If you cannot fit it in one
> response, you MUST split it into chunks. There is no excuse for incomplete work.
> The user paid for the full output — deliver every last line.

**SAFE RULE 3: CHUNK = QUALITY**
> Chunking is not a compromise — it is a QUALITY MULTIPLIER. When you write in
> chunks, each chunk gets your full attention. Each section is polished. Each
> table is complete. Each code block is verified. Chunk-by-chunk delivers
> BETTER work than trying to rush everything into one output.

**SAFE RULE 4: ALWAYS VERIFY**
> After writing all chunks, you MUST verify the assembled file. Check the first
> lines, check the last lines, check the total line count. If anything is missing
> or duplicated — fix it before telling the user you're done.

**SAFE RULE 5: COMMUNICATE**
> Tell the user what you're doing: "Writing chunk 1 of 3..." / "Appending chunk 2..."
> Transparency builds trust. The user should never wonder why multiple writes are
> happening — they should see the progress and feel confident.

### Perfect Writing Principles

Chunk-by-chunk is also a **writing quality framework**:

| Principle | How Chunking Helps |
|-----------|-------------------|
| **Depth over breadth** | Each chunk gets full attention — no rushing to "fit it all in" |
| **Complete sections** | Every table is whole, every code block is closed, every list is finished |
| **No filler** | When you have room to write properly, you don't need padding or shortcuts |
| **Structured delivery** | Logical section order, consistent formatting, professional output |
| **Iterative refinement** | You can review chunk 1 before writing chunk 2 — catch mistakes early |

### When These Rules Activate

These rules are **ALWAYS ACTIVE** but trigger with extra urgency when:

- ❗ A token limit error occurred in this conversation
- ❗ The document has 10+ sections or 20+ items to detail
- ❗ You're generating code files over 200 lines
- ❗ You're building specs, configs, or variant definitions
- ❗ You're writing analysis reports with data tables
- ❗ You feel ANY pressure to "shorten" or "summarize" to fit

**If you feel the urge to shorten your work to fit — THAT is the signal to chunk.**



## Core Philosophy

```
┌─────────────────────────────────────────────────────────────────┐
│  NEVER LET TOKEN LIMITS TRUNCATE YOUR WORK                      │
│  ─────────────────────────────────────────────────────────────  │
│  Large outputs are not a problem — they are an opportunity      │
│  to deliver MORE detail, MORE quality, MORE value.              │
│                                                                 │
│  When output might be large:                                    │
│  1. PLAN the structure first (outline in your head)             │
│  2. SPLIT into logical chunks (sections, not arbitrary cuts)    │
│  3. WRITE each chunk to file sequentially                       │
│  4. VERIFY the final assembled file is complete                 │
│                                                                 │
│  The user should NEVER see a truncated or incomplete output.    │
│  The user should NEVER get a "token limit exceeded" error.      │
└─────────────────────────────────────────────────────────────────┘
```

---

## When to Activate

Activate this skill PROACTIVELY when you detect any of these conditions:

| Signal | Action |
|--------|--------|
| Document with 10+ sections | Split into 2-3 chunks |
| Document with 20+ sections | Split into 3-5 chunks |
| Code file over 200 lines | Split into logical blocks |
| Table with 20+ rows of detail | Write table in its own chunk |
| Multiple detailed variant/config specs | Group 5-10 per chunk |
| Research report with data + analysis + recommendations | 3 chunks: data → analysis → recommendations |
| Any previous token limit error in conversation | ALWAYS chunk from now on |

---

## Chunking Strategy

### Step 1: Plan Before Writing

Before writing ANY large document, create a mental outline:

```
Document: "20 TH Variants"
├── Chunk 1: Header + Architecture + Variants 1-10
├── Chunk 2: Variants 11-20
└── Chunk 3: Reference tables + selection guide + appendix
```

### Step 2: Choose the Right Chunk Boundaries

**DO** split at:
- Section boundaries (## headers)
- Logical groups (variants 1-10, then 11-20)
- Topic transitions (data → analysis → recommendations)
- Natural breaks (intro → body → reference)

**DON'T** split at:
- Mid-sentence or mid-paragraph
- Inside a table or code block
- Between a heading and its content
- In the middle of a logical group

### Step 3: Write Sequentially

```
Chunk 1: write_to_file (creates file)
Chunk 2: replace_file_content (appends at end)
Chunk 3: replace_file_content (appends at end)
Final:   view_file (verify completeness)
```

### Step 4: Verify Assembly

After all chunks are written:
1. View the file start (first 5 lines) to confirm header
2. View the file end (last 5 lines) to confirm footer
3. Check total line count matches expectation

---

## Implementation Patterns

### Pattern 1: New Document (write + append)

```
# First chunk — create the file
write_to_file:
  TargetFile: path/to/document.md
  Overwrite: true
  CodeContent: [Header + first major section]

# Second chunk — append
replace_file_content:
  TargetFile: path/to/document.md
  TargetContent: [last unique line of chunk 1]
  ReplacementContent: [last line of chunk 1 + all of chunk 2]
  StartLine: [last line number]
  EndLine: [last line number]

# Third chunk — append again
replace_file_content:
  TargetFile: path/to/document.md
  TargetContent: [last unique line of chunk 2]
  ReplacementContent: [last line of chunk 2 + all of chunk 3]
  StartLine: [new last line]
  EndLine: [new last line]
```

### Pattern 2: Overwrite Existing (chunk rebuild)

```
# When rebuilding a large file, write chunk 1 with Overwrite: true
# Then append subsequent chunks using replace_file_content
```

### Pattern 3: Code Generation

```
# For large code files:
# Chunk 1: imports + constants + first class/function group
# Chunk 2: second class/function group
# Chunk 3: third class/function group + exports
```

---

## Sizing Guidelines

| Content Type | Max Lines Per Chunk | Notes |
|-------------|:---:|-------|
| Markdown documentation | 150-200 lines | Split at ## headers |
| Code (TypeScript/Python) | 200-300 lines | Split at class/function boundaries |
| Tables | 30-40 rows | Keep header row with each chunk |
| Pine Script | 150-250 lines | Split at function boundaries |
| JSON/Config | 100-150 lines | Split at top-level keys |
| Mixed (code + docs) | 150 lines | Most conservative |

---

## Quality Rules

### Rule 1: Never Sacrifice Quality for Chunking
Chunking exists to ENABLE more detail, not to reduce it. Each chunk should be as detailed and polished as if it were the entire document.

### Rule 2: Maintain Context Across Chunks
Each chunk should reference what came before and set up what comes next. The reader should never feel a "seam" between chunks.

### Rule 3: Verify After Assembly
Always check the final file:
- Total line count is reasonable
- First and last lines are correct
- No duplicate content at chunk boundaries
- No missing content between chunks

### Rule 4: Communicate Progress
Tell the user what you're doing:
- "Writing chunk 1 of 3 (variants 1-10)..."
- "Now appending chunk 2 (variants 11-20)..."
- "Final chunk — reference tables and guide..."

### Rule 5: Handle Failures Gracefully
If a chunk write fails:
1. View the file to see what was written
2. Identify the gap
3. Re-attempt just the missing chunk
4. Never re-write the entire file

---

## Anti-Patterns

### ❌ Don't: Try to Write Everything at Once
```
# BAD: 500-line document in one write_to_file
write_to_file:
  CodeContent: [500 lines of content]
# → Token limit error, everything lost
```

### ✅ Do: Split Proactively
```
# GOOD: 3 chunks of 150-170 lines each
write_to_file: [chunk 1: 170 lines]
replace_file_content: [chunk 2: 160 lines]
replace_file_content: [chunk 3: 170 lines]
# → Complete 500-line document, no limits hit
```

### ❌ Don't: Split Arbitrarily
```
# BAD: Splitting mid-table
Chunk 1: | Header1 | Header2 |
         | row1    | data    |
         | row2    | da---   ← SPLIT HERE
Chunk 2: ta       |          ← BROKEN
```

### ✅ Do: Split at Logical Boundaries
```
# GOOD: Complete sections in each chunk
Chunk 1: [Full Section 1 + Full Section 2]
Chunk 2: [Full Section 3 + Full Section 4]
```

### ❌ Don't: Forget to Verify
```
# BAD: Write 3 chunks and move on
# What if chunk 2 had an error? You'd never know.
```

### ✅ Do: Always Verify
```
# GOOD: After all chunks, check the file
view_file: [check first 5 lines]
view_file: [check last 5 lines]
# Confirm: total lines = expected, content is complete
```

---

## Quick Reference

### Chunk Planning Formula
```
Total estimated lines ÷ 170 = Number of chunks needed
Round UP, never down.
```

### Chunk Boundary Checklist
Before splitting at a point, confirm:
- [ ] Not inside a code block
- [ ] Not inside a table
- [ ] Not between a heading and its content
- [ ] The last line of the chunk is unique (for targeting)
- [ ] The chunk is self-contained logically

### Emergency Recovery
If you hit a token limit despite chunking:
1. Your chunks were too large — use smaller chunks next time
2. Check what was written successfully
3. Continue from where it stopped
4. Never restart from scratch — build on what exists
