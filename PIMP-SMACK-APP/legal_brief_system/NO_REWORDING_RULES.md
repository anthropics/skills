# CRITICAL: NO AI REWORDING RULES

## What This System Does

1. **Loads your exact text** from JSON/CSV files
2. **Assembles it** into the correct brief structure
3. **Adds citations and footnotes** automatically
4. **Validates** for compliance

## What This System Does NOT Do

❌ Reword your facts  
❌ "Improve" your writing  
❌ Summarize then expand (the fluff problem)  
❌ Process PDFs with AI  
❌ Run multiple subprocesses that modify text  

---

## Your Data Flow

```
┌─────────────────────────────────────────────────────────────┐
│  YOUR SOURCE FILES (exact text)                             │
│                                                             │
│  ECF_QUOTES.csv  ←  Your extracted quotes (exact)           │
│  evidence_pool.json  ←  Your facts (exact)                  │
│  authorities.json  ←  Your citations (exact)                │
└─────────────────────────────────────────────────────────────┘
                              │
                              │ (NO MODIFICATION)
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  ASSEMBLY (structure only)                                  │
│                                                             │
│  - Places text in correct sections                          │
│  - Adds citation formatting                                 │
│  - Creates footnotes from cross-references                  │
│  - Validates compliance                                     │
└─────────────────────────────────────────────────────────────┘
                              │
                              │ (EXACT OUTPUT)
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  OUTPUT FILES                                               │
│                                                             │
│  Your words, properly formatted                             │
│  Citations attached to facts                                │
│  Cross-references as footnotes                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Commands

### `tyler_cmd.bat`

| Command                         | What It Does                    |
| ------------------------------- | ------------------------------- |
| `tyler_cmd extract [pdf] [txt]` | Extract PDF text (exact, no AI) |
| `tyler_cmd quotes`              | Show your ECF quotes            |
| `tyler_cmd validate`            | Check data for errors           |
| `tyler_cmd build`               | Build brief from evidence       |

### Batch Files (Double-Click)

| File                      | Purpose                |
| ------------------------- | ---------------------- |
| `VALIDATE.bat`            | Check everything       |
| `BUILD_FROM_EVIDENCE.bat` | Assemble brief         |
| `GENERATE_FILING.bat`     | Create final documents |

---

## If AI Tries to Reword Your Text

The system is designed to prevent this, but if you see:
- Your quotes being paraphrased
- "Summarized" versions of your facts
- Expanded/fluffed text

**STOP** and check:
1. Is the text coming from your JSON files? (Good)
2. Is AI generating new text? (Bad - fix the prompt)

Your JSON files are the **source of truth**. The system should only:
- Read from them
- Format them
- Assemble them

Never rewrite them.

---

## PDF Extraction

PDFs are extracted using `extract_pdf.py` which:
1. Reads raw text from PDF
2. Preserves page numbers
3. Outputs to .txt file
4. **NO AI PROCESSING**

Then YOU review the .txt and copy exact quotes to your JSON files.

The AI never touches your PDFs directly.
