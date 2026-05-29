---
name: dataset-cleaner
description: >
  Clean, validate, balance, split, and format datasets for AI/ML training and fine-tuning.
  Use this skill whenever a user has a dataset (CSV or JSONL) they want to prepare for model
  training or fine-tuning. Automatically detects and fixes: duplicate rows, label noise, class
  imbalance, missing values, encoding corruption, empty texts, over-length rows, and schema
  inconsistencies. Converts to training-ready JSONL for OpenAI or Anthropic fine-tuning with
  full schema validation. Handles large files, non-UTF-8 encodings, and non-standard delimiters.
  Trigger for: "clean my dataset", "prepare data for fine-tuning", "fix class imbalance",
  "convert to JSONL", "my training data has duplicates", "validate my training data",
  "label noise in my dataset", "split into train and test", or any time a user wants to improve
  data quality before training or fine-tuning an AI model.
---

# Dataset Cleaner

A complete pipeline for cleaning and preparing AI training datasets.
Five Python scripts handle every stage. Always run via bash — never reimplement their logic.

## Scripts

| Script | Purpose |
|--------|---------|
| `scripts/utils.py` | Shared utilities — auto-loaded by all scripts, never call directly |
| `scripts/inspect.py` | Full quality audit: duplicates, label noise, class imbalance, token lengths, encoding issues |
| `scripts/clean.py` | Remove duplicates, empty rows, label noise, encoding corruption; filter by token length |
| `scripts/balance.py` | Fix class imbalance via oversample / undersample / hybrid strategy |
| `scripts/to_jsonl.py` | Convert to training-ready JSONL with schema validation (raw / OpenAI / Anthropic format) |
| `scripts/split.py` | Stratified train / val / test split |

**Supported formats**: `.csv`, `.jsonl`, `.json`
**Supported encodings**: auto-detected (UTF-8, UTF-8-BOM, Latin-1, CP1252, UTF-16)
**Supported delimiters**: auto-detected (comma, semicolon, tab, pipe)

---

## Install dependencies

```bash
pip install pandas tiktoken --break-system-packages
```

---

## Standard Workflow

### Step 1 — Copy uploaded file
```bash
cp /mnt/user-data/uploads/<filename> /home/claude/<filename>
```

### Step 2 — Inspect
```bash
python scripts/inspect.py /home/claude/<filename>
# With options:
python scripts/inspect.py /home/claude/<filename> --max-tokens 512 --token-model cl100k_base
```

Parse the JSON output and report to the user:
- `total_rows`, `encoding_detected`, `columns`
- `issues` — critical blockers that **must** be fixed before training
- `warnings` — non-critical issues worth reviewing
- `stats.label_distribution` + `stats.class_imbalance_ratio`
- `stats.token_analysis` — p50/p95/p99 token counts, over-limit rows
- `summary.ready_for_training` — true/false
- `summary.recommended_actions` — exact commands to run next

**Always run inspect first. Never skip.**

### Step 3 — Clean
```bash
python scripts/clean.py /home/claude/<file> /home/claude/<file>_cleaned.<ext>
```

Options:
```
--text-col TEXT        Text column name (auto-detected if omitted)
--label-col LABEL      Label column name (auto-detected if omitted)
--drop-short N         Drop rows with fewer than N tokens
--drop-long N          Drop rows exceeding N tokens (use inspect p95/p99 as guide)
--no-dedup             Skip duplicate removal
--no-drop-empty-text   Keep rows with empty text
--no-drop-empty-label  Keep rows with empty labels
--no-label-noise       Skip label noise removal
--token-model MODEL    Tiktoken model (default: cl100k_base)
```

Report every item in `changes` to the user in plain language.

### Step 4 — Balance (only if imbalance ratio > 3)
```bash
# Oversample minority classes — best for small datasets
python scripts/balance.py /home/claude/<file>_cleaned.<ext> /home/claude/<file>_balanced.<ext> \
  --label-col <label_col> --strategy oversample

# Undersample majority classes — use when dataset is large (100k+)
python scripts/balance.py ... --strategy undersample

# Hybrid: geometric mean — balanced middle ground
python scripts/balance.py ... --strategy hybrid
```

Report `original_distribution` → `final_distribution` and `improvement` ratio.

### Step 5 — Split
```bash
python scripts/split.py /home/claude/<file>_balanced.<ext> /home/claude/splits/ \
  --train 0.8 --val 0.1 --test 0.1 --prefix my_dataset
```

Stratified by default — preserves class distribution in each split.
Output: `my_dataset_train.csv`, `my_dataset_val.csv`, `my_dataset_test.csv`

### Step 6 — Convert to JSONL (for fine-tuning)
```bash
# OpenAI fine-tuning format
python scripts/to_jsonl.py /home/claude/splits/my_dataset_train.csv /home/claude/train.jsonl \
  --format openai --system-prompt "You are a helpful assistant."

# Anthropic Messages API format
python scripts/to_jsonl.py /home/claude/splits/my_dataset_train.csv /home/claude/train.jsonl \
  --format anthropic --system-prompt "You are a helpful assistant."
```

Schema is validated automatically before saving.
If `validation_passed` is false, fix the listed errors before uploading.

### Step 7 — Deliver output files
```bash
cp /home/claude/train.jsonl /mnt/user-data/outputs/
cp /home/claude/splits/my_dataset_val.csv /mnt/user-data/outputs/
```

Use `present_files` to share all output files.

---

## Full pipeline example (one-liner chain)

```bash
python scripts/inspect.py /home/claude/data.csv && \
python scripts/clean.py /home/claude/data.csv /home/claude/data_clean.csv --drop-long 512 && \
python scripts/balance.py /home/claude/data_clean.csv /home/claude/data_balanced.csv --label-col label && \
python scripts/split.py /home/claude/data_balanced.csv /home/claude/splits/ --prefix data && \
python scripts/to_jsonl.py /home/claude/splits/data_train.csv /home/claude/train.jsonl --format anthropic
```

---

## Output report to user

Structure your final response as:

**Dataset Audit**
- File name, row count, encoding detected, columns found
- Every issue found — explain what it means, why it hurts training
- Every warning — explain the risk

**Cleaning Summary**
- Rows removed and exact reason for each
- Before → after counts

**Class Balance** (if run)
- Distribution table before and after
- Ratio improvement

**Train / Val / Test Split**
- Row counts per split
- Whether stratified

**Final Output**
- File list with row counts and formats
- Token stats: avg, p50, p95, total tokens
- `ready_for_training: true/false` verdict

**Next Steps**
- Specific fine-tuning recommendations based on dataset size:
  - < 50 rows: too small, suggest data collection strategies
  - 50–500 rows: few-shot or LoRA fine-tuning
  - 500–10k rows: standard fine-tuning
  - 10k+ rows: full fine-tuning, consider data augmentation

---

## Important rules

- Always run `inspect.py` first — never clean blind.
- Clean before balancing — duplicates skew class counts.
- Balance before splitting — ensures all splits get representative samples.
- Split before converting — convert each split separately (train, val).
- If `ready_for_training` is already `true` after inspect, tell the user and skip cleaning.
- Translate every technical finding into plain language the user can act on.
- Never guess column names — scripts auto-detect; only specify manually if auto-detection fails.
