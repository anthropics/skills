# dataset-cleaner

A complete pipeline for cleaning, validating, balancing, splitting, and formatting text datasets for AI model training and fine-tuning.

Works on any labeled text dataset — sentiment analysis, intent classification, spam detection, Q&A pairs, chatbot training data, and more. If your data has a text column and a label column, this skill handles it.

---

## What it does

Takes a raw, messy dataset and produces clean, validated, training-ready files in five steps:

1. **Inspect** — full quality audit before touching anything
2. **Clean** — remove duplicates, label noise, empty rows, encoding corruption
3. **Balance** — fix class imbalance so your model does not favor the majority class
4. **Split** — stratified train / val / test split
5. **Convert** — export to JSONL with schema validation for OpenAI or Anthropic fine-tuning

---

## Scripts

| File | Purpose |
|------|---------|
| `scripts/utils.py` | Shared utilities — encoding detection, file I/O, token counting, schema validation |
| `scripts/inspect.py` | Audit dataset for issues before cleaning |
| `scripts/clean.py` | Fix duplicates, label noise, encoding, whitespace, length issues |
| `scripts/balance.py` | Fix class imbalance via oversample, undersample, or hybrid |
| `scripts/split.py` | Stratified train / val / test split |
| `scripts/to_jsonl.py` | Convert to training-ready JSONL with schema validation |

---

## Supported formats

- Input: `.csv`, `.jsonl`, `.json`
- Output: `.csv`, `.jsonl`
- Encodings: auto-detected (UTF-8, UTF-8-BOM, Latin-1, CP1252, UTF-16)
- Delimiters: auto-detected (comma, semicolon, tab, pipe)

---

## Installation

```bash
pip install tiktoken pandas
```

All other dependencies (`json`, `csv`, `hashlib`, `collections`, `random`) are Python standard library.

---

## Usage

### Inspect
```bash
python scripts/inspect.py data.csv
python scripts/inspect.py data.csv --max-tokens 512 --token-model cl100k_base
```

### Clean
```bash
python scripts/clean.py data.csv data_clean.csv
python scripts/clean.py data.csv data_clean.csv --drop-long 512 --drop-short 5
```

### Balance
```bash
python scripts/balance.py data_clean.csv data_balanced.csv --label-col label --strategy oversample
python scripts/balance.py data_clean.csv data_balanced.csv --label-col label --strategy undersample
python scripts/balance.py data_clean.csv data_balanced.csv --label-col label --strategy hybrid
```

### Split
```bash
python scripts/split.py data_balanced.csv ./splits/ --train 0.8 --val 0.1 --test 0.1 --prefix my_dataset
```

### Convert to JSONL
```bash
# Anthropic fine-tuning format
python scripts/to_jsonl.py splits/my_dataset_train.csv train.jsonl \
  --format anthropic --system-prompt "You are a helpful assistant."

# OpenAI fine-tuning format
python scripts/to_jsonl.py splits/my_dataset_train.csv train.jsonl \
  --format openai --system-prompt "You are a helpful assistant."
```

### Full pipeline
```bash
python scripts/inspect.py data.csv && \
python scripts/clean.py data.csv data_clean.csv --drop-long 512 && \
python scripts/balance.py data_clean.csv data_balanced.csv --label-col label && \
python scripts/split.py data_balanced.csv ./splits/ --prefix data && \
python scripts/to_jsonl.py splits/data_train.csv train.jsonl --format anthropic
```

---

## What it detects

- Exact duplicate rows
- Label noise — same text mapped to multiple different labels
- Class imbalance with severity ratio
- Missing values per column
- Empty text or label fields
- Token length distribution (min, max, mean, p50, p95, p99)
- Rows exceeding tokenizer limits
- Unicode encoding corruption
- Schema inconsistencies across rows
- Malformed JSONL rows

---

## Output formats

**raw** — preserves original columns, outputs clean JSONL

**openai** — OpenAI fine-tuning format:
```json
{"messages": [{"role": "system", "content": "..."}, {"role": "user", "content": "..."}, {"role": "assistant", "content": "..."}]}
```

**anthropic** — Anthropic Messages API format:
```json
{"system": "...", "messages": [{"role": "user", "content": "..."}, {"role": "assistant", "content": "..."}]}
```

Both formats are validated against the official spec before saving.

---

## Column auto-detection

Text and label columns are detected automatically from common naming patterns.

Text column candidates: `text`, `input`, `prompt`, `content`, `sentence`, `question`, `utterance`, `body`, `message`

Label column candidates: `label`, `output`, `target`, `class`, `category`, `answer`, `response`, `intent`, `tag`

To override: `--text-col my_column --label-col my_label`

---

## Who this is for

- Developers fine-tuning language models for the first time
- Researchers preparing labeled classification datasets
- Teams where multiple annotators labeled the same data (label noise is common)
- Anyone whose fine-tuning job failed or performed poorly due to data quality issues

---

## Recommended dataset sizes for fine-tuning

| Size | Recommendation |
|------|---------------|
| Under 50 rows | Too small — collect more data first |
| 50 to 500 rows | Few-shot prompting or LoRA fine-tuning |
| 500 to 10,000 rows | Standard fine-tuning |
| Over 10,000 rows | Full fine-tuning, consider data augmentation |