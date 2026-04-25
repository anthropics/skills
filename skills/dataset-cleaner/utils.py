"""
dataset-cleaner: utils.py
Shared utilities: file I/O, encoding detection, token counting, progress, validation.
"""

import sys
import json
import csv
import os
import hashlib
from pathlib import Path


# ── Encoding detection ─────────────────────────────────────────────────────────

ENCODINGS_TO_TRY = ["utf-8", "utf-8-sig", "latin-1", "cp1252", "utf-16"]

def detect_encoding(path):
    """Try common encodings and return the first one that works."""
    try:
        import chardet
        with open(path, "rb") as f:
            raw = f.read(100_000)
        result = chardet.detect(raw)
        if result["confidence"] > 0.7:
            return result["encoding"]
    except ImportError:
        pass
    for enc in ENCODINGS_TO_TRY:
        try:
            with open(path, "r", encoding=enc) as f:
                f.read(10_000)
            return enc
        except (UnicodeDecodeError, LookupError):
            continue
    return "utf-8"


def detect_delimiter(path, encoding):
    """Detect CSV delimiter: comma, semicolon, tab, or pipe."""
    try:
        with open(path, "r", encoding=encoding, errors="replace") as f:
            sample = f.read(4096)
        dialect = csv.Sniffer().sniff(sample, delimiters=",;\t|")
        return dialect.delimiter
    except csv.Error:
        return ","


# ── File I/O ───────────────────────────────────────────────────────────────────

def load_file(path, show_progress=True):
    """Load CSV or JSONL file. Returns (rows, parse_errors, format, encoding, delimiter)."""
    path = str(path)
    ext = Path(path).suffix.lower()
    encoding = detect_encoding(path)
    parse_errors = []

    if ext == ".jsonl":
        rows = []
        total_bytes = os.path.getsize(path)
        bytes_read = 0
        with open(path, "r", encoding=encoding, errors="replace") as f:
            for i, line in enumerate(f):
                bytes_read += len(line.encode(encoding, errors="replace"))
                line = line.strip()
                if not line:
                    continue
                try:
                    rows.append(json.loads(line))
                except json.JSONDecodeError as e:
                    parse_errors.append({"line": i + 1, "error": str(e), "content": line[:100]})
                if show_progress and i % 10_000 == 0 and i > 0:
                    pct = min(100, int(bytes_read / total_bytes * 100))
                    print(f"[progress] Loading... {pct}%", file=sys.stderr)
        return rows, parse_errors, "jsonl", encoding, None

    elif ext == ".csv":
        delimiter = detect_delimiter(path, encoding)
        rows = []
        with open(path, "r", encoding=encoding, errors="replace", newline="") as f:
            reader = csv.DictReader(f, delimiter=delimiter)
            for i, row in enumerate(reader):
                rows.append(dict(row))
                if show_progress and i % 10_000 == 0 and i > 0:
                    print(f"[progress] Loading... {i:,} rows", file=sys.stderr)
        return rows, parse_errors, "csv", encoding, delimiter

    elif ext == ".json":
        with open(path, "r", encoding=encoding, errors="replace") as f:
            data = json.load(f)
        rows = data if isinstance(data, list) else [data]
        return rows, parse_errors, "json", encoding, None

    else:
        print(json.dumps({"error": f"Unsupported file type '{ext}'. Supported: .csv, .jsonl, .json"}))
        sys.exit(1)


def save_file(rows, path, fmt, delimiter=","):
    """Save rows to CSV or JSONL."""
    path = str(path)
    os.makedirs(Path(path).parent, exist_ok=True)

    if fmt == "jsonl":
        with open(path, "w", encoding="utf-8") as f:
            for row in rows:
                f.write(json.dumps(row, ensure_ascii=False) + "\n")

    elif fmt in ("csv", "json"):
        if not rows:
            open(path, "w").close()
            return
        with open(path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys(), delimiter=delimiter)
            writer.writeheader()
            writer.writerows(rows)

    # verify file was written
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        raise IOError(f"Output file was not written correctly: {path}")


# ── Column auto-detection ──────────────────────────────────────────────────────

TEXT_CANDIDATES  = ["text", "input", "prompt", "content", "sentence", "question", "utterance", "body", "message"]
LABEL_CANDIDATES = ["label", "output", "target", "class", "category", "answer", "response", "intent", "tag"]

def detect_columns(keys, text_col=None, label_col=None):
    """Auto-detect text and label columns from a list of keys."""
    keys_lower = {k.lower(): k for k in keys}
    if not text_col:
        for c in TEXT_CANDIDATES:
            if c in keys_lower:
                text_col = keys_lower[c]
                break
    if not label_col:
        for c in LABEL_CANDIDATES:
            if c in keys_lower:
                label_col = keys_lower[c]
                break
    return text_col, label_col


# ── Token counting ─────────────────────────────────────────────────────────────

_tokenizer_cache = {}

def count_tokens(text, model="cl100k_base"):
    """Count tokens using tiktoken. Falls back to word count if unavailable."""
    try:
        import tiktoken
        if model not in _tokenizer_cache:
            _tokenizer_cache[model] = tiktoken.get_encoding(model)
        return len(_tokenizer_cache[model].encode(str(text)))
    except Exception:
        return len(str(text).split())


# ── Row hashing ────────────────────────────────────────────────────────────────

def row_hash(r):
    return hashlib.md5(json.dumps(r, sort_keys=True, ensure_ascii=False).encode()).hexdigest()

def text_hash(text):
    return hashlib.md5(str(text).lower().strip().encode()).hexdigest()


# ── JSONL validation ───────────────────────────────────────────────────────────

def validate_openai_jsonl(rows):
    """Validate rows against OpenAI fine-tuning JSONL spec."""
    errors = []
    for i, row in enumerate(rows):
        if "messages" not in row:
            errors.append(f"Row {i+1}: missing 'messages' key.")
            continue
        msgs = row["messages"]
        if not isinstance(msgs, list) or len(msgs) < 2:
            errors.append(f"Row {i+1}: 'messages' must be a list with at least 2 items.")
            continue
        roles = [m.get("role") for m in msgs]
        if roles[-1] != "assistant":
            errors.append(f"Row {i+1}: last message must have role 'assistant'.")
        for j, m in enumerate(msgs):
            if "role" not in m or "content" not in m:
                errors.append(f"Row {i+1}, message {j+1}: missing 'role' or 'content'.")
            if m.get("role") not in ("system", "user", "assistant"):
                errors.append(f"Row {i+1}, message {j+1}: invalid role '{m.get('role')}'.")
    return errors


def validate_anthropic_jsonl(rows):
    """Validate rows against Anthropic Messages fine-tuning spec."""
    errors = []
    for i, row in enumerate(rows):
        if "messages" not in row:
            errors.append(f"Row {i+1}: missing 'messages' key.")
            continue
        msgs = row["messages"]
        if not isinstance(msgs, list) or len(msgs) < 2:
            errors.append(f"Row {i+1}: 'messages' must be a list with at least 2 items.")
            continue
        if msgs[0].get("role") != "user":
            errors.append(f"Row {i+1}: first message must have role 'user'.")
        if msgs[-1].get("role") != "assistant":
            errors.append(f"Row {i+1}: last message must have role 'assistant'.")
        for j, m in enumerate(msgs):
            if "role" not in m or "content" not in m:
                errors.append(f"Row {i+1}, message {j+1}: missing 'role' or 'content'.")
            if not str(m.get("content", "")).strip():
                errors.append(f"Row {i+1}, message {j+1}: 'content' is empty.")
    return errors
