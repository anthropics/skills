"""
dataset-cleaner: clean.py
Cleans a dataset (CSV or JSONL) for AI training.
Fixes: duplicates, empty rows, label noise, encoding corruption,
whitespace, and over/under length rows (by token count).

Usage:
  python clean.py <input> <output>
                  [--text-col TEXT] [--label-col LABEL]
                  [--drop-short N]  [--drop-long N]
                  [--no-dedup] [--no-drop-empty-text] [--no-drop-empty-label]
                  [--no-fix-encoding] [--no-label-noise]
                  [--token-model cl100k_base]
"""

import sys
import json
import argparse
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from utils import load_file, save_file, detect_columns, count_tokens, row_hash, text_hash


def clean(input_path, output_path,
          text_col=None, label_col=None,
          drop_duplicates=True, drop_empty_text=True, drop_empty_label=True,
          drop_short=None, drop_long=None,
          fix_encoding=True, remove_label_noise=True,
          token_model="cl100k_base"):

    rows, parse_errors, fmt, encoding, delimiter = load_file(input_path)
    original_count = len(rows)
    log = []

    if not rows:
        print(json.dumps({"error": "Input file is empty or could not be parsed."}))
        sys.exit(1)

    all_keys = list(rows[0].keys())
    text_col, label_col = detect_columns(all_keys, text_col, label_col)

    # ── Fix encoding corruption ───────────────────────────────────────────────
    if fix_encoding:
        fixed_fields = 0
        for r in rows:
            for k, v in r.items():
                if isinstance(v, str) and "\ufffd" in v:
                    r[k] = v.replace("\ufffd", "").strip()
                    fixed_fields += 1
        if fixed_fields:
            log.append(f"Fixed encoding corruption in {fixed_fields} field(s).")

    # ── Strip whitespace ──────────────────────────────────────────────────────
    stripped = 0
    for r in rows:
        for k, v in r.items():
            if isinstance(v, str):
                clean_v = v.strip()
                if clean_v != v:
                    r[k] = clean_v
                    stripped += 1
    if stripped:
        log.append(f"Stripped leading/trailing whitespace from {stripped} field(s).")

    # ── Drop empty text ───────────────────────────────────────────────────────
    if drop_empty_text and text_col:
        before = len(rows)
        rows = [r for r in rows if str(r.get(text_col, "")).strip()]
        dropped = before - len(rows)
        if dropped:
            log.append(f"Dropped {dropped} rows with empty '{text_col}'.")

    # ── Drop empty labels ─────────────────────────────────────────────────────
    if drop_empty_label and label_col:
        before = len(rows)
        rows = [r for r in rows if str(r.get(label_col, "")).strip()]
        dropped = before - len(rows)
        if dropped:
            log.append(f"Dropped {dropped} rows with empty '{label_col}'.")

    # ── Drop short texts (by token count) ────────────────────────────────────
    if drop_short is not None and text_col:
        before = len(rows)
        rows = [r for r in rows
                if count_tokens(str(r.get(text_col, "")), token_model) >= drop_short]
        dropped = before - len(rows)
        if dropped:
            log.append(f"Dropped {dropped} rows with fewer than {drop_short} tokens in '{text_col}'.")

    # ── Drop long texts (by token count) ─────────────────────────────────────
    if drop_long is not None and text_col:
        before = len(rows)
        rows = [r for r in rows
                if count_tokens(str(r.get(text_col, "")), token_model) <= drop_long]
        dropped = before - len(rows)
        if dropped:
            log.append(f"Dropped {dropped} rows exceeding {drop_long} tokens in '{text_col}'.")

    # ── Remove exact duplicates ───────────────────────────────────────────────
    if drop_duplicates:
        before = len(rows)
        seen = set()
        deduped = []
        for r in rows:
            h = row_hash(r)
            if h not in seen:
                seen.add(h)
                deduped.append(r)
        rows = deduped
        dropped = before - len(rows)
        if dropped:
            log.append(f"Removed {dropped} exact duplicate rows.")

    # ── Remove label noise ────────────────────────────────────────────────────
    if remove_label_noise and text_col and label_col:
        text_to_labels = {}
        for r in rows:
            th = text_hash(str(r.get(text_col, "")))
            lbl = str(r.get(label_col, "")).strip()
            if th not in text_to_labels:
                text_to_labels[th] = set()
            if lbl:
                text_to_labels[th].add(lbl)
        noisy = {th for th, lbls in text_to_labels.items() if len(lbls) > 1}
        if noisy:
            before = len(rows)
            rows = [r for r in rows
                    if text_hash(str(r.get(text_col, ""))) not in noisy]
            dropped = before - len(rows)
            log.append(
                f"Removed {dropped} rows with label noise "
                f"({len(noisy)} texts had conflicting labels)."
            )

    # ── Save ──────────────────────────────────────────────────────────────────
    out_ext = Path(output_path).suffix.lower()
    out_fmt = "jsonl" if out_ext == ".jsonl" else "csv"
    try:
        save_file(rows, output_path, out_fmt, delimiter or ",")
    except IOError as e:
        print(json.dumps({"error": str(e)}))
        sys.exit(1)

    print(json.dumps({
        "input_file": str(input_path),
        "output_file": str(output_path),
        "original_rows": original_count,
        "cleaned_rows": len(rows),
        "rows_removed": original_count - len(rows),
        "removal_pct": round((original_count - len(rows)) / original_count * 100, 2) if original_count else 0,
        "detected_text_col": text_col,
        "detected_label_col": label_col,
        "token_model_used": token_model,
        "changes": log if log else ["No issues found — dataset was already clean."],
    }, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Clean a dataset for AI training.")
    parser.add_argument("input_file")
    parser.add_argument("output_file")
    parser.add_argument("--text-col", default=None)
    parser.add_argument("--label-col", default=None)
    parser.add_argument("--drop-short", type=int, default=None, help="Drop rows with fewer than N tokens")
    parser.add_argument("--drop-long", type=int, default=None, help="Drop rows exceeding N tokens")
    parser.add_argument("--no-dedup", action="store_true")
    parser.add_argument("--no-drop-empty-text", action="store_true")
    parser.add_argument("--no-drop-empty-label", action="store_true")
    parser.add_argument("--no-fix-encoding", action="store_true")
    parser.add_argument("--no-label-noise", action="store_true")
    parser.add_argument("--token-model", default="cl100k_base")
    args = parser.parse_args()

    clean(
        args.input_file, args.output_file,
        text_col=args.text_col, label_col=args.label_col,
        drop_duplicates=not args.no_dedup,
        drop_empty_text=not args.no_drop_empty_text,
        drop_empty_label=not args.no_drop_empty_label,
        drop_short=args.drop_short, drop_long=args.drop_long,
        fix_encoding=not args.no_fix_encoding,
        remove_label_noise=not args.no_label_noise,
        token_model=args.token_model,
    )
