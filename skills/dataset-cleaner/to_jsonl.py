"""
dataset-cleaner: to_jsonl.py
Converts CSV/JSON to training-ready JSONL with schema validation.
Formats: raw, openai (fine-tune), anthropic (Messages API fine-tune).
Validates output against official spec before saving.

Usage:
  python to_jsonl.py <input> <o>
                     [--format raw|openai|anthropic]
                     [--text-col TEXT] [--label-col LABEL]
                     [--system-prompt "You are a helpful assistant."]
                     [--validate]
"""

import sys
import json
import argparse
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from utils import (load_file, save_file, detect_columns,
                   count_tokens, validate_openai_jsonl, validate_anthropic_jsonl)


def convert(input_path, output_path,
            fmt="raw", text_col=None, label_col=None,
            system_prompt=None, validate=True,
            token_model="cl100k_base"):

    rows, parse_errors, in_fmt, encoding, delimiter = load_file(input_path)

    if not rows:
        print(json.dumps({"error": "Input file is empty or could not be parsed."}))
        sys.exit(1)

    all_keys = list(rows[0].keys())
    text_col, label_col = detect_columns(all_keys, text_col, label_col)

    if not text_col:
        print(json.dumps({
            "error": "Could not detect text column. Specify --text-col.",
            "available_columns": all_keys
        }))
        sys.exit(1)

    converted = []
    skipped = 0
    total_tokens = 0
    over_limit = 0

    for r in rows:
        text = str(r.get(text_col, "")).strip()
        label = str(r.get(label_col, "")).strip() if label_col else ""

        if not text:
            skipped += 1
            continue

        tc = count_tokens(text, token_model)
        total_tokens += tc
        if tc > 4096:
            over_limit += 1

        if fmt == "raw":
            out = {text_col: text}
            if label_col and label:
                out[label_col] = label
            converted.append(out)

        elif fmt == "openai":
            messages = []
            if system_prompt:
                messages.append({"role": "system", "content": system_prompt})
            messages.append({"role": "user", "content": text})
            if label:
                messages.append({"role": "assistant", "content": label})
            converted.append({"messages": messages})

        elif fmt == "anthropic":
            messages = [{"role": "user", "content": text}]
            if label:
                messages.append({"role": "assistant", "content": label})
            entry = {"messages": messages}
            if system_prompt:
                entry["system"] = system_prompt
            converted.append(entry)

    if not converted:
        print(json.dumps({"error": "No rows were converted. Check --text-col value."}))
        sys.exit(1)

    # ── Schema validation ─────────────────────────────────────────────────────
    validation_errors = []
    if validate:
        if fmt == "openai":
            validation_errors = validate_openai_jsonl(converted)
        elif fmt == "anthropic":
            validation_errors = validate_anthropic_jsonl(converted)

    if validation_errors:
        print(json.dumps({
            "error": "Output failed schema validation. Fix these issues before uploading for fine-tuning.",
            "validation_errors": validation_errors[:20],
        }, indent=2))
        sys.exit(1)

    # ── Save ──────────────────────────────────────────────────────────────────
    try:
        save_file(converted, output_path, "jsonl")
    except IOError as e:
        print(json.dumps({"error": str(e)}))
        sys.exit(1)

    avg_tokens = round(total_tokens / len(converted), 1) if converted else 0

    print(json.dumps({
        "input_file": str(input_path),
        "output_file": str(output_path),
        "format": fmt,
        "total_input_rows": len(rows),
        "converted_rows": len(converted),
        "skipped_rows": skipped,
        "detected_text_col": text_col,
        "detected_label_col": label_col,
        "system_prompt_used": bool(system_prompt),
        "schema_validated": validate,
        "validation_passed": len(validation_errors) == 0,
        "token_stats": {
            "model": token_model,
            "total_tokens": total_tokens,
            "avg_tokens_per_row": avg_tokens,
            "rows_over_4096_tokens": over_limit,
        },
    }, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert dataset to training-ready JSONL.")
    parser.add_argument("input_file")
    parser.add_argument("output_file")
    parser.add_argument("--format", default="raw", choices=["raw", "openai", "anthropic"])
    parser.add_argument("--text-col", default=None)
    parser.add_argument("--label-col", default=None)
    parser.add_argument("--system-prompt", default=None)
    parser.add_argument("--no-validate", action="store_true", help="Skip schema validation")
    parser.add_argument("--token-model", default="cl100k_base")
    args = parser.parse_args()
    convert(
        args.input_file, args.output_file,
        fmt=args.format,
        text_col=args.text_col, label_col=args.label_col,
        system_prompt=args.system_prompt,
        validate=not args.no_validate,
        token_model=args.token_model,
    )
