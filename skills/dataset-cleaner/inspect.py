"""
dataset-cleaner: inspect.py
Full quality audit for AI training datasets.
Detects: duplicates, label noise, class imbalance, missing values,
token length issues, encoding corruption, malformed rows, schema problems.

Usage:
  python inspect.py <file> [--text-col TEXT] [--label-col LABEL]
                           [--token-model cl100k_base] [--max-tokens 512]
"""

import sys
import json
import argparse
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path(__file__).parent))
from utils import load_file, detect_columns, count_tokens, row_hash, text_hash


def inspect(path, text_col=None, label_col=None, token_model="cl100k_base", max_tokens=512):
    rows, parse_errors, fmt, encoding, delimiter = load_file(path)

    report = {
        "file": Path(path).name,
        "format": fmt,
        "encoding_detected": encoding,
        "total_rows": len(rows),
        "parse_errors": parse_errors[:10],  # cap at 10
        "issues": [],
        "warnings": [],
        "stats": {},
        "columns": [],
    }

    if parse_errors:
        report["issues"].append(f"{len(parse_errors)} rows failed to parse — file may be malformed.")

    if not rows:
        report["issues"].append("File is empty or could not be parsed.")
        report["summary"] = {"total_issues": 1, "total_warnings": 0, "ready_for_training": False}
        print(json.dumps(report, indent=2))
        return

    all_keys = list(rows[0].keys())
    report["columns"] = all_keys
    text_col, label_col = detect_columns(all_keys, text_col, label_col)
    report["detected_text_col"] = text_col
    report["detected_label_col"] = label_col

    # ── Missing values ────────────────────────────────────────────────────────
    missing_by_col = {}
    for key in all_keys:
        count = sum(1 for r in rows if not str(r.get(key, "")).strip())
        if count > 0:
            pct = round(count / len(rows) * 100, 2)
            missing_by_col[key] = {"count": count, "pct": pct}
            target = "issues" if pct > 10 else "warnings"
            report[target].append(f"'{key}' has {pct}% missing values ({count} rows).")
    report["stats"]["missing_values"] = missing_by_col

    # ── Exact duplicates ──────────────────────────────────────────────────────
    hashes = [row_hash(r) for r in rows]
    dup_count = len(hashes) - len(set(hashes))
    report["stats"]["duplicate_rows"] = dup_count
    if dup_count > 0:
        pct = round(dup_count / len(rows) * 100, 2)
        report["issues"].append(f"{dup_count} exact duplicate rows ({pct}% of dataset).")

    # ── Label noise ───────────────────────────────────────────────────────────
    if text_col and label_col:
        text_to_labels = {}
        for r in rows:
            th = text_hash(str(r.get(text_col, "")))
            lbl = str(r.get(label_col, "")).strip()
            if th not in text_to_labels:
                text_to_labels[th] = set()
            if lbl:
                text_to_labels[th].add(lbl)
        noisy_texts = {th for th, lbls in text_to_labels.items() if len(lbls) > 1}
        noisy_rows = sum(1 for r in rows if text_hash(str(r.get(text_col, ""))) in noisy_texts)
        report["stats"]["label_noise_rows"] = noisy_rows
        report["stats"]["label_noise_texts"] = len(noisy_texts)
        if noisy_rows > 0:
            report["issues"].append(
                f"{noisy_rows} rows have label noise — same text mapped to multiple labels "
                f"({len(noisy_texts)} unique texts affected). This will directly hurt model accuracy."
            )

    # ── Class imbalance ───────────────────────────────────────────────────────
    if label_col:
        labels = [str(r.get(label_col, "")).strip() for r in rows if str(r.get(label_col, "")).strip()]
        label_counts = Counter(labels)
        report["stats"]["label_distribution"] = dict(label_counts.most_common())
        report["stats"]["num_classes"] = len(label_counts)

        if label_counts:
            most_n = label_counts.most_common(1)[0][1]
            least_n = label_counts.most_common()[-1][1]
            ratio = round(most_n / least_n, 2) if least_n > 0 else float("inf")
            report["stats"]["class_imbalance_ratio"] = ratio

            if ratio > 10:
                report["issues"].append(
                    f"Severe class imbalance (ratio {ratio}:1). "
                    f"Most common: '{label_counts.most_common(1)[0][0]}' ({most_n}), "
                    f"least common: '{label_counts.most_common()[-1][0]}' ({least_n}). "
                    "Model will be heavily biased toward majority class."
                )
            elif ratio > 3:
                report["warnings"].append(
                    f"Moderate class imbalance (ratio {ratio}:1). Consider running balance.py."
                )

        empty_labels = sum(1 for r in rows if not str(r.get(label_col, "")).strip())
        if empty_labels > 0:
            report["issues"].append(f"{empty_labels} rows have empty or missing labels.")

    # ── Token analysis ────────────────────────────────────────────────────────
    over_limit = 0
    if text_col:
        token_counts = []
        empty_texts = 0
        for r in rows:
            t = str(r.get(text_col, "")).strip()
            if not t:
                empty_texts += 1
                token_counts.append(0)
            else:
                token_counts.append(count_tokens(t, token_model))

        over_limit = sum(1 for tc in token_counts if tc > max_tokens)
        very_short = sum(1 for tc in token_counts if 0 < tc < 5)
        sorted_tc = sorted(token_counts)
        n = len(sorted_tc)

        report["stats"]["token_analysis"] = {
            "tokenizer": token_model,
            "max_tokens_threshold": max_tokens,
            "min": sorted_tc[0],
            "max": sorted_tc[-1],
            "mean": round(sum(token_counts) / n, 1),
            "p50": sorted_tc[n // 2],
            "p95": sorted_tc[int(n * 0.95)],
            "p99": sorted_tc[int(n * 0.99)],
            "empty_texts": empty_texts,
            "over_limit": over_limit,
            "very_short_under_5_tokens": very_short,
        }

        if empty_texts > 0:
            report["issues"].append(f"{empty_texts} rows have empty text in '{text_col}'.")
        if over_limit > 0:
            pct = round(over_limit / n * 100, 1)
            report["warnings"].append(
                f"{over_limit} rows ({pct}%) exceed {max_tokens} tokens and will be truncated by most tokenizers."
            )
        if very_short > 0:
            report["warnings"].append(f"{very_short} rows have fewer than 5 tokens — likely junk or noise.")

    # ── Encoding corruption ───────────────────────────────────────────────────
    encoding_issues = sum(1 for r in rows if any("\ufffd" in str(v) for v in r.values()))
    report["stats"]["encoding_issues"] = encoding_issues
    if encoding_issues > 0:
        report["issues"].append(
            f"{encoding_issues} rows contain Unicode replacement characters — encoding corruption."
        )

    # ── Schema consistency ────────────────────────────────────────────────────
    expected_keys = set(all_keys)
    schema_errors = sum(1 for r in rows if set(r.keys()) != expected_keys)
    report["stats"]["schema_inconsistencies"] = schema_errors
    if schema_errors > 0:
        report["issues"].append(f"{schema_errors} rows have inconsistent schema (missing or extra columns).")

    # ── Summary + recommendations ─────────────────────────────────────────────
    actions = []
    if dup_count > 0 or report["stats"].get("label_noise_rows", 0) > 0:
        actions.append("Run clean.py to remove duplicates and label noise.")
    if report["stats"].get("class_imbalance_ratio", 1) > 3:
        actions.append("Run balance.py to fix class imbalance.")
    if over_limit > 0:
        actions.append(f"Run clean.py --drop-long {max_tokens} to remove over-limit rows.")

    report["summary"] = {
        "total_issues": len(report["issues"]),
        "total_warnings": len(report["warnings"]),
        "ready_for_training": len(report["issues"]) == 0,
        "recommended_actions": actions,
    }

    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Audit a dataset for AI training quality issues.")
    parser.add_argument("file")
    parser.add_argument("--text-col", default=None)
    parser.add_argument("--label-col", default=None)
    parser.add_argument("--token-model", default="cl100k_base")
    parser.add_argument("--max-tokens", type=int, default=512)
    args = parser.parse_args()
    inspect(args.file, args.text_col, args.label_col, args.token_model, args.max_tokens)
