"""
dataset-cleaner: balance.py
Fixes class imbalance in AI training datasets.
Strategies: oversample (random), undersample (random), hybrid (geometric mean).
For text data, oversampling uses simple duplication — pair with augmentation
tools for richer synthetic samples.

Usage:
  python balance.py <input> <output> --label-col LABEL
                    [--strategy oversample|undersample|hybrid]
                    [--seed 42]
"""

import sys
import json
import argparse
import random
from pathlib import Path
from collections import Counter, defaultdict

sys.path.insert(0, str(Path(__file__).parent))
from utils import load_file, save_file, detect_columns


def balance(input_path, output_path, label_col=None, strategy="oversample", seed=42):
    random.seed(seed)
    rows, _, fmt, encoding, delimiter = load_file(input_path)

    if not rows:
        print(json.dumps({"error": "Input file is empty."}))
        sys.exit(1)

    all_keys = list(rows[0].keys())
    _, label_col = detect_columns(all_keys, label_col=label_col)

    if not label_col:
        print(json.dumps({"error": "Could not detect label column. Specify --label-col."}))
        sys.exit(1)

    # partition rows into labeled groups
    groups = defaultdict(list)
    unlabeled = []
    for r in rows:
        lbl = str(r.get(label_col, "")).strip()
        if lbl:
            groups[lbl].append(r)
        else:
            unlabeled.append(r)

    if not groups:
        print(json.dumps({"error": "No labeled rows found."}))
        sys.exit(1)

    counts = Counter({k: len(v) for k, v in groups.items()})
    max_n = counts.most_common(1)[0][1]
    min_n = counts.most_common()[-1][1]
    original_dist = dict(counts.most_common())
    original_ratio = round(max_n / min_n, 2) if min_n > 0 else float("inf")

    if strategy == "oversample":
        target = max_n
        balanced = []
        for lbl, group in groups.items():
            if len(group) < target:
                extra = target - len(group)
                group = group + random.choices(group, k=extra)
            balanced.extend(group)

    elif strategy == "undersample":
        target = min_n
        balanced = []
        for lbl, group in groups.items():
            balanced.extend(random.sample(group, target))

    elif strategy == "hybrid":
        import math
        target = max(min_n, int(math.sqrt(max_n * min_n)))
        balanced = []
        for lbl, group in groups.items():
            if len(group) > target:
                balanced.extend(random.sample(group, target))
            elif len(group) < target:
                extra = target - len(group)
                balanced.extend(group + random.choices(group, k=extra))
            else:
                balanced.extend(group)
    else:
        print(json.dumps({"error": f"Unknown strategy '{strategy}'. Use: oversample, undersample, hybrid"}))
        sys.exit(1)

    random.shuffle(balanced)
    balanced.extend(unlabeled)

    out_ext = Path(output_path).suffix.lower()
    out_fmt = "jsonl" if out_ext == ".jsonl" else "csv"
    try:
        save_file(balanced, output_path, out_fmt, delimiter or ",")
    except IOError as e:
        print(json.dumps({"error": str(e)}))
        sys.exit(1)

    final_counts = Counter(str(r.get(label_col, "")).strip() for r in balanced if str(r.get(label_col, "")).strip())
    final_min = min(final_counts.values())
    final_max = max(final_counts.values())
    final_ratio = round(final_max / final_min, 2) if final_min > 0 else 1.0

    print(json.dumps({
        "input_file": str(input_path),
        "output_file": str(output_path),
        "strategy": strategy,
        "label_col": label_col,
        "seed": seed,
        "original_distribution": original_dist,
        "final_distribution": dict(final_counts.most_common()),
        "original_total": len(rows),
        "final_total": len(balanced),
        "original_imbalance_ratio": original_ratio,
        "final_imbalance_ratio": final_ratio,
        "improvement": f"{original_ratio}:1 → {final_ratio}:1",
    }, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Balance class distribution in a training dataset.")
    parser.add_argument("input_file")
    parser.add_argument("output_file")
    parser.add_argument("--label-col", default=None)
    parser.add_argument("--strategy", default="oversample", choices=["oversample", "undersample", "hybrid"])
    parser.add_argument("--seed", type=int, default=42)
    args = parser.parse_args()
    balance(args.input_file, args.output_file, args.label_col, args.strategy, args.seed)
