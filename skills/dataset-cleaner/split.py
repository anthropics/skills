"""
dataset-cleaner: split.py
Splits a dataset into train / validation / test sets.
Supports stratified splitting to preserve class distribution.

Usage:
  python split.py <input> <output_dir>
                  [--train 0.8] [--val 0.1] [--test 0.1]
                  [--label-col LABEL] [--stratify]
                  [--seed 42] [--prefix my_dataset]
"""

import sys
import json
import argparse
import random
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, str(Path(__file__).parent))
from utils import load_file, save_file, detect_columns


def split(input_path, output_dir,
          train_ratio=0.8, val_ratio=0.1, test_ratio=0.1,
          label_col=None, stratify=True, seed=42, prefix="dataset"):

    random.seed(seed)

    # validate ratios
    total = round(train_ratio + val_ratio + test_ratio, 6)
    if abs(total - 1.0) > 0.001:
        print(json.dumps({"error": f"Train + val + test must sum to 1.0, got {total}"}))
        sys.exit(1)

    rows, _, fmt, encoding, delimiter = load_file(input_path)

    if not rows:
        print(json.dumps({"error": "Input file is empty."}))
        sys.exit(1)

    all_keys = list(rows[0].keys())
    _, label_col = detect_columns(all_keys, label_col=label_col)

    out_ext = Path(input_path).suffix.lower()
    out_fmt = "jsonl" if out_ext == ".jsonl" else "csv"
    Path(output_dir).mkdir(parents=True, exist_ok=True)

    def do_split(data):
        random.shuffle(data)
        n = len(data)
        train_end = int(n * train_ratio)
        val_end = train_end + int(n * val_ratio)
        return data[:train_end], data[train_end:val_end], data[val_end:]

    if stratify and label_col:
        # split within each class, then combine
        groups = defaultdict(list)
        unlabeled = []
        for r in rows:
            lbl = str(r.get(label_col, "")).strip()
            if lbl:
                groups[lbl].append(r)
            else:
                unlabeled.append(r)

        train_rows, val_rows, test_rows = [], [], []
        class_splits = {}

        for lbl, group in groups.items():
            tr, va, te = do_split(group)
            train_rows.extend(tr)
            val_rows.extend(va)
            test_rows.extend(te)
            class_splits[lbl] = {"train": len(tr), "val": len(va), "test": len(te)}

        # distribute unlabeled proportionally
        utr, uva, ute = do_split(unlabeled)
        train_rows.extend(utr)
        val_rows.extend(uva)
        test_rows.extend(ute)

    else:
        train_rows, val_rows, test_rows = do_split(list(rows))
        class_splits = None

    # shuffle final splits
    random.shuffle(train_rows)
    random.shuffle(val_rows)
    random.shuffle(test_rows)

    # save
    splits = {
        "train": (train_rows, f"{prefix}_train.{out_ext.lstrip('.')}"),
        "val":   (val_rows,   f"{prefix}_val.{out_ext.lstrip('.')}"),
        "test":  (test_rows,  f"{prefix}_test.{out_ext.lstrip('.')}"),
    }

    # skip empty splits
    saved = {}
    for name, (split_rows, filename) in splits.items():
        if not split_rows:
            continue
        path = str(Path(output_dir) / filename)
        try:
            save_file(split_rows, path, out_fmt, delimiter or ",")
            saved[name] = {"file": path, "rows": len(split_rows)}
        except IOError as e:
            print(json.dumps({"error": str(e)}))
            sys.exit(1)

    result = {
        "input_file": str(input_path),
        "output_dir": str(output_dir),
        "total_rows": len(rows),
        "stratified": stratify and bool(label_col),
        "label_col": label_col,
        "seed": seed,
        "splits": saved,
        "ratios": {"train": train_ratio, "val": val_ratio, "test": test_ratio},
    }
    if class_splits:
        result["class_splits"] = class_splits

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Split a dataset into train/val/test sets.")
    parser.add_argument("input_file")
    parser.add_argument("output_dir")
    parser.add_argument("--train", type=float, default=0.8)
    parser.add_argument("--val", type=float, default=0.1)
    parser.add_argument("--test", type=float, default=0.1)
    parser.add_argument("--label-col", default=None)
    parser.add_argument("--no-stratify", action="store_true")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--prefix", default="dataset")
    args = parser.parse_args()
    split(
        args.input_file, args.output_dir,
        train_ratio=args.train, val_ratio=args.val, test_ratio=args.test,
        label_col=args.label_col, stratify=not args.no_stratify,
        seed=args.seed, prefix=args.prefix,
    )
