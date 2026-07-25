#!/usr/bin/env python3
"""Summarize experimental data from CSV files with descriptive statistics and outlier detection."""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd


def compute_statistics(series: pd.Series) -> dict:
    """Compute descriptive statistics for a numeric series."""
    clean = series.dropna()
    if clean.empty:
        return {
            "count": 0,
            "mean": None,
            "std": None,
            "min": None,
            "max": None,
            "median": None,
            "Q1": None,
            "Q3": None,
            "CV_percent": None,
        }

    count = int(clean.count())
    mean = float(clean.mean())
    std = float(clean.std(ddof=1)) if count > 1 else 0.0
    min_val = float(clean.min())
    max_val = float(clean.max())
    median = float(clean.median())
    q1 = float(clean.quantile(0.25))
    q3 = float(clean.quantile(0.75))
    cv = (std / mean * 100) if mean != 0 else None

    return {
        "count": count,
        "mean": mean,
        "std": std,
        "min": min_val,
        "max": max_val,
        "median": median,
        "Q1": q1,
        "Q3": q3,
        "CV_percent": cv,
    }


def detect_outliers_iqr(series: pd.Series) -> pd.Series:
    """Detect outliers using the IQR method. Returns a boolean mask (True = outlier)."""
    clean = series.dropna()
    if clean.empty:
        return pd.Series(dtype=bool)

    q1 = clean.quantile(0.25)
    q3 = clean.quantile(0.75)
    iqr = q3 - q1
    lower = q1 - 1.5 * iqr
    upper = q3 + 1.5 * iqr
    return series.notna() & ((series < lower) | (series > upper))


def detect_outliers_zscore(series: pd.Series, threshold: float = 3.0) -> pd.Series:
    """Detect outliers using the Z-score method. Returns a boolean mask (True = outlier)."""
    clean = series.dropna()
    if clean.empty or clean.std(ddof=1) == 0:
        return pd.Series(False, index=series.index)

    mean = clean.mean()
    std = clean.std(ddof=1)
    z_scores = (series - mean).abs() / std
    return series.notna() & (z_scores > threshold)


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    parser = argparse.ArgumentParser(
        description="Summarize experimental data from CSV with descriptive statistics and outlier detection."
    )
    parser.add_argument("input", help="Path to the input CSV file")
    parser.add_argument(
        "--group-by",
        required=True,
        help="Column name to group data by (e.g., sample_id, formulation_id)",
    )
    parser.add_argument(
        "--value-column",
        required=True,
        help="Column name containing the numeric values to analyze",
    )
    parser.add_argument(
        "--outliers",
        choices=["iqr", "zscore"],
        default=None,
        help="Outlier detection method: 'iqr' (IQR method) or 'zscore' (Z-score method). "
        "If not specified, only summary statistics are computed.",
    )
    parser.add_argument(
        "--zscore-threshold",
        type=float,
        default=3.0,
        help="Z-score threshold for outlier detection (default: 3.0)",
    )
    parser.add_argument(
        "--output",
        required=True,
        help="Output file path. Use .json extension for JSON report, .csv for CSV summary.",
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file '{input_path}' does not exist.", file=sys.stderr)
        return 1

    try:
        df = pd.read_csv(input_path)
    except Exception as e:
        print(f"Error reading CSV: {e}", file=sys.stderr)
        return 1

    group_col = args.group_by
    value_col = args.value_column

    if group_col not in df.columns:
        print(f"Error: Group column '{group_col}' not found in CSV. Available columns: {list(df.columns)}", file=sys.stderr)
        return 1

    if value_col not in df.columns:
        print(f"Error: Value column '{value_col}' not found in CSV. Available columns: {list(df.columns)}", file=sys.stderr)
        return 1

    # Try to convert value column to numeric
    df[value_col] = pd.to_numeric(df[value_col], errors="coerce")

    output_path = Path(args.output)
    output_format = output_path.suffix.lower()

    if args.outliers is not None:
        # Outlier detection mode
        if args.outliers == "iqr":
            df["is_outlier"] = df.groupby(group_col)[value_col].transform(detect_outliers_iqr)
        else:
            df["is_outlier"] = df.groupby(group_col)[value_col].transform(
                lambda x: detect_outliers_zscore(x, threshold=args.zscore_threshold)
            )

        outlier_df = df[df["is_outlier"]].copy()

        if output_format == ".json":
            result = {}
            for group_name, group_df in outlier_df.groupby(group_col):
                group_key = str(group_name)
                result[group_key] = group_df[[group_col, value_col]].to_dict(orient="records")
            with output_path.open("w", encoding="utf-8") as f:
                json.dump(result, f, indent=2, default=str)
        else:
            # CSV output
            out_cols = [group_col, value_col]
            outlier_df[out_cols].to_csv(output_path, index=False, encoding="utf-8-sig")

        print(f"Outlier detection ({args.outliers}) complete. Found {len(outlier_df)} outlier(s). Output: {output_path}")

    else:
        # Summary statistics mode
        grouped = df.groupby(group_col)[value_col]
        stats = grouped.apply(compute_statistics).reset_index()

        # Flatten the statistics dict into columns
        stats_records = []
        for _, row in stats.iterrows():
            record = {group_col: row[group_col]}
            record.update(row[value_col])
            stats_records.append(record)

        stats_df = pd.DataFrame(stats_records)

        if output_format == ".json":
            result = {}
            for record in stats_records:
                group_key = str(record[group_col])
                result[group_key] = {k: v for k, v in record.items() if k != group_col}
            with output_path.open("w", encoding="utf-8") as f:
                json.dump(result, f, indent=2, default=str)
        else:
            stats_df.to_csv(output_path, index=False, encoding="utf-8-sig")

        print(f"Summary statistics computed for {len(stats_records)} group(s). Output: {output_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
