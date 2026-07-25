#!/usr/bin/env python3
"""Template for DOE analysis from an experiment_plan.csv file."""

from __future__ import annotations

import json
from pathlib import Path

import pandas as pd


CSV_PATH = Path("experiment_plan.csv")
FACTORS = ["factor_A", "factor_B", "factor_C", "factor_D"]
RESPONSE = "response_1"
OUTPUT_PATH = Path("analysis_results.json")


def range_analysis(df: pd.DataFrame, factors: list[str], response: str) -> dict:
    grand_mean = float(df[response].mean())
    results = []
    for factor in factors:
        means = df.groupby(factor)[response].mean()
        results.append(
            {
                "factor": factor,
                "level_means": {str(k): float(v) for k, v in means.items()},
                "range": float(means.max() - means.min()),
            }
        )
    results.sort(key=lambda item: item["range"], reverse=True)
    return {"grand_mean": grand_mean, "factors": results}


def main() -> int:
    df = pd.read_csv(CSV_PATH)
    required = [*FACTORS, RESPONSE]
    missing = [column for column in required if column not in df.columns]
    if missing:
        raise SystemExit(f"Missing columns: {', '.join(missing)}")
    clean = df.dropna(subset=[RESPONSE])
    if clean.empty:
        raise SystemExit(f"No numeric response data found in {RESPONSE}")
    result = range_analysis(clean, FACTORS, RESPONSE)
    OUTPUT_PATH.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"Wrote {OUTPUT_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
