"""Orthogonal experiment analysis: range analysis, ANOVA, optimal prediction."""

import argparse
import json
import sys

import numpy as np
import pandas as pd
from scipy import stats


def range_analysis(df: pd.DataFrame, factors: list[str], response: str) -> dict:
    """Compute range analysis (极差分析) for an orthogonal experiment.

    Returns dict with grand_mean and per-factor K, k, R values sorted by R descending.
    """
    grand_mean = df[response].mean()
    result_factors = []

    for factor in factors:
        level_means = df.groupby(factor)[response].mean()
        level_sums = df.groupby(factor)[response].sum()
        level_counts = df.groupby(factor)[response].count()
        r = level_means.max() - level_means.min()

        result_factors.append({
            "factor": factor,
            "K": {str(k): float(v) for k, v in level_sums.items()},
            "k": {str(k): float(v) for k, v in level_means.items()},
            "R": float(r),
            "n": {str(k): int(v) for k, v in level_counts.items()},
        })

    result_factors.sort(key=lambda x: x["R"], reverse=True)
    return {"grand_mean": float(grand_mean), "factors": result_factors}


def anova_analysis(
    df: pd.DataFrame, factors: list[str], response: str, alpha: float = 0.05
) -> dict:
    """Single-factor ANOVA for each factor with F-test.

    For each factor: SS, df, MS, F, F_critical, significant flag.
    Error is computed as residual (SS_T - sum of factor SS).
    """
    y = df[response].values
    n = len(y)
    cf = y.sum() ** 2 / n  # correction factor
    ss_t = (y**2).sum() - cf

    factor_results = []
    ss_factor_sum = 0.0

    for factor in factors:
        groups = [g[response].values for _, g in df.groupby(factor)]
        a = len(groups)
        group_sizes = [len(g) for g in groups]
        if len(set(group_sizes)) > 1:
            raise ValueError(
                f"factor '{factor}' has unbalanced level sizes: {group_sizes}. "
                "anova_analysis requires equal replicates per level."
            )
        ni = group_sizes[0]
        if ni == 0:
            raise ValueError(f"factor '{factor}' has an empty level")
        k_j = np.array([g.sum() for g in groups])
        ss_f = float((k_j**2).sum() / ni - cf)
        df_f = a - 1
        ms_f = ss_f / df_f if df_f > 0 else 0.0

        factor_results.append({
            "factor": factor,
            "SS": ss_f,
            "df": df_f,
            "MS": ms_f,
            "levels": a,
        })
        ss_factor_sum += ss_f

    ss_e = ss_t - ss_factor_sum
    df_total = n - 1
    df_error = df_total - sum(r["df"] for r in factor_results)
    ms_e = ss_e / df_error if df_error > 0 else float("inf")

    for r in factor_results:
        f_val = r["MS"] / ms_e if ms_e > 0 else float("inf")
        f_crit = float(stats.f.ppf(1 - alpha, r["df"], df_error))
        r["F"] = f_val
        r["F_critical"] = f_crit
        r["significant"] = f_val > f_crit
        r["p_value"] = float(stats.f.sf(f_val, r["df"], df_error))

    return {
        "SS_total": ss_t,
        "SS_error": ss_e,
        "df_total": df_total,
        "df_error": df_error,
        "MS_error": ms_e,
        "alpha": alpha,
        "factors": factor_results,
    }


def predict_optimal(
    df: pd.DataFrame,
    factors: list[str],
    response: str,
    goal: str = "max",
) -> dict:
    """Predict the optimal factor-level combination.

    goal: 'max' (larger-is-better), 'min' (smaller-is-best), or 'target' (nominal-is-best).
    Returns optimal levels and predicted response.
    """
    grand_mean = df[response].mean()
    optimal_levels = {}
    adjustments = []

    for factor in factors:
        level_means = df.groupby(factor)[response].mean()
        if goal == "max":
            best_level = level_means.idxmax()
        elif goal == "min":
            best_level = level_means.idxmin()
        else:
            best_level = (level_means - grand_mean).abs().idxmin()

        best_mean = level_means[best_level]
        optimal_levels[factor] = str(best_level)
        adjustments.append(best_mean - grand_mean)

    predicted = grand_mean + sum(adjustments)
    return {
        "optimal_levels": optimal_levels,
        "predicted_response": float(predicted),
        "grand_mean": float(grand_mean),
        "goal": goal,
    }


def main():
    parser = argparse.ArgumentParser(description="Orthogonal experiment analysis")
    parser.add_argument("csv_file", help="Path to experiment CSV file")
    parser.add_argument(
        "--factors", "-f", nargs="+", required=True, help="Factor column names"
    )
    parser.add_argument("--response", "-r", required=True, help="Response column name")
    parser.add_argument(
        "--goal",
        "-g",
        choices=["max", "min", "target"],
        default="max",
        help="Optimization goal (default: max)",
    )
    parser.add_argument(
        "--alpha", "-a", type=float, default=0.05, help="Significance level (default: 0.05)"
    )
    parser.add_argument(
        "--output", "-o", help="Output JSON file (default: stdout)"
    )
    args = parser.parse_args()

    df = pd.read_csv(args.csv_file)

    ra = range_analysis(df, args.factors, args.response)
    anova = anova_analysis(df, args.factors, args.response, args.alpha)
    optimal = predict_optimal(df, args.factors, args.response, args.goal)

    result = {
        "range_analysis": ra,
        "anova": anova,
        "optimal_prediction": optimal,
    }

    output = json.dumps(result, indent=2, ensure_ascii=False)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output)
    else:
        print(output)


if __name__ == "__main__":
    main()
