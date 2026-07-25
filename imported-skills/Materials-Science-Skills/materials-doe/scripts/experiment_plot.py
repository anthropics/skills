"""Experiment visualization: factor-response, range bar, dosage-performance plots."""

import argparse
import sys
from pathlib import Path

# Ensure sibling DOE scripts are importable regardless of CWD.
_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd


def plot_factor_response(
    df: pd.DataFrame,
    factors: list[str],
    response: str,
    output_path: str,
) -> str:
    """Plot main effects (factor-response) for each factor.

    One subplot per factor showing level means with connecting line.
    Returns output_path.
    """
    n = len(factors)
    fig, axes = plt.subplots(1, n, figsize=(5 * n, 4), squeeze=False)

    for i, factor in enumerate(factors):
        ax = axes[0, i]
        level_means = df.groupby(factor)[response].mean()
        levels = level_means.index.tolist()
        means = level_means.values

        ax.plot(range(len(levels)), means, "o-", linewidth=2, markersize=8, color="#2563eb")
        ax.set_xticks(range(len(levels)))
        ax.set_xticklabels([str(l) for l in levels])
        ax.set_xlabel(factor, fontsize=11)
        ax.set_ylabel(f"Mean {response}", fontsize=11)
        ax.set_title(f"Main Effect: {factor}", fontsize=12, fontweight="bold")
        ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(output_path, dpi=300, bbox_inches="tight")
    plt.close(fig)
    return output_path


def plot_range_bar(
    ranges: dict[str, float],
    output_path: str,
) -> str:
    """Plot bar chart of R values (range analysis) sorted descending.

    ranges: {factor_name: R_value}
    Returns output_path.
    """
    sorted_items = sorted(ranges.items(), key=lambda x: x[1], reverse=True)
    names = [x[0] for x in sorted_items]
    values = [x[1] for x in sorted_items]

    fig, ax = plt.subplots(figsize=(max(6, len(names) * 1.5), 4))
    colors = ["#2563eb" if i == 0 else "#93c5fd" for i in range(len(names))]
    bars = ax.bar(names, values, color=colors, edgecolor="#1e40af", linewidth=0.8)

    for bar, val in zip(bars, values):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.01 * max(values),
                f"{val:.3f}", ha="center", va="bottom", fontsize=10)

    ax.set_xlabel("Factor", fontsize=11)
    ax.set_ylabel("Range R", fontsize=11)
    ax.set_title("Range Analysis", fontsize=12, fontweight="bold")
    ax.grid(axis="y", alpha=0.3)

    fig.tight_layout()
    fig.savefig(output_path, dpi=300, bbox_inches="tight")
    plt.close(fig)
    return output_path


def plot_dosage_performance(
    df: pd.DataFrame,
    dosage_col: str,
    response_col: str,
    output_path: str,
) -> str:
    """Plot dosage-performance curve with optimum marker.

    Returns output_path.
    """
    x = df[dosage_col].values
    y = df[response_col].values

    idx_max = np.argmax(y)
    idx_min = np.argmin(y)

    fig, ax = plt.subplots(figsize=(7, 5))
    ax.plot(x, y, "o-", linewidth=2, markersize=7, color="#2563eb", label="Measured")
    ax.plot(x[idx_max], y[idx_max], "^", markersize=14, color="#dc2626",
            label=f"Max: {y[idx_max]:.2f}", zorder=5)
    ax.plot(x[idx_min], y[idx_min], "v", markersize=14, color="#16a34a",
            label=f"Min: {y[idx_min]:.2f}", zorder=5)

    ax.set_xlabel(dosage_col, fontsize=11)
    ax.set_ylabel(response_col, fontsize=11)
    ax.set_title("Dosage–Performance Curve", fontsize=12, fontweight="bold")
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    fig.tight_layout()
    fig.savefig(output_path, dpi=300, bbox_inches="tight")
    plt.close(fig)
    return output_path


def main():
    parser = argparse.ArgumentParser(description="Experiment plotting")
    sub = parser.add_subparsers(dest="command")

    p1 = sub.add_parser("factor-response", help="Main effects plot")
    p1.add_argument("csv_file", help="Experiment CSV")
    p1.add_argument("--factors", "-f", nargs="+", required=True)
    p1.add_argument("--response", "-r", required=True)
    p1.add_argument("--output", "-o", required=True, help="Output image path")

    p2 = sub.add_parser("range-bar", help="Range analysis bar chart")
    p2.add_argument("csv_file", help="Experiment CSV")
    p2.add_argument("--factors", "-f", nargs="+", required=True)
    p2.add_argument("--response", "-r", required=True)
    p2.add_argument("--output", "-o", required=True, help="Output image path")

    p3 = sub.add_parser("dosage-performance", help="Dosage-performance curve")
    p3.add_argument("csv_file", help="Experiment CSV")
    p3.add_argument("--dosage", "-d", required=True, help="Dosage column")
    p3.add_argument("--response", "-r", required=True, help="Response column")
    p3.add_argument("--output", "-o", required=True, help="Output image path")

    args = parser.parse_args()

    if args.command == "factor-response":
        df = pd.read_csv(args.csv_file)
        plot_factor_response(df, args.factors, args.response, args.output)
        print(f"Saved: {args.output}")

    elif args.command == "range-bar":
        df = pd.read_csv(args.csv_file)
        from orthogonal_analysis import range_analysis
        ra = range_analysis(df, args.factors, args.response)
        ranges = {f["factor"]: f["R"] for f in ra["factors"]}
        plot_range_bar(ranges, args.output)
        print(f"Saved: {args.output}")

    elif args.command == "dosage-performance":
        df = pd.read_csv(args.csv_file)
        plot_dosage_performance(df, args.dosage, args.response, args.output)
        print(f"Saved: {args.output}")

    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
