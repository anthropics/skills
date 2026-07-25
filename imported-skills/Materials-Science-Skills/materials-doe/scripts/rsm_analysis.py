"""Response Surface Methodology (RSM) analysis: CCD/BBD generation,
quadratic model fitting with ANOVA, contour plots, and optimization."""

import argparse
import json
import sys
from itertools import combinations

import numpy as np
import pandas as pd
from scipy import stats


# ---------------------------------------------------------------------------
# Design matrix generation
# ---------------------------------------------------------------------------

def generate_ccd_matrix(
    factor_names: list[str],
    alpha: float | None = None,
    center_points: int = 5,
) -> pd.DataFrame:
    """Generate a Central Composite Design (CCD) matrix in coded levels.

    Parameters
    ----------
    factor_names : list of factor names (length k, 2-5).
    alpha : axial distance.  If *None*, uses rotatable alpha = 2^(k/4).
    center_points : number of center-point replicates (default 5).

    Returns
    -------
    pd.DataFrame with columns = factor_names, rows in coded units.
    """
    k = len(factor_names)
    if k < 2 or k > 5:
        raise ValueError("CCD requires 2-5 factors")

    if alpha is None:
        alpha = 2 ** (k / 4)

    # Factorial portion: full 2^k factorial at +/-1
    factorial = np.array(
        np.meshgrid(*([-1, 1],) * k)
    ).T.reshape(-1, k)

    # Axial portion: +/-alpha on each axis, others at 0
    axial = np.zeros((2 * k, k))
    for i in range(k):
        axial[2 * i, i] = alpha
        axial[2 * i + 1, i] = -alpha

    # Center points
    center = np.zeros((center_points, k))

    coded = np.vstack([factorial, axial, center])
    return pd.DataFrame(coded, columns=factor_names)


def generate_bbd_matrix(
    factor_names: list[str],
    center_points: int = 5,
) -> pd.DataFrame:
    """Generate a Box-Behnken Design (BBD) matrix in coded levels.

    Parameters
    ----------
    factor_names : list of factor names (length k, 2-5).
    center_points : number of center-point replicates (default 5).

    Returns
    -------
    pd.DataFrame with columns = factor_names, rows in coded units.
    """
    k = len(factor_names)
    if k < 2 or k > 5:
        raise ValueError("BBD requires 2-5 factors")

    # For each pair of factors, create a 2^2 factorial with those two
    # factors at +/-1 and all other factors at 0.
    edge_points = []
    for i, j in combinations(range(k), 2):
        for li in [-1, 1]:
            for lj in [-1, 1]:
                row = np.zeros(k)
                row[i] = li
                row[j] = lj
                edge_points.append(row)

    center = np.zeros((center_points, k))
    coded = np.vstack([np.array(edge_points), center])
    return pd.DataFrame(coded, columns=factor_names)


def coded_to_actual(
    coded_df: pd.DataFrame,
    levels: dict[str, tuple[float, float]],
) -> pd.DataFrame:
    """Convert coded design matrix to actual levels.

    levels : dict mapping factor name -> (low, high).
    """
    actual = coded_df.copy()
    for name in coded_df.columns:
        low, high = levels[name]
        center = (low + high) / 2
        half = (high - low) / 2
        actual[name] = center + coded_df[name].values * half
    return actual


def parse_levels(level_specs: list[str]) -> dict[str, tuple[float, float]]:
    """Parse level specs like ['A:10,50', 'B:20,80'] into a dict."""
    levels = {}
    for spec in level_specs:
        name, vals = spec.split(":")
        low, high = vals.split(",")
        levels[name.strip()] = (float(low), float(high))
    return levels


# ---------------------------------------------------------------------------
# Quadratic model fitting & ANOVA
# ---------------------------------------------------------------------------

def _build_quadratic_terms(X_coded: np.ndarray) -> tuple[np.ndarray, list[str]]:
    """Build the full quadratic model matrix from coded factor values.

    Returns (design_matrix, term_names).
    """
    n, k = X_coded.shape
    columns = [np.ones(n)]  # intercept
    names = ["Intercept"]

    # Linear terms
    for i in range(k):
        columns.append(X_coded[:, i])
        names.append(f"x{i + 1}")

    # Interaction terms
    for i, j in combinations(range(k), 2):
        columns.append(X_coded[:, i] * X_coded[:, j])
        names.append(f"x{i + 1}x{j + 1}")

    # Quadratic terms
    for i in range(k):
        columns.append(X_coded[:, i] ** 2)
        names.append(f"x{i + 1}^2")

    return np.column_stack(columns), names


def fit_quadratic_model(
    df: pd.DataFrame,
    factors: list[str],
    response: str,
    alpha: float = 0.05,
) -> dict:
    """Fit a full quadratic model and compute ANOVA.

    Returns dict with:
      - coefficients: list of {term, coefficient, SE, t_value, p_value}
      - anova: {model, residual, lack_of_fit, pure_error, total,
                R2, adj_R2, pred_R2}
    """
    k = len(factors)
    X_coded = df[factors].values.astype(float)
    y = df[response].values.astype(float)
    n = len(y)

    # Build design matrix
    M, term_names = _build_quadratic_terms(X_coded)
    p = M.shape[1]  # number of model terms (including intercept)

    # OLS fit
    beta, residuals_sum, rank, sv = np.linalg.lstsq(M, y, rcond=None)
    y_hat = M @ beta
    ss_residual = float(np.sum((y - y_hat) ** 2))
    df_residual = n - rank

    # --- ANOVA decomposition ---
    y_mean = y.mean()
    ss_total = float(np.sum((y - y_mean) ** 2))
    ss_model = ss_total - ss_residual
    df_model = rank - 1  # exclude intercept

    # Pure error & lack-of-fit
    # Group by unique design points
    X_rounded = np.round(X_coded, decimals=8)
    unique_rows, inverse = np.unique(X_rounded, axis=0, return_inverse=True)
    n_unique = len(unique_rows)

    ss_pure_error = 0.0
    df_pure_error = 0
    for idx in range(n_unique):
        mask = inverse == idx
        group = y[mask]
        ni = len(group)
        if ni > 1:
            ss_pure_error += float(np.sum((group - group.mean()) ** 2))
            df_pure_error += ni - 1

    ss_lack_of_fit = ss_residual - ss_pure_error
    df_lack_of_fit = df_residual - df_pure_error

    ms_model = ss_model / df_model if df_model > 0 else 0.0
    ms_residual = ss_residual / df_residual if df_residual > 0 else 0.0
    ms_lack_of_fit = ss_lack_of_fit / df_lack_of_fit if df_lack_of_fit > 0 else 0.0
    ms_pure_error = ss_pure_error / df_pure_error if df_pure_error > 0 else 0.0

    f_model = ms_model / ms_residual if ms_residual > 0 else float("inf")
    f_lof = ms_lack_of_fit / ms_pure_error if ms_pure_error > 0 else float("inf")

    p_model = float(stats.f.sf(f_model, df_model, df_residual)) if df_residual > 0 else float("nan")
    p_lof = float(stats.f.sf(f_lof, df_lack_of_fit, df_pure_error)) if df_pure_error > 0 else float("nan")

    # R-squared values
    r2 = 1 - ss_residual / ss_total if ss_total > 0 else 0.0
    adj_r2 = 1 - (ss_residual / df_residual) / (ss_total / (n - 1)) if (n - 1) > 0 and df_residual > 0 else 0.0

    # Predicted R² (leave-one-out)
    if n > p and df_residual > 0:
        h = np.diag(M @ np.linalg.inv(M.T @ M) @ M.T)
        press = 0.0
        for i in range(n):
            y_pred_i = y_hat[i] - (y[i] - y_hat[i]) * h[i] / (1 - h[i]) if (1 - h[i]) != 0 else y_hat[i]
            press += (y[i] - y_pred_i) ** 2
        pred_r2 = 1 - press / ss_total if ss_total > 0 else 0.0
    else:
        pred_r2 = 0.0

    # Coefficient statistics
    if df_residual > 0:
        try:
            cov_beta = ms_residual * np.linalg.inv(M.T @ M)
        except np.linalg.LinAlgError:
            cov_beta = np.full((p, p), np.nan)
    else:
        cov_beta = np.full((p, p), np.nan)

    se_beta = np.sqrt(np.diag(cov_beta))
    t_values = beta / se_beta
    p_values = np.array([
        float(2 * stats.t.sf(abs(t), df_residual)) if df_residual > 0 else float("nan")
        for t in t_values
    ])

    coefficients = []
    for i, name in enumerate(term_names):
        coefficients.append({
            "term": name,
            "coefficient": float(beta[i]),
            "SE": float(se_beta[i]),
            "t_value": float(t_values[i]),
            "p_value": float(p_values[i]),
        })

    anova = {
        "model": {
            "SS": ss_model, "df": df_model,
            "MS": ms_model, "F": f_model, "p_value": p_model,
        },
        "residual": {
            "SS": ss_residual, "df": df_residual,
            "MS": ms_residual,
        },
        "lack_of_fit": {
            "SS": ss_lack_of_fit, "df": df_lack_of_fit,
            "MS": ms_lack_of_fit, "F": f_lof, "p_value": p_lof,
        },
        "pure_error": {
            "SS": ss_pure_error, "df": df_pure_error,
            "MS": ms_pure_error,
        },
        "total": {
            "SS": ss_total, "df": n - 1,
        },
        "R2": r2,
        "adj_R2": adj_r2,
        "pred_R2": pred_r2,
        "alpha": alpha,
    }

    return {"coefficients": coefficients, "anova": anova, "n_factors": k}


# ---------------------------------------------------------------------------
# Contour plot
# ---------------------------------------------------------------------------

def _get_model_predictor(
    fit_result: dict,
    factor_names: list[str],
):
    """Return a callable that predicts y from coded factor values."""
    k = len(factor_names)
    coefficients = fit_result["coefficients"]
    beta = np.array([c["coefficient"] for c in coefficients])

    # Rebuild term structure
    def predict(x_coded: np.ndarray) -> float:
        """x_coded: 1-D array of length k in coded units."""
        M, _ = _build_quadratic_terms(x_coded.reshape(1, -1))
        return float((M @ beta)[0])

    return predict


def generate_contour_plot(
    df: pd.DataFrame,
    factors: list[str],
    response: str,
    pair: list[str],
    output_path: str,
    n_grid: int = 100,
) -> None:
    """Generate a contour plot for two factors, others fixed at center.

    Saves a PNG file at *output_path* (300 dpi).
    """
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    # Fit model first
    fit_result = fit_quadratic_model(df, factors, response)
    predict = _get_model_predictor(fit_result, factors)

    k = len(factors)
    # Identify indices for the pair
    idx1 = factors.index(pair[0])
    idx2 = factors.index(pair[1])

    # Grid range: -alpha_max to +alpha_max for the pair, others at 0
    grid_range = np.linspace(-2, 2, n_grid)
    g1, g2 = np.meshgrid(grid_range, grid_range)

    # Build full factor array for each grid point
    center = np.zeros(k)
    Z = np.zeros_like(g1)
    for i in range(n_grid):
        for j in range(n_grid):
            x = center.copy()
            x[idx1] = g1[i, j]
            x[idx2] = g2[i, j]
            Z[i, j] = predict(x)

    fig, ax = plt.subplots(figsize=(8, 6))
    cf = ax.contourf(g1, g2, Z, levels=20, cmap="viridis")
    fig.colorbar(cf, ax=ax)
    ax.set_xlabel(f"{pair[0]} (coded)", fontsize=12)
    ax.set_ylabel(f"{pair[1]} (coded)", fontsize=12)
    ax.set_title(f"Contour Plot: {response} vs {pair[0]}, {pair[1]}", fontsize=14)
    ax.contour(g1, g2, Z, levels=20, colors="white", linewidths=0.5, alpha=0.5)
    plt.tight_layout()
    plt.savefig(output_path, dpi=300)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Optimization
# ---------------------------------------------------------------------------

def optimize_rsm(
    df: pd.DataFrame,
    factors: list[str],
    response: str,
    goal: str = "max",
) -> dict:
    """Optimize factor settings using the fitted quadratic model.

    goal: 'max' or 'min'.
    Returns dict with optimal coded/actual factor values and predicted response.
    """
    fit_result = fit_quadratic_model(df, factors, response)
    predict = _get_model_predictor(fit_result, factors)

    k = len(factors)
    x0 = np.zeros(k)  # start from center

    if goal == "max":
        def objective(x):
            return -predict(x)
    else:
        def objective(x):
            return predict(x)

    from scipy.optimize import minimize
    result = minimize(objective, x0, method="Nelder-Mead",
                      options={"xatol": 1e-8, "fatol": 1e-8, "maxiter": 10000})

    optimal_coded = {factors[i]: float(result.x[i]) for i in range(k)}
    predicted_response = float(predict(result.x))

    return {
        "optimal_coded": optimal_coded,
        "predicted_response": predicted_response,
        "goal": goal,
        "success": bool(result.success),
        "message": result.message if hasattr(result, "message") else "",
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Response Surface Methodology (RSM) analysis"
    )
    parser.add_argument(
        "csv_file", nargs="?", default=None,
        help="Path to experiment CSV file (not needed for --task generate)",
    )
    parser.add_argument(
        "--factors", "-f", nargs="+", required=True,
        help="Factor column names",
    )
    parser.add_argument(
        "--response", "-r", default=None,
        help="Response column name (not needed for --task generate)",
    )
    parser.add_argument(
        "--task", "-t",
        choices=["generate", "fit", "contour", "optimize"],
        default="fit",
        help="Task to perform (default: fit)",
    )
    parser.add_argument(
        "--design", "-d", choices=["ccd", "bbd"], default="ccd",
        help="Design type for generate task (default: ccd)",
    )
    parser.add_argument(
        "--alpha", "-a", type=float, default=None,
        help="CCD axial distance (default: rotatable alpha=2^(k/4)); "
             "for fit task, significance level (default: 0.05)",
    )
    parser.add_argument(
        "--center-points", type=int, default=5,
        help="Number of center points for generate task (default: 5)",
    )
    parser.add_argument(
        "--levels", nargs="+", default=None,
        help="Factor level ranges for generate task, e.g. A:10,50 B:20,80",
    )
    parser.add_argument(
        "--pair", nargs=2, default=None,
        help="Two factors for contour plot, e.g. --pair A B",
    )
    parser.add_argument(
        "--goal", "-g", choices=["max", "min"], default="max",
        help="Optimization goal (default: max)",
    )
    parser.add_argument(
        "--output", "-o", default=None,
        help="Output file (JSON for fit/optimize, CSV for generate, PNG for contour)",
    )
    args = parser.parse_args()

    # --- generate ---
    if args.task == "generate":
        if args.levels is None:
            parser.error("--levels is required for --task generate")

        levels = parse_levels(args.levels)
        # Validate that all factors have levels
        for f in args.factors:
            if f not in levels:
                parser.error(f"No level range provided for factor '{f}'")

        if args.design == "ccd":
            alpha_val = args.alpha  # None means auto rotatable
            coded_df = generate_ccd_matrix(
                args.factors, alpha=alpha_val, center_points=args.center_points,
            )
        else:
            coded_df = generate_bbd_matrix(
                args.factors, center_points=args.center_points,
            )

        actual_df = coded_to_actual(coded_df, levels)

        # Combine coded + actual into one output
        coded_df.columns = [f"{c}_coded" for c in coded_df.columns]
        combined = pd.concat([coded_df, actual_df], axis=1)

        if args.output:
            combined.to_csv(args.output, index=False)
        else:
            print(combined.to_csv(index=False))
        return

    # For all other tasks, we need data
    if args.csv_file is None:
        parser.error("csv_file is required for --task fit/contour/optimize")
    if args.response is None:
        parser.error("--response is required for --task fit/contour/optimize")

    df = pd.read_csv(args.csv_file)

    # --- fit ---
    if args.task == "fit":
        sig_alpha = args.alpha if args.alpha is not None else 0.05
        result = fit_quadratic_model(df, args.factors, args.response, alpha=sig_alpha)
        output = json.dumps(result, indent=2, ensure_ascii=False)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as f:
                f.write(output)
        else:
            print(output)

    # --- contour ---
    elif args.task == "contour":
        if args.pair is None:
            parser.error("--pair is required for --task contour")
        if args.output is None:
            parser.error("--output is required for --task contour (PNG path)")
        generate_contour_plot(
            df, args.factors, args.response, args.pair, args.output,
        )

    # --- optimize ---
    elif args.task == "optimize":
        result = optimize_rsm(df, args.factors, args.response, goal=args.goal)
        output = json.dumps(result, indent=2, ensure_ascii=False)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as f:
                f.write(output)
        else:
            print(output)


if __name__ == "__main__":
    main()
