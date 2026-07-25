"""Screening design analysis: Plackett-Burman, effect analysis, fractional factorial."""

import argparse
import json
import sys
from itertools import combinations
from math import comb

import numpy as np
import pandas as pd
from scipy import stats


# ---------------------------------------------------------------------------
# Plackett-Burman matrix generation
# ---------------------------------------------------------------------------

def _find_base_row_backtrack(n, k, target, timeout=30.0):
    """Find PB base row via backtracking search with pruning."""
    import time

    best_row = [None]

    def _check_complete(row):
        """Check if a complete base row gives valid PB design."""
        for d in range(1, n - 1):
            c = sum(1 for i in range(n - 1) if row[i] == 1 and row[(i + d) % (n - 1)] == 1)
            if c != target:
                return False
        return True

    start_time = [time.time()]

    def _backtrack(positions, remaining):
        if time.time() - start_time[0] > timeout:
            return
        if remaining == 0:
            row = [0] * (n - 1)
            for p in positions:
                row[p] = 1
            if _check_complete(row):
                best_row[0] = row[:]
            return

        needed = remaining
        for start_pos in range(positions[-1] + 1 if positions else 1, n - 1 - needed + 1):
            new_positions = positions + [start_pos]

            # Pruning: check partial autocorrelations
            valid = True
            for d in range(1, n - 1):
                c = sum(
                    1
                    for i in range(len(new_positions))
                    if (new_positions[i] + d) % (n - 1) in set(new_positions)
                )
                if c > target:
                    valid = False
                    break

            if valid:
                if best_row[0] is not None:
                    return
                _backtrack(new_positions, remaining - 1)

    _backtrack([], k)

    if best_row[0] is not None:
        return best_row[0]

    # Fallback: randomized greedy search
    rng = np.random.RandomState(42)
    for _ in range(5000):
        if time.time() - start_time[0] > timeout:
            break
        pos = list(range(n - 1))
        rng.shuffle(pos)
        pos = sorted(pos[:k])

        row = [0] * (n - 1)
        for p in pos:
            row[p] = 1

        violations = sum(
            abs(
                sum(1 for i in range(n - 1) if row[i] == 1 and row[(i + d) % (n - 1)] == 1)
                - target
            )
            for d in range(1, n - 1)
        )

        if violations == 0:
            return row

        # Iterative swap improvement
        for __ in range(2000):
            if violations == 0:
                break
            i, j = rng.randint(k), rng.randint(n - 1 - k)
            in_pos = set(pos)
            out_candidates = [x for x in range(n - 1) if x not in in_pos]
            if not out_candidates:
                break
            j_pos = rng.randint(len(out_candidates))
            j = out_candidates[j_pos]

            old_i, new_j = pos[i], j
            pos[i] = new_j
            row[old_i], row[new_j] = 0, 1

            new_violations = sum(
                abs(
                    sum(1 for ii in range(n - 1) if row[ii] == 1 and row[(ii + d) % (n - 1)] == 1)
                    - target
                )
                for d in range(1, n - 1)
            )

            if new_violations <= violations:
                violations = new_violations
            else:
                pos[i] = old_i
                row[old_i], row[new_j] = 1, 0

        if violations == 0:
            return row

    return None


def generate_pb_matrix(n_factors, levels=None, actual_levels=None):
    """Generate a Plackett-Burman design matrix.

    Parameters
    ----------
    n_factors : int
        Number of factors (2-15).
    levels : list of float, optional
        [low, high] coded levels.  Default [-1, 1].
    actual_levels : dict, optional
        Mapping like ``{"A": (low, high), ...}`` for actual level conversion.

    Returns
    -------
    dict with coded_matrix, actual_matrix, n_runs, factor_names.
    """
    if levels is None:
        levels = [-1.0, 1.0]

    if n_factors < 2 or n_factors > 15:
        raise ValueError("n_factors must be between 2 and 15")

    # N = smallest multiple of 4 that is > n_factors
    n_runs = ((n_factors + 4) // 4) * 4
    if n_runs <= n_factors:
        n_runs += 4

    # Base row construction parameters.
    # The base row has length N-1 with N/2 entries of +1 and N/2-1 entries of -1.
    # For the cyclic PB matrix to be orthogonal, every non-zero cyclic shift
    # of the base row must produce an overlap of exactly N/4 between +1 positions.
    k = n_runs // 2          # number of +1 in the base row
    target = n_runs // 4     # target overlap for each non-zero shift

    # Find base row via backtracking search.
    # The base row has length N-1; the full N x (N-1) matrix is built by
    # cyclic shifts + an all-(-1) row.
    base_row = _find_base_row_backtrack(n_runs, k, target)

    if base_row is None:
        raise RuntimeError(
            f"Could not find PB({n_runs}) base row. "
            "This design size may not support a cyclic construction."
        )

    # Build full matrix from base row via cyclic shifts.
    # The base row uses 1/+1 and 0/-1 encoding; convert to +1/-1.
    base_arr = np.array([1 if x == 1 else -1 for x in base_row], dtype=int)
    n_cols = n_runs - 1
    matrix = np.zeros((n_runs, n_cols), dtype=int)
    for i in range(n_runs - 1):
        matrix[i, :] = np.roll(base_arr, i)
    matrix[-1, :] = -1  # all -1 row

    # Truncate to requested number of factors
    matrix = matrix[:, :n_factors]

    # Verify orthogonality
    mtm = matrix.T @ matrix
    for i in range(n_factors):
        for j in range(i + 1, n_factors):
            if mtm[i, j] != 0:
                raise RuntimeError(
                    f"PB matrix orthogonality check failed: "
                    f"columns {i} and {j} have inner product {mtm[i, j]}"
                )

    factor_names = [f"x{i+1}" for i in range(n_factors)]

    # Build coded design matrix
    low, high = float(levels[0]), float(levels[1])
    coded_df = pd.DataFrame(matrix, columns=factor_names)
    coded_df.insert(0, "run", range(1, n_runs + 1))

    # Build actual design matrix
    actual_df = pd.DataFrame()
    actual_df["run"] = coded_df["run"]
    for i, fn in enumerate(factor_names):
        if actual_levels and fn in actual_levels:
            al = actual_levels[fn]
            actual_df[fn] = np.where(
                matrix[:, i] == 1, float(al[1]), float(al[0])
            )
        else:
            actual_df[fn] = np.where(
                matrix[:, i] == 1, high, low
            )

    return {
        "coded_matrix": coded_df,
        "actual_matrix": actual_df,
        "n_runs": n_runs,
        "n_factors": n_factors,
        "factor_names": factor_names,
    }


# ---------------------------------------------------------------------------
# Effect analysis
# ---------------------------------------------------------------------------

def analyze_effects(df, factors, response, alpha=0.05):
    """Compute main effects, t-values, p-values for a screening design.

    Effect = mean(Y | factor=+1) - mean(Y | factor=-1).

    Standard error is estimated from residual MSE when degrees of freedom allow,
    otherwise falls back to Lenth's robust method for saturated designs.
    """
    y = df[response].values.astype(float)
    n = len(y)
    k = len(factors)

    effects = {}
    for factor in factors:
        x = df[factor].values.astype(float)
        mean_plus = y[x > 0].mean()
        mean_minus = y[x < 0].mean()
        effects[factor] = float(mean_plus - mean_minus)

    # Estimate standard error of effects
    # Try residual-based MSE first
    X = np.column_stack([np.ones(n), df[factors].values.astype(float)])
    try:
        beta, residuals_sum, _, _ = np.linalg.lstsq(X, y, rcond=None)
        y_hat = X @ beta
        ss_res = float(np.sum((y - y_hat) ** 2))
        df_error = n - k - 1

        if df_error > 0:
            mse = ss_res / df_error
            se_effect = float(np.sqrt(mse * 4.0 / n))
            method = "residual"
        else:
            raise ValueError("saturated")
    except Exception:
        # Fallback: Lenth's robust estimate
        abs_effects = np.array([abs(effects[f]) for f in factors])
        s0 = 1.5 * np.median(abs_effects)
        sig_effects = [abs(effects[f]) for f in factors if abs(effects[f]) < 2.5 * s0]
        if len(sig_effects) > 1:
            se = 1.5 * np.median(sig_effects)
        else:
            se = s0
        se_effect = float(se) if se > 0 else 1.0
        df_error = k - 1 if k > 1 else 1
        method = "lenth"

    # t-values and p-values
    t_values = {}
    p_values = {}
    for factor in factors:
        t_val = effects[factor] / se_effect if se_effect > 0 else 0.0
        t_values[factor] = float(t_val)
        p_values[factor] = float(
            2.0 * stats.t.sf(abs(t_val), max(df_error, 1))
        )

    significant = [f for f in factors if p_values[f] < alpha]

    # Pareto data: sorted by |effect| descending
    pareto = sorted(
        [
            {
                "factor": f,
                "effect": effects[f],
                "abs_effect": abs(effects[f]),
                "t_value": t_values[f],
                "p_value": p_values[f],
                "significant": p_values[f] < alpha,
            }
            for f in factors
        ],
        key=lambda x: x["abs_effect"],
        reverse=True,
    )

    return {
        "effects": effects,
        "t_values": t_values,
        "p_values": p_values,
        "significant_factors": significant,
        "alpha": alpha,
        "se_effect": se_effect,
        "df_error": df_error,
        "se_method": method,
        "pareto": pareto,
    }


# ---------------------------------------------------------------------------
# Fractional factorial design generation
# ---------------------------------------------------------------------------

def _full_factorial_2level(n_cols):
    """Full 2^n factorial in coded -1/+1."""
    if n_cols <= 0:
        return np.empty((1, 0), dtype=int)
    n_runs = 2 ** n_cols
    design = np.ones((n_runs, n_cols), dtype=int)
    for j in range(n_cols):
        period = 2 ** (j + 1)
        half = period // 2
        for i in range(n_runs):
            if (i % period) < half:
                design[i, j] = -1
    return design


def _compute_generators(n_basic, n_extra, resolution):
    """Assign generator columns for extra factors.

    Each extra factor is the product of *resolution - 1* basic factors,
    cycling through combinations.
    """
    generators = {}
    gen_size = resolution - 1
    if gen_size < 2:
        gen_size = 2
    all_combs = list(combinations(range(n_basic), gen_size))
    if n_extra > len(all_combs):
        raise ValueError(
            f"Cannot create {n_extra} extra factors with resolution {resolution} "
            f"and {n_basic} basic factors. Use more basic factors or lower resolution."
        )
    for i in range(n_extra):
        generators[n_basic + i] = list(all_combs[i])
    return generators


def _defining_words(generators, factor_names):
    """Compute defining relation words from generators.

    Each generator ``X = ABC`` contributes the word ``I = ABCX``.
    Products of generators are also included.
    """
    words = []
    n_gens = len(generators)
    for r in range(1, n_gens + 1):
        for combo in combinations(sorted(generators.keys()), r):
            cols = set()
            for g in combo:
                cols ^= set(generators[g]) | {g}  # include the generated factor
            word = "".join(factor_names[c] for c in sorted(cols))
            words.append(word)
    return words


def _alias_chains(factor_names, generators, max_order=2):
    """Compute alias structure for main effects and 2-factor interactions."""
    n = len(factor_names)
    # Build defining relation (as sets of factor indices)
    def_words = [set()]  # identity
    n_gens = len(generators)
    for r in range(1, n_gens + 1):
        for combo in combinations(sorted(generators.keys()), r):
            cols = set()
            for g in combo:
                cols ^= set(generators[g]) | {g}
            def_words.append(cols)

    def _multiply(s1, s2):
        result = s1 ^ s2  # symmetric difference
        return result

    def _label(s):
        if len(s) == 0:
            return "I"
        return "".join(factor_names[i] for i in sorted(s))

    # Generate all effects up to max_order
    all_effects = []
    for order in range(1, max_order + 1):
        for combo in combinations(range(n), order):
            all_effects.append(set(combo))

    alias_groups = []
    visited = set()

    for effect in all_effects:
        key = frozenset(effect)
        if key in visited:
            continue
        chain = []
        for word in def_words:
            aliased = _multiply(effect, word)
            fkey = frozenset(aliased)
            if fkey not in visited and len(aliased) <= max_order:
                chain.append(aliased)
                visited.add(fkey)
        if chain:
            alias_groups.append([_label(a) for a in chain])

    return alias_groups


def generate_fractional_ff(n_factors, resolution="IV"):
    """Generate a 2^(k-p) fractional factorial design.

    Parameters
    ----------
    n_factors : int
        Number of factors (2-5 for practical use).
    resolution : str
        Design resolution: III, IV, or V.

    Returns
    -------
    dict with design matrix, generators, defining relation, alias structure.
    """
    res_map = {"III": 3, "IV": 4, "V": 5}
    if resolution not in res_map:
        raise ValueError(f"resolution must be III, IV, or V, got '{resolution}'")
    res_val = res_map[resolution]

    # Determine number of basic factors
    # For resolution R, each generator uses R-1 basic factors
    # We need enough basic factors to support the generators
    n_basic = res_val - 1  # minimum basic factors for the generator size
    n_extra = n_factors - n_basic

    if n_extra < 0:
        # Fewer factors than generator size; use full factorial
        n_basic = n_factors
        n_extra = 0

    # Ensure we have enough combinations for generators
    gen_size = res_val - 1
    while n_extra > 0 and comb(n_basic, gen_size) < n_extra:
        n_basic += 1
        n_extra = n_factors - n_basic

    n_runs = 2 ** n_basic
    factor_names = [chr(ord("A") + i) for i in range(n_factors)]

    # Build base full factorial
    base_design = _full_factorial_2level(n_basic)

    # Add extra factors via generators
    generators = _compute_generators(n_basic, n_extra, res_val)
    extra_cols = []
    for extra_idx in sorted(generators.keys()):
        gen_cols = generators[extra_idx]
        col = np.ones(n_runs, dtype=int)
        for c in gen_cols:
            col = col * base_design[:, c]
        extra_cols.append((extra_idx, col))

    # Assemble full design
    all_cols = [base_design]
    for _, col in extra_cols:
        all_cols.append(col.reshape(-1, 1))
    design = np.hstack(all_cols) if len(extra_cols) > 0 else base_design

    # Build DataFrame
    df = pd.DataFrame(design, columns=factor_names)
    df.insert(0, "run", range(1, n_runs + 1))

    # Generators description
    gen_desc = {}
    for extra_idx, gen_cols in sorted(generators.items()):
        gen_label = "".join(factor_names[c] for c in gen_cols)
        gen_desc[factor_names[extra_idx]] = gen_label

    # Defining relation
    def_words = _defining_words(generators, factor_names)
    defining_relation = ["I = " + w for w in def_words]

    # Alias structure
    aliases = _alias_chains(factor_names, generators, max_order=2)

    return {
        "design": df,
        "n_runs": n_runs,
        "n_factors": n_factors,
        "n_basic": n_basic,
        "n_extra": n_extra,
        "resolution": resolution,
        "generators": gen_desc,
        "defining_relation": defining_relation,
        "alias_structure": aliases,
        "factor_names": factor_names,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Screening design analysis: Plackett-Burman, effect analysis, "
        "fractional factorial"
    )
    parser.add_argument(
        "csv_file", nargs="?", default=None, help="Input CSV file (required for analyze)"
    )
    parser.add_argument(
        "--task",
        "-t",
        choices=["generate", "analyze", "generate-ff"],
        default="analyze",
        help="Task to perform (default: analyze)",
    )
    parser.add_argument(
        "--factors", "-f", nargs="+", help="Factor names"
    )
    parser.add_argument(
        "--response", "-r", help="Response column name (for analyze)"
    )
    parser.add_argument(
        "--levels", "-l", nargs=2, type=float, default=[-1.0, 1.0],
        metavar=("LOW", "HIGH"),
        help="Coded low/high levels (default: -1 1)",
    )
    parser.add_argument(
        "--actual-levels", nargs="+", metavar="FACTOR:LOW,HIGH",
        help='Actual level mapping, e.g. "A:10,50" "B:20,80"',
    )
    parser.add_argument(
        "--resolution", choices=["III", "IV", "V"], default="IV",
        help="Resolution for fractional factorial (default: IV)",
    )
    parser.add_argument(
        "--alpha", "-a", type=float, default=0.05,
        help="Significance level (default: 0.05)",
    )
    parser.add_argument(
        "--output", "-o", help="Output file (CSV for generate tasks, JSON for analyze)"
    )
    args = parser.parse_args()

    # ---- generate: Plackett-Burman ----
    if args.task == "generate":
        if not args.factors:
            parser.error("--factors is required for --task generate")
        n_factors = len(args.factors)

        # Parse actual levels
        actual_levels = {}
        if args.actual_levels:
            for item in args.actual_levels:
                name, vals = item.split(":")
                lo, hi = vals.split(",")
                actual_levels[name.strip()] = (float(lo), float(hi))

        result = generate_pb_matrix(n_factors, args.levels, actual_levels or None)

        # Use provided factor names
        coded_df = result["coded_matrix"]
        actual_df = result["actual_matrix"]
        rename = dict(zip(result["factor_names"], args.factors))
        coded_df = coded_df.rename(columns=rename)
        actual_df = actual_df.rename(columns=rename)

        if args.output:
            coded_df.to_csv(args.output, index=False)
            # Write actual levels to a companion file
            base = args.output.rsplit(".", 1)
            actual_path = base[0] + "_actual." + base[1] if len(base) == 2 else args.output + "_actual"
            actual_df.to_csv(actual_path, index=False)
            print(
                f"PB({result['n_runs']}) design: {result['n_factors']} factors, "
                f"{result['n_runs']} runs",
                file=sys.stderr,
            )
            print(f"Coded design -> {args.output}", file=sys.stderr)
            print(f"Actual design -> {actual_path}", file=sys.stderr)
        else:
            print(coded_df.to_csv(index=False), end="")

    # ---- analyze: effect analysis ----
    elif args.task == "analyze":
        if not args.csv_file:
            parser.error("csv_file is required for --task analyze")
        if not args.factors:
            parser.error("--factors is required for --task analyze")
        if not args.response:
            parser.error("--response is required for --task analyze")

        df = pd.read_csv(args.csv_file)
        result = analyze_effects(df, args.factors, args.response, args.alpha)

        output = json.dumps(result, indent=2, ensure_ascii=False)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as f:
                f.write(output)
        else:
            print(output)

    # ---- generate-ff: Fractional Factorial ----
    elif args.task == "generate-ff":
        if not args.factors:
            parser.error("--factors is required for --task generate-ff")
        n_factors = len(args.factors)

        result = generate_fractional_ff(n_factors, args.resolution)

        # Rename factors
        rename = dict(zip(result["factor_names"], args.factors))
        design_df = result["design"].rename(columns=rename)

        # Remap alias structure and generators to use provided names
        gen_renamed = {}
        for k, v in result["generators"].items():
            new_key = rename.get(k, k)
            new_val = "".join(rename.get(c, c) for c in v)
            gen_renamed[new_key] = new_val

        def_rel_renamed = []
        for word in result["defining_relation"]:
            new_word = "I = "
            rest = word.replace("I = ", "")
            new_word += "".join(rename.get(c, c) for c in rest)
            def_rel_renamed.append(new_word)

        alias_renamed = []
        for group in result["alias_structure"]:
            new_group = []
            for label in group:
                if label == "I":
                    new_group.append("I")
                else:
                    new_group.append("".join(rename.get(c, c) for c in label))
            alias_renamed.append(new_group)

        if args.output:
            design_df.to_csv(args.output, index=False)
            print(
                f"2^({result['n_basic']}-{result['n_extra']}) fractional factorial, "
                f"resolution {result['resolution']}",
                file=sys.stderr,
            )
            print(f"Design -> {args.output}", file=sys.stderr)

            # Print generators and alias info to stderr
            print(f"\nGenerators:", file=sys.stderr)
            for k, v in gen_renamed.items():
                print(f"  {k} = {v}", file=sys.stderr)
            print(f"\nDefining relation:", file=sys.stderr)
            for w in def_rel_renamed:
                print(f"  {w}", file=sys.stderr)
            print(f"\nAlias structure:", file=sys.stderr)
            for group in alias_renamed:
                print(f"  {' = '.join(group)}", file=sys.stderr)
        else:
            # Output everything as JSON to stdout
            info = {
                "design": design_df.to_dict(orient="list"),
                "n_runs": result["n_runs"],
                "resolution": result["resolution"],
                "generators": gen_renamed,
                "defining_relation": def_rel_renamed,
                "alias_structure": alias_renamed,
            }
            print(json.dumps(info, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
