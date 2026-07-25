#!/usr/bin/env python3
"""
stats_toolkit.py — a tested statistical toolkit for the rigorous-statistical-analysis skill.

Every function returns plain dicts/objects that print cleanly into a report. The guiding rule of the
skill applies here too: recompute, never trust a supplied statistic; always attach an effect size and
a confidence interval; check assumptions before reporting an inferential result.

Dependencies: numpy, scipy, pandas, statsmodels.
    pip install numpy scipy pandas statsmodels

Quick check:
    python3 stats_toolkit.py --selftest
"""
from __future__ import annotations

import math
from typing import Sequence

import numpy as np
from scipy import stats

try:
    import statsmodels.api as sm
    import statsmodels.formula.api as smf
    from statsmodels.stats.outliers_influence import variance_inflation_factor
    from statsmodels.stats.diagnostic import het_breuschpagan
    from statsmodels.stats.stattools import durbin_watson
    _HAS_SM = True
except Exception:  # pragma: no cover - statsmodels optional at runtime
    _HAS_SM = False


# --------------------------------------------------------------------------------------
# Descriptive & dispersion
# --------------------------------------------------------------------------------------
def describe(x: Sequence[float]) -> dict:
    """n, mean, sd, se, median, IQR, min, max, CV (SD/mean), skew, kurtosis."""
    a = np.asarray(x, dtype=float)
    a = a[~np.isnan(a)]
    n = a.size
    mean = float(np.mean(a))
    sd = float(np.std(a, ddof=1)) if n > 1 else float("nan")
    q1, q3 = np.percentile(a, [25, 75])
    return {
        "n": n,
        "mean": mean,
        "sd": sd,
        "se": sd / math.sqrt(n) if n > 1 else float("nan"),
        "median": float(np.median(a)),
        "iqr": float(q3 - q1),
        "min": float(np.min(a)),
        "max": float(np.max(a)),
        "cv": sd / mean if mean != 0 else float("nan"),
        "skew": float(stats.skew(a)),
        "kurtosis": float(stats.kurtosis(a)),  # excess kurtosis
    }


# --------------------------------------------------------------------------------------
# Confidence intervals
# --------------------------------------------------------------------------------------
def ci_mean(x: Sequence[float], conf: float = 0.95) -> dict:
    """t-based confidence interval for a mean."""
    a = np.asarray(x, dtype=float)
    a = a[~np.isnan(a)]
    n = a.size
    mean = float(np.mean(a))
    se = float(np.std(a, ddof=1) / math.sqrt(n))
    h = se * stats.t.ppf((1 + conf) / 2, n - 1)
    return {"estimate": mean, "lo": mean - h, "hi": mean + h, "conf": conf, "n": n}


def bootstrap_ci(x: Sequence[float], statfn=np.mean, n_boot: int = 10000,
                 conf: float = 0.95, seed: int | None = 42) -> dict:
    """Percentile bootstrap CI for any statistic (median, Gini, ratio, ...)."""
    rng = np.random.default_rng(seed)
    a = np.asarray(x, dtype=float)
    a = a[~np.isnan(a)]
    n = a.size
    boot = np.empty(n_boot)
    for i in range(n_boot):
        boot[i] = statfn(rng.choice(a, size=n, replace=True))
    lo, hi = np.percentile(boot, [(1 - conf) / 2 * 100, (1 + conf) / 2 * 100])
    return {"estimate": float(statfn(a)), "lo": float(lo), "hi": float(hi),
            "conf": conf, "n_boot": n_boot}


# --------------------------------------------------------------------------------------
# Effect sizes
# --------------------------------------------------------------------------------------
def cohens_d(a: Sequence[float], b: Sequence[float], paired: bool = False) -> dict:
    """Cohen's d (pooled SD) with Hedges' g small-sample correction."""
    a = np.asarray(a, dtype=float); a = a[~np.isnan(a)]
    b = np.asarray(b, dtype=float); b = b[~np.isnan(b)]
    n1, n2 = a.size, b.size
    if paired:
        diff = a - b
        d = float(np.mean(diff) / np.std(diff, ddof=1))
        dof = n1 - 1
    else:
        sp = math.sqrt(((n1 - 1) * np.var(a, ddof=1) + (n2 - 1) * np.var(b, ddof=1)) / (n1 + n2 - 2))
        d = float((np.mean(a) - np.mean(b)) / sp)
        dof = n1 + n2 - 2
    g = d * (1 - 3 / (4 * dof - 1))  # Hedges correction
    return {"d": d, "hedges_g": g, "magnitude": _mag(abs(d), (0.2, 0.5, 0.8))}


def _mag(v, thresh):
    lo, mid, hi = thresh
    if v < lo:
        return "negligible"
    if v < mid:
        return "small"
    if v < hi:
        return "medium"
    return "large"


# --------------------------------------------------------------------------------------
# Comparison tests
# --------------------------------------------------------------------------------------
def t_onesample(x: Sequence[float], popmean: float) -> dict:
    a = np.asarray(x, dtype=float); a = a[~np.isnan(a)]
    t, p = stats.ttest_1samp(a, popmean)
    return {"test": "one-sample t", "t": float(t), "df": a.size - 1, "p": float(p),
            "mean": float(np.mean(a)), "popmean": popmean, "verdict": verdict(float(p))}


def t_independent(a: Sequence[float], b: Sequence[float], welch: bool = True) -> dict:
    """Independent-samples t-test. Welch (unequal variance) by default."""
    a = np.asarray(a, dtype=float); a = a[~np.isnan(a)]
    b = np.asarray(b, dtype=float); b = b[~np.isnan(b)]
    t, p = stats.ttest_ind(a, b, equal_var=not welch)
    es = cohens_d(a, b)
    diff = float(np.mean(a) - np.mean(b))
    return {"test": "Welch t" if welch else "Student t", "t": float(t), "p": float(p),
            "mean_diff": diff, "d": es["d"], "hedges_g": es["hedges_g"],
            "magnitude": es["magnitude"], "verdict": verdict(float(p))}


def t_paired(a: Sequence[float], b: Sequence[float]) -> dict:
    a = np.asarray(a, dtype=float); b = np.asarray(b, dtype=float)
    t, p = stats.ttest_rel(a, b)
    es = cohens_d(a, b, paired=True)
    return {"test": "paired t", "t": float(t), "df": a.size - 1, "p": float(p),
            "mean_diff": float(np.mean(a - b)), "d": es["d"], "magnitude": es["magnitude"],
            "verdict": verdict(float(p))}


def one_way_anova(*groups: Sequence[float]) -> dict:
    """One-way ANOVA with eta-squared and (less biased) omega-squared."""
    gs = [np.asarray(g, dtype=float) for g in groups]
    gs = [g[~np.isnan(g)] for g in gs]
    f, p = stats.f_oneway(*gs)
    grand = np.concatenate(gs)
    n = grand.size
    k = len(gs)
    ss_total = float(np.sum((grand - grand.mean()) ** 2))
    ss_between = float(sum(g.size * (g.mean() - grand.mean()) ** 2 for g in gs))
    ss_within = ss_total - ss_between
    df_b, df_w = k - 1, n - k
    ms_within = ss_within / df_w
    eta2 = ss_between / ss_total
    omega2 = (ss_between - df_b * ms_within) / (ss_total + ms_within)
    return {"test": "one-way ANOVA", "F": float(f), "df_between": df_b, "df_within": df_w,
            "p": float(p), "eta2": eta2, "omega2": float(omega2), "verdict": verdict(float(p))}


def mann_whitney(a: Sequence[float], b: Sequence[float]) -> dict:
    a = np.asarray(a, dtype=float); b = np.asarray(b, dtype=float)
    u, p = stats.mannwhitneyu(a, b, alternative="two-sided")
    rb = 1 - (2 * u) / (a.size * b.size)  # rank-biserial correlation
    return {"test": "Mann-Whitney U", "U": float(u), "p": float(p),
            "rank_biserial": float(rb), "verdict": verdict(float(p))}


def wilcoxon(a: Sequence[float], b: Sequence[float]) -> dict:
    a = np.asarray(a, dtype=float); b = np.asarray(b, dtype=float)
    w, p = stats.wilcoxon(a, b)
    return {"test": "Wilcoxon signed-rank", "W": float(w), "p": float(p),
            "verdict": verdict(float(p))}


def kruskal(*groups: Sequence[float]) -> dict:
    gs = [np.asarray(g, dtype=float) for g in groups]
    h, p = stats.kruskal(*gs)
    return {"test": "Kruskal-Wallis", "H": float(h), "df": len(gs) - 1, "p": float(p),
            "verdict": verdict(float(p))}


# --------------------------------------------------------------------------------------
# Association
# --------------------------------------------------------------------------------------
def correlation(x: Sequence[float], y: Sequence[float], method: str = "pearson") -> dict:
    x = np.asarray(x, dtype=float); y = np.asarray(y, dtype=float)
    if method == "pearson":
        r, p = stats.pearsonr(x, y)
    elif method == "spearman":
        r, p = stats.spearmanr(x, y)
    elif method == "kendall":
        r, p = stats.kendalltau(x, y)
    else:
        raise ValueError("method must be pearson|spearman|kendall")
    n = x.size
    out = {"method": method, "r": float(r), "p": float(p), "n": n,
           "r2": float(r ** 2), "verdict": verdict(float(p))}
    if method == "pearson" and n > 3:  # Fisher z CI
        z = np.arctanh(r)
        se = 1 / math.sqrt(n - 3)
        zcrit = stats.norm.ppf(0.975)
        out["ci"] = (float(np.tanh(z - zcrit * se)), float(np.tanh(z + zcrit * se)))
    return out


def corr_matrix(df, method: str = "pearson") -> dict:
    """Correlation matrix with a matching matrix of p-values."""
    cols = list(df.columns)
    k = len(cols)
    R = np.eye(k)
    P = np.zeros((k, k))
    for i in range(k):
        for j in range(i + 1, k):
            res = correlation(df[cols[i]].values, df[cols[j]].values, method)
            R[i, j] = R[j, i] = res["r"]
            P[i, j] = P[j, i] = res["p"]
    return {"columns": cols, "r": R, "p": P}


def chi_square(table) -> dict:
    """Chi-square test of independence with Cramér's V; suggests Fisher if cells are sparse."""
    table = np.asarray(table, dtype=float)
    chi2, p, dof, expected = stats.chi2_contingency(table)
    n = table.sum()
    k = min(table.shape) - 1
    cramers_v = math.sqrt(chi2 / (n * k)) if k > 0 else float("nan")
    return {"test": "chi-square", "chi2": float(chi2), "df": int(dof), "p": float(p),
            "cramers_v": float(cramers_v), "min_expected": float(expected.min()),
            "use_fisher": bool(expected.min() < 5), "verdict": verdict(float(p))}


# --------------------------------------------------------------------------------------
# Regression
# --------------------------------------------------------------------------------------
def ols_fit(df, formula: str, robust: str = "HC3") -> dict:
    """OLS with robust (HC3) SE by default + VIF, Breusch-Pagan, Durbin-Watson diagnostics."""
    _require_sm()
    model = smf.ols(formula, data=df).fit(cov_type=robust) if robust else smf.ols(formula, data=df).fit()
    coefs = {}
    ci = model.conf_int()
    for name in model.params.index:
        coefs[name] = {"beta": float(model.params[name]), "se": float(model.bse[name]),
                       "t": float(model.tvalues[name]), "p": float(model.pvalues[name]),
                       "ci": (float(ci.loc[name, 0]), float(ci.loc[name, 1]))}
    # diagnostics
    exog = model.model.exog
    names = model.model.exog_names
    vif = {}
    if exog.shape[1] > 2:  # more than intercept + 1
        for i, nm in enumerate(names):
            if nm == "Intercept":
                continue
            vif[nm] = float(variance_inflation_factor(exog, i))
    bp = het_breuschpagan(model.resid, exog)
    return {"n": int(model.nobs), "r2": float(model.rsquared),
            "adj_r2": float(model.rsquared_adj), "f": float(model.fvalue),
            "f_p": float(model.f_pvalue), "coefs": coefs, "vif": vif,
            "breusch_pagan_p": float(bp[1]), "durbin_watson": float(durbin_watson(model.resid)),
            "cov_type": robust or "nonrobust"}


def fixed_effects(df, y: str, x, entity: str, cluster: bool = True) -> dict:
    """OLS with entity fixed effects (dummies), cluster-robust SE by entity by default.

    x: str or list of predictor column names. Entity dummies absorb time-invariant
    between-unit differences, isolating the within-unit relationship.
    """
    _require_sm()
    xs = [x] if isinstance(x, str) else list(x)
    formula = f"{y} ~ {' + '.join(xs)} + C({entity})"
    if cluster:
        model = smf.ols(formula, data=df).fit(cov_type="cluster",
                                              cov_kwds={"groups": df[entity]})
    else:
        model = smf.ols(formula, data=df).fit(cov_type="HC3")
    ci = model.conf_int()
    coefs = {}
    for nm in xs:
        coefs[nm] = {"beta": float(model.params[nm]), "se": float(model.bse[nm]),
                     "t": float(model.tvalues[nm]), "p": float(model.pvalues[nm]),
                     "ci": (float(ci.loc[nm, 0]), float(ci.loc[nm, 1])),
                     "verdict": verdict(float(model.pvalues[nm]))}
    return {"n": int(model.nobs), "n_entities": int(df[entity].nunique()),
            "within_r2": float(model.rsquared), "coefs": coefs,
            "se": "clustered by entity" if cluster else "HC3 robust"}


# --------------------------------------------------------------------------------------
# Inequality & diversity
# --------------------------------------------------------------------------------------
def gini(x: Sequence[float]) -> float:
    """Gini coefficient (0 = perfectly equal, →1 = fully concentrated). Requires non-negative values."""
    a = np.sort(np.asarray(x, dtype=float))
    if np.any(a < 0):
        raise ValueError("Gini is undefined for negative values")
    n = a.size
    if n == 0 or a.sum() == 0:
        return float("nan")
    idx = np.arange(1, n + 1)
    return float((2 * np.sum(idx * a)) / (n * np.sum(a)) - (n + 1) / n)


def shannon_wiener(counts: Sequence[float]) -> dict:
    """Shannon-Wiener diversity H and evenness = H / ln(S)."""
    c = np.asarray(counts, dtype=float)
    c = c[c > 0]
    p = c / c.sum()
    h = float(-np.sum(p * np.log(p)))
    s = c.size
    return {"H": h, "S": s, "evenness": h / math.log(s) if s > 1 else float("nan")}


def hhi(shares_percent: Sequence[float]) -> dict:
    """Herfindahl-Hirschman Index from shares in PERCENT (0-100). Sum of squared shares."""
    s = np.asarray(shares_percent, dtype=float)
    val = float(np.sum(s ** 2))
    level = "low" if val < 1500 else ("moderate" if val < 2500 else "high")
    return {"hhi": val, "concentration": level}


# --------------------------------------------------------------------------------------
# Trend
# --------------------------------------------------------------------------------------
def mann_kendall(x: Sequence[float]) -> dict:
    """Mann-Kendall monotonic-trend test (distribution-free, robust to outliers)."""
    a = np.asarray(x, dtype=float)
    n = a.size
    s = 0
    for k in range(n - 1):
        s += np.sum(np.sign(a[k + 1:] - a[k]))
    var_s = (n * (n - 1) * (2 * n + 5)) / 18.0
    if s > 0:
        z = (s - 1) / math.sqrt(var_s)
    elif s < 0:
        z = (s + 1) / math.sqrt(var_s)
    else:
        z = 0.0
    p = 2 * (1 - stats.norm.cdf(abs(z)))
    tau = s / (0.5 * n * (n - 1))
    trend = "increasing" if (p < 0.05 and s > 0) else ("decreasing" if (p < 0.05 and s < 0) else "none")
    return {"test": "Mann-Kendall", "S": float(s), "tau": float(tau), "z": float(z),
            "p": float(p), "trend": trend, "verdict": verdict(float(p))}


def cagr(begin: float, end: float, periods: int) -> float:
    """Compound annual growth rate over `periods` intervals."""
    if begin <= 0 or periods <= 0:
        return float("nan")
    return (end / begin) ** (1 / periods) - 1


# --------------------------------------------------------------------------------------
# Outliers
# --------------------------------------------------------------------------------------
def outliers_iqr(x: Sequence[float], k: float = 1.5) -> dict:
    a = np.asarray(x, dtype=float)
    q1, q3 = np.percentile(a, [25, 75])
    iqr = q3 - q1
    lo, hi = q1 - k * iqr, q3 + k * iqr
    mask = (a < lo) | (a > hi)
    return {"method": "IQR", "lower": float(lo), "upper": float(hi),
            "indices": np.where(mask)[0].tolist(), "values": a[mask].tolist()}


def outliers_modified_z(x: Sequence[float], thresh: float = 3.5) -> dict:
    """Robust outlier detection via median/MAD; preferred over the plain z-score."""
    a = np.asarray(x, dtype=float)
    med = np.median(a)
    mad = np.median(np.abs(a - med))
    if mad > 0:
        mz = 0.6745 * (a - med) / mad
        basis = "MAD"
    else:
        # Iglewicz-Hoaglin fallback when MAD collapses to 0 (many tied values)
        mean_ad = np.mean(np.abs(a - med))
        if mean_ad == 0:
            return {"method": "modified z", "indices": [], "values": [],
                    "note": "MAD=0 and MeanAD=0 (no dispersion)"}
        mz = (a - med) / (1.253314 * mean_ad)
        basis = "MeanAD"
    mask = np.abs(mz) > thresh
    return {"method": "modified z", "threshold": thresh, "basis": basis,
            "indices": np.where(mask)[0].tolist(), "values": a[mask].tolist()}


# --------------------------------------------------------------------------------------
# Multiplicity & verdict
# --------------------------------------------------------------------------------------
def p_adjust(pvals: Sequence[float], method: str = "fdr_bh") -> list:
    """Adjust p-values for multiplicity. method: 'fdr_bh' (default) or 'bonferroni'."""
    p = np.asarray(pvals, dtype=float)
    m = p.size
    if method == "bonferroni":
        return list(np.minimum(p * m, 1.0))
    if method == "fdr_bh":
        order = np.argsort(p)
        ranked = p[order] * m / (np.arange(m) + 1)
        ranked = np.minimum.accumulate(ranked[::-1])[::-1]
        out = np.empty(m)
        out[order] = np.minimum(ranked, 1.0)
        return list(out)
    raise ValueError("method must be fdr_bh|bonferroni")


def verdict(p: float, alpha: float = 0.05) -> str:
    """Significance verdict (BM, per the DVS reporting convention)."""
    if p < alpha:
        return "Signifikan"
    if p < 0.10:
        return "Kecenderungan"
    return "Tidak signifikan"


def _require_sm():
    if not _HAS_SM:
        raise ImportError("statsmodels is required for regression functions: pip install statsmodels")


# --------------------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------------------
def _selftest() -> None:
    rng = np.random.default_rng(0)
    ok = 0
    total = 0

    def check(name, cond):
        nonlocal ok, total
        total += 1
        ok += bool(cond)
        print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

    # describe
    d = describe([1, 2, 3, 4, 5])
    check("describe mean=3", abs(d["mean"] - 3) < 1e-9)
    check("describe sd≈1.5811", abs(d["sd"] - 1.5811388) < 1e-4)

    # ci_mean covers true mean for a big normal sample
    big = rng.normal(10, 2, 2000)
    c = ci_mean(big)
    check("ci_mean brackets 10", c["lo"] < 10 < c["hi"])

    # cohen's d of clearly separated groups is large
    a = rng.normal(0, 1, 200); b = rng.normal(1.5, 1, 200)
    es = cohens_d(a, b)
    check("cohens_d large & negative", es["d"] < -1 and es["magnitude"] == "large")

    # independent t detects a real difference
    ti = t_independent(a, b)
    check("t_independent significant", ti["p"] < 0.001 and ti["verdict"] == "Signifikan")

    # ANOVA: identical groups -> not significant; separated -> significant
    an0 = one_way_anova(rng.normal(0, 1, 100), rng.normal(0, 1, 100), rng.normal(0, 1, 100))
    an1 = one_way_anova(rng.normal(0, 1, 100), rng.normal(2, 1, 100), rng.normal(4, 1, 100))
    check("ANOVA null not sig", an0["p"] > 0.05)
    check("ANOVA separated sig + large omega2", an1["p"] < 0.001 and an1["omega2"] > 0.14)

    # correlation recovers a strong positive relationship
    x = np.arange(50, dtype=float); y = 2 * x + rng.normal(0, 3, 50)
    cr = correlation(x, y)
    check("correlation r>0.98", cr["r"] > 0.98 and cr["ci"][0] > 0)

    # gini: equal -> 0, concentrated -> high
    check("gini equal≈0", abs(gini([5, 5, 5, 5])) < 1e-9)
    check("gini concentrated high", gini([0, 0, 0, 100]) > 0.7)

    # shannon: even categories -> evenness 1
    sw = shannon_wiener([10, 10, 10, 10])
    check("shannon evenness≈1", abs(sw["evenness"] - 1.0) < 1e-9)

    # hhi banding
    check("hhi high", hhi([60, 30, 10])["concentration"] == "high")

    # mann-kendall on a monotone series
    mk = mann_kendall([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    check("mann_kendall increasing", mk["trend"] == "increasing" and mk["tau"] > 0.9)

    # cagr: doubling over 1 period = 100%
    check("cagr doubling", abs(cagr(100, 200, 1) - 1.0) < 1e-9)

    # outliers
    oz = outliers_modified_z([1, 2, 2, 2, 3, 2, 100])
    check("modified-z flags 100", 6 in oz["indices"])

    # p_adjust monotonic & bounded
    adj = p_adjust([0.01, 0.02, 0.03], "bonferroni")
    check("bonferroni x3", abs(adj[0] - 0.03) < 1e-9)

    # verdict thresholds
    check("verdict signifikan", verdict(0.01) == "Signifikan")
    check("verdict kecenderungan", verdict(0.07) == "Kecenderungan")
    check("verdict tidak", verdict(0.5) == "Tidak signifikan")

    # regression (if statsmodels present)
    if _HAS_SM:
        import pandas as pd
        n = 200
        entity = rng.integers(0, 5, n)
        fe = entity * 10.0  # time-invariant unit effect
        xx = rng.normal(0, 1, n)
        yy = 3 * xx + fe + rng.normal(0, 1, n)
        frame = pd.DataFrame({"y": yy, "x": xx, "unit": entity})
        r = ols_fit(frame, "y ~ x")
        check("ols recovers slope≈3", abs(r["coefs"]["x"]["beta"] - 3) < 0.5)
        f = fixed_effects(frame, "y", "x", entity="unit")
        check("fixed_effects slope≈3 & sig", abs(f["coefs"]["x"]["beta"] - 3) < 0.5
              and f["coefs"]["x"]["p"] < 0.001)
    else:
        print("  [SKIP] regression tests (statsmodels not installed)")

    print(f"\n{ok}/{total} checks passed.")
    if ok != total:
        raise SystemExit(1)


if __name__ == "__main__":
    import sys
    if "--selftest" in sys.argv:
        _selftest()
    else:
        print(__doc__)
