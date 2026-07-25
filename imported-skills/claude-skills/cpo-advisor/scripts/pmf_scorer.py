#!/usr/bin/env python3
"""
PMF Scorer — Multi-dimensional Product-Market Fit analysis.

Scores PMF across four dimensions:
  - Retention   (40%): D30 and D90 cohort retention
  - Engagement  (25%): DAU/MAU, session depth, key action rate
  - Satisfaction(20%): Sean Ellis score, NPS
  - Growth      (15%): Organic signup rate, referral rate

Usage:
    python pmf_scorer.py                    # Run with built-in sample data
    python pmf_scorer.py --input data.json  # Run with your data

JSON input format: see sample_data() function below.
"""

import json
import sys
import argparse
import math
from typing import Optional


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

def sample_data() -> dict:
    """
    Sample input data. Replace with your own values.

    All fields are optional — missing fields score 0 for that sub-metric
    and a note is added to recommendations.
    """
    return {
        "product_name": "Acme SaaS",
        "business_model": "b2b_saas",  # b2b_saas | consumer | marketplace | plg

        # Retention: D30 and D90 as decimals (e.g. 0.42 = 42%)
        # Provide multiple cohorts if available. Most recent first.
        "retention": {
            "d30_cohorts": [0.38, 0.41, 0.44, 0.43],  # newest → oldest
            "d90_cohorts": [0.28, 0.30, 0.31],
            "curve_flattening": True,  # Does the curve flatten (vs. continuing to drop)?
        },

        # Engagement
        "engagement": {
            "dau_mau_ratio": 0.24,           # Daily active / Monthly active (decimal)
            "avg_sessions_per_week": 3.2,    # Per active user
            "key_action_rate": 0.55,         # % of users who performed core value action in last 30d
            "session_depth_score": 0.6,      # 0-1: 0 = one page, 1 = full feature exploration
        },

        # Satisfaction
        "satisfaction": {
            "sean_ellis_very_disappointed": 0.38,  # Fraction (e.g. 0.38 = 38%)
            "sean_ellis_sample_size": 87,           # Raw response count
            "nps_score": 34,                        # -100 to 100
            "nps_sample_size": 210,
        },

        # Growth
        "growth": {
            "organic_signup_pct": 0.27,     # % of new signups from organic/referral/WOM
            "referral_rate": 0.18,          # % of active users who referred someone last 90d
            "mom_growth_rate": 0.08,        # Month-over-month new user growth (decimal)
        },
    }


# ---------------------------------------------------------------------------
# Thresholds by business model
# ---------------------------------------------------------------------------

THRESHOLDS = {
    "b2b_saas": {
        "d30_pmf": 0.40,   "d30_strong": 0.60,
        "d90_pmf": 0.25,   "d90_strong": 0.45,
        "dau_mau_pmf": 0.15, "dau_mau_strong": 0.35,
        "sean_ellis_pmf": 0.40, "sean_ellis_strong": 0.55,
        "nps_pmf": 30, "nps_strong": 50,
    },
    "consumer": {
        "d30_pmf": 0.20,   "d30_strong": 0.35,
        "d90_pmf": 0.10,   "d90_strong": 0.20,
        "dau_mau_pmf": 0.20, "dau_mau_strong": 0.40,
        "sean_ellis_pmf": 0.40, "sean_ellis_strong": 0.55,
        "nps_pmf": 20, "nps_strong": 45,
    },
    "marketplace": {
        "d30_pmf": 0.30,   "d30_strong": 0.50,
        "d90_pmf": 0.20,   "d90_strong": 0.35,
        "dau_mau_pmf": 0.15, "dau_mau_strong": 0.30,
        "sean_ellis_pmf": 0.40, "sean_ellis_strong": 0.55,
        "nps_pmf": 25, "nps_strong": 45,
    },
    "plg": {
        "d30_pmf": 0.25,   "d30_strong": 0.45,
        "d90_pmf": 0.15,   "d90_strong": 0.30,
        "dau_mau_pmf": 0.20, "dau_mau_strong": 0.40,
        "sean_ellis_pmf": 0.40, "sean_ellis_strong": 0.55,
        "nps_pmf": 30, "nps_strong": 50,
    },
}

# Weights for the four dimensions (must sum to 1.0)
DIMENSION_WEIGHTS = {
    "retention":    0.40,
    "engagement":   0.25,
    "satisfaction": 0.20,
    "growth":       0.15,
}


# ---------------------------------------------------------------------------
# Scoring helpers
# ---------------------------------------------------------------------------

def clamp(value: float, lo: float = 0.0, hi: float = 1.0) -> float:
    return max(lo, min(hi, value))


def score_between(value: Optional[float], lo: float, hi: float) -> float:
    """Linear interpolation: lo → 0.0, hi → 1.0, beyond hi → 1.0."""
    if value is None:
        return 0.0
    if value <= lo:
        return 0.0
    if value >= hi:
        return 1.0
    return (value - lo) / (hi - lo)


def cohort_trend(cohorts: list) -> float:
    """
    Given cohorts newest-first, return a trend score -1 to +1.
    Positive = improving. Negative = degrading.
    """
    if len(cohorts) < 2:
        return 0.0
    # Simple: compare most recent half average vs. older half average
    mid = len(cohorts) // 2
    recent_avg = sum(cohorts[:mid]) / mid if mid else cohorts[0]
    older_avg = sum(cohorts[mid:]) / (len(cohorts) - mid)
    if older_avg == 0:
        return 0.0
    delta = (recent_avg - older_avg) / older_avg
    return clamp(delta * 5, -1.0, 1.0)  # scale: 20% improvement = score of 1.0


# ---------------------------------------------------------------------------
# Dimension scorers
# ---------------------------------------------------------------------------

def score_retention(data: dict, thresholds: dict) -> tuple[float, list]:
    """Returns (score 0-1, list of findings)."""
    r = data.get("retention", {})
    findings = []
    scores = []

    d30 = r.get("d30_cohorts", [])
    d90 = r.get("d90_cohorts", [])

    if not d30:
        findings.append("⚠ No D30 retention data — this is the most important PMF signal. Instrument it immediately.")
        return 0.0, findings

    latest_d30 = d30[0]
    d30_score = score_between(latest_d30, 0, thresholds["d30_strong"])
    scores.append(d30_score)

    if latest_d30 >= thresholds["d30_strong"]:
        findings.append(f"✓ D30 retention {latest_d30:.0%} — strong PMF signal")
    elif latest_d30 >= thresholds["d30_pmf"]:
        findings.append(f"◑ D30 retention {latest_d30:.0%} — approaching PMF threshold ({thresholds['d30_pmf']:.0%})")
    else:
        findings.append(f"✗ D30 retention {latest_d30:.0%} — below PMF threshold ({thresholds['d30_pmf']:.0%}). Focus here before anything else.")

    # Trend bonus
    if len(d30) >= 2:
        trend = cohort_trend(d30)
        trend_score = (trend + 1) / 2  # normalize to 0-1
        scores.append(trend_score * 0.5)  # trend is bonus, not primary
        if trend > 0.1:
            findings.append(f"✓ D30 retention improving across cohorts — strong learning signal")
        elif trend < -0.1:
            findings.append(f"✗ D30 retention declining across cohorts — product changes may be hurting core users")

    if d90:
        latest_d90 = d90[0]
        d90_score = score_between(latest_d90, 0, thresholds["d90_strong"])
        scores.append(d90_score)
        if latest_d90 >= thresholds["d90_strong"]:
            findings.append(f"✓ D90 retention {latest_d90:.0%} — excellent long-term retention")
        elif latest_d90 >= thresholds["d90_pmf"]:
            findings.append(f"◑ D90 retention {latest_d90:.0%} — some long-term value demonstrated")
        else:
            findings.append(f"✗ D90 retention {latest_d90:.0%} — users not finding long-term value")
    else:
        findings.append("⚠ No D90 data. Add 90-day cohort tracking.")

    flattening = r.get("curve_flattening", False)
    if flattening:
        scores.append(0.8)
        findings.append("✓ Retention curve flattening — core retained segment exists")
    else:
        scores.append(0.2)
        findings.append("✗ Retention curve not flattening — no stable retained segment yet")

    return clamp(sum(scores) / len(scores)), findings


def score_engagement(data: dict, thresholds: dict) -> tuple[float, list]:
    e = data.get("engagement", {})
    findings = []
    scores = []

    dau_mau = e.get("dau_mau_ratio")
    if dau_mau is not None:
        s = score_between(dau_mau, 0, thresholds["dau_mau_strong"])
        scores.append(s)
        if dau_mau >= thresholds["dau_mau_strong"]:
            findings.append(f"✓ DAU/MAU {dau_mau:.0%} — strong daily habit")
        elif dau_mau >= thresholds["dau_mau_pmf"]:
            findings.append(f"◑ DAU/MAU {dau_mau:.0%} — moderate engagement")
        else:
            findings.append(f"✗ DAU/MAU {dau_mau:.0%} — users not building a habit. Find the daily job or accept weekly use pattern.")
    else:
        findings.append("⚠ No DAU/MAU data.")

    sessions = e.get("avg_sessions_per_week")
    if sessions is not None:
        # 5+ sessions/week = strong, 2 = threshold
        s = score_between(sessions, 1, 5)
        scores.append(s)
        if sessions >= 5:
            findings.append(f"✓ {sessions:.1f} sessions/week — high engagement")
        elif sessions >= 2:
            findings.append(f"◑ {sessions:.1f} sessions/week — moderate")
        else:
            findings.append(f"✗ {sessions:.1f} sessions/week — very low. Users not returning within week.")
    else:
        findings.append("⚠ No session frequency data.")

    kar = e.get("key_action_rate")
    if kar is not None:
        s = score_between(kar, 0.10, 0.70)
        scores.append(s)
        if kar >= 0.60:
            findings.append(f"✓ Key action rate {kar:.0%} — core value well-adopted")
        elif kar >= 0.30:
            findings.append(f"◑ Key action rate {kar:.0%} — improve onboarding to drive this up")
        else:
            findings.append(f"✗ Key action rate {kar:.0%} — most users not reaching core value. This is an activation problem.")
    else:
        findings.append("⚠ No key action rate. Define your 'aha moment' action and track it.")

    depth = e.get("session_depth_score")
    if depth is not None:
        scores.append(depth)
        if depth >= 0.6:
            findings.append(f"✓ Session depth {depth:.1f} — users exploring the product")
        else:
            findings.append(f"◑ Session depth {depth:.1f} — users sticking to narrow feature set")

    if not scores:
        return 0.0, findings
    return clamp(sum(scores) / len(scores)), findings


def score_satisfaction(data: dict, thresholds: dict) -> tuple[float, list]:
    s_data = data.get("satisfaction", {})
    findings = []
    scores = []

    se_score = s_data.get("sean_ellis_very_disappointed")
    se_n = s_data.get("sean_ellis_sample_size", 0)
    if se_score is not None:
        if se_n < 40:
            findings.append(f"⚠ Sean Ellis n={se_n} — too small to be reliable. Need 40+ responses.")
            scores.append(score_between(se_score, 0, thresholds["sean_ellis_strong"]) * 0.5)  # half weight
        else:
            s = score_between(se_score, 0, thresholds["sean_ellis_strong"])
            scores.append(s)
            if se_score >= thresholds["sean_ellis_strong"]:
                findings.append(f"✓ Sean Ellis {se_score:.0%} 'very disappointed' — strong PMF signal (n={se_n})")
            elif se_score >= thresholds["sean_ellis_pmf"]:
                findings.append(f"◑ Sean Ellis {se_score:.0%} — at PMF threshold. Push to > {thresholds['sean_ellis_strong']:.0%}.")
            else:
                findings.append(f"✗ Sean Ellis {se_score:.0%} — below {thresholds['sean_ellis_pmf']:.0%} threshold. Interview 'somewhat disappointed' group.")
    else:
        findings.append("⚠ No Sean Ellis data. Run a one-question survey to your active users now.")

    nps = s_data.get("nps_score")
    nps_n = s_data.get("nps_sample_size", 0)
    if nps is not None:
        if nps_n < 50:
            findings.append(f"⚠ NPS n={nps_n} — sample too small. Need 50+ for reliability.")
        # NPS ranges from -100 to 100; normalize to 0-1 against threshold
        s = score_between(nps, -20, thresholds["nps_strong"])
        scores.append(s)
        if nps >= thresholds["nps_strong"]:
            findings.append(f"✓ NPS {nps} — excellent. Promoters will drive organic growth.")
        elif nps >= thresholds["nps_pmf"]:
            findings.append(f"◑ NPS {nps} — acceptable. Focus on converting passives to promoters.")
        elif nps >= 0:
            findings.append(f"✗ NPS {nps} — low. More detractors than promoters is a warning sign.")
        else:
            findings.append(f"✗ NPS {nps} — negative. Active detractors outnumber promoters.")
    else:
        findings.append("⚠ No NPS data.")

    if not scores:
        return 0.0, findings
    return clamp(sum(scores) / len(scores)), findings


def score_growth(data: dict, _thresholds: dict) -> tuple[float, list]:
    g = data.get("growth", {})
    findings = []
    scores = []

    organic_pct = g.get("organic_signup_pct")
    if organic_pct is not None:
        s = score_between(organic_pct, 0.05, 0.50)
        scores.append(s)
        if organic_pct >= 0.30:
            findings.append(f"✓ {organic_pct:.0%} organic signups — word of mouth is working")
        elif organic_pct >= 0.20:
            findings.append(f"◑ {organic_pct:.0%} organic — moderate. Build referral loop deliberately.")
        else:
            findings.append(f"✗ {organic_pct:.0%} organic — almost all paid. PMF may not be strong enough to generate word of mouth.")
    else:
        findings.append("⚠ No organic signup tracking. Tag all signup sources now.")

    referral = g.get("referral_rate")
    if referral is not None:
        s = score_between(referral, 0.05, 0.35)
        scores.append(s)
        if referral >= 0.25:
            findings.append(f"✓ {referral:.0%} of active users referring — strong viral signal")
        elif referral >= 0.15:
            findings.append(f"◑ {referral:.0%} referral rate — building. Add referral incentive or friction removal.")
        else:
            findings.append(f"✗ {referral:.0%} referral rate — users not recommending. Satisfaction or network effects missing.")
    else:
        findings.append("⚠ No referral rate data.")

    mom = g.get("mom_growth_rate")
    if mom is not None:
        s = score_between(mom, 0, 0.20)
        scores.append(s)
        if mom >= 0.15:
            findings.append(f"✓ {mom:.0%} MoM growth — strong momentum")
        elif mom >= 0.08:
            findings.append(f"◑ {mom:.0%} MoM growth — moderate. Identify top acquisition channel and double it.")
        else:
            findings.append(f"✗ {mom:.0%} MoM growth — slow. Acquisition is a bottleneck.")

    if not scores:
        return 0.0, findings
    return clamp(sum(scores) / len(scores)), findings


# ---------------------------------------------------------------------------
# Overall scoring and recommendations
# ---------------------------------------------------------------------------

def pmf_status(overall: float) -> tuple[str, str]:
    """Returns (status label, description)."""
    if overall >= 0.80:
        return "STRONG PMF", "Clear product-market fit. Shift focus to scaling acquisition and defending moat."
    elif overall >= 0.60:
        return "PMF APPROACHING", "Meaningful signals present. Identify and remove the 1-2 friction points blocking retention."
    elif overall >= 0.40:
        return "EARLY SIGNALS", "Weak PMF. Some users find value. Narrow your ICP and double down on what's working."
    elif overall >= 0.20:
        return "PRE-PMF", "No clear PMF yet. Don't scale acquisition. Focus entirely on retention experiments."
    else:
        return "NO SIGNAL", "No PMF signals detected. Revisit the problem hypothesis before investing further in the solution."


def top_recommendations(dim_scores: dict, data: dict) -> list[str]:
    """Prioritized recommendations based on weakest dimensions."""
    recs = []
    model = data.get("business_model", "b2b_saas")

    ranked = sorted(dim_scores.items(), key=lambda x: x[1])

    for dim, score in ranked:
        if score < 0.40:
            if dim == "retention":
                recs.append(
                    "CRITICAL — Retention: Run cohort analysis by segment. Find the cohort with highest D30. "
                    "Interview 10 of those users. Build for them exclusively until retention flattens."
                )
            elif dim == "engagement":
                recs.append(
                    "Engagement: Define your 'aha moment' — the one action that predicts long-term retention. "
                    "Measure time-to-aha. Remove every friction point on that path."
                )
            elif dim == "satisfaction":
                recs.append(
                    "Satisfaction: Run Sean Ellis survey immediately (need n ≥ 40). "
                    "Interview every 'somewhat disappointed' user — the gap between 'somewhat' and 'very' is your product gap."
                )
            elif dim == "growth":
                recs.append(
                    "Growth: Track signup source for every new user. If organic < 20%, "
                    "you may be papering over weak PMF with paid acquisition. Fix retention first."
                )

    if not recs:
        recs.append(
            "All dimensions scoring above threshold. Focus: "
            "(1) Defend moat, (2) Expand ICP carefully, (3) Build referral flywheel."
        )

    if model == "b2b_saas":
        recs.append("B2B tip: Track NRR (Net Revenue Retention). PMF in B2B requires expansion, not just retention.")
    elif model == "consumer":
        recs.append("Consumer tip: Find your D7 'magic moment'. The habit window is small — optimize for it.")
    elif model == "plg":
        recs.append("PLG tip: Define your PQL (product-qualified lead). The activation event that predicts paid conversion.")
    elif model == "marketplace":
        recs.append("Marketplace tip: Measure both sides separately. PMF on demand side ≠ PMF on supply side.")

    return recs


# ---------------------------------------------------------------------------
# Report renderer
# ---------------------------------------------------------------------------

def render_report(data: dict, dim_scores: dict, dim_findings: dict, overall: float) -> str:
    status, description = pmf_status(overall)
    recs = top_recommendations(dim_scores, data)

    lines = []
    lines.append("=" * 60)
    lines.append(f"  PMF SCORER — {data.get('product_name', 'Product')}")
    lines.append(f"  Model: {data.get('business_model', 'unknown').upper()}")
    lines.append("=" * 60)
    lines.append("")

    # Overall
    bar_len = 40
    filled = round(overall * bar_len)
    bar = "█" * filled + "░" * (bar_len - filled)
    lines.append(f"  Overall PMF Score: {overall:.0%}")
    lines.append(f"  [{bar}]")
    lines.append(f"  Status: {status}")
    lines.append(f"  {description}")
    lines.append("")

    # Dimension breakdown
    lines.append("  DIMENSION SCORES")
    lines.append("  " + "-" * 50)
    for dim, weight in DIMENSION_WEIGHTS.items():
        score = dim_scores.get(dim, 0.0)
        dim_bar_len = 20
        dim_filled = round(score * dim_bar_len)
        dim_bar = "█" * dim_filled + "░" * (dim_bar_len - dim_filled)
        label = dim.capitalize().ljust(12)
        lines.append(f"  {label} [{dim_bar}] {score:.0%}  (weight: {weight:.0%})")
    lines.append("")

    # Findings per dimension
    for dim in ["retention", "engagement", "satisfaction", "growth"]:
        findings = dim_findings.get(dim, [])
        if findings:
            lines.append(f"  {dim.upper()} FINDINGS")
            for f in findings:
                lines.append(f"    {f}")
            lines.append("")

    # Recommendations
    lines.append("  PRIORITIZED RECOMMENDATIONS")
    lines.append("  " + "-" * 50)
    for i, rec in enumerate(recs, 1):
        # Wrap at 70 chars
        words = rec.split()
        line = f"  {i}. "
        for word in words:
            if len(line) + len(word) + 1 > 72:
                lines.append(line)
                line = "     " + word + " "
            else:
                line += word + " "
        lines.append(line.rstrip())
    lines.append("")
    lines.append("=" * 60)

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(data: dict) -> dict:
    """
    Score PMF from input data dict.
    Returns dict with overall score, dimension scores, and findings.
    """
    model = data.get("business_model", "b2b_saas")
    thresholds = THRESHOLDS.get(model, THRESHOLDS["b2b_saas"])

    dim_scores = {}
    dim_findings = {}

    ret_score, ret_findings = score_retention(data, thresholds)
    dim_scores["retention"] = ret_score
    dim_findings["retention"] = ret_findings

    eng_score, eng_findings = score_engagement(data, thresholds)
    dim_scores["engagement"] = eng_score
    dim_findings["engagement"] = eng_findings

    sat_score, sat_findings = score_satisfaction(data, thresholds)
    dim_scores["satisfaction"] = sat_score
    dim_findings["satisfaction"] = sat_findings

    grow_score, grow_findings = score_growth(data, thresholds)
    dim_scores["growth"] = grow_score
    dim_findings["growth"] = grow_findings

    overall = sum(
        dim_scores[dim] * weight
        for dim, weight in DIMENSION_WEIGHTS.items()
    )

    return {
        "overall": overall,
        "dim_scores": dim_scores,
        "dim_findings": dim_findings,
        "status": pmf_status(overall)[0],
    }


def main():
    parser = argparse.ArgumentParser(
        description="PMF Scorer — Multi-dimensional Product-Market Fit analysis",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--input", "-i",
        metavar="FILE",
        help="JSON file with your product data (default: built-in sample data)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output raw JSON instead of formatted report",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Run with the built-in sample data (no notice line — safe for JSON piping)",
    )
    args = parser.parse_args()

    if args.sample:
        # --sample wins over --input, consistent with the other sample-pattern tools.
        if args.input:
            print("Warning: --sample specified; ignoring --input", file=sys.stderr)
        data = sample_data()
    elif args.input:
        try:
            with open(args.input) as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"Error: file not found: {args.input}", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: invalid JSON: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        # Notice goes to stderr so `--json` output stays parseable when piped.
        print("No input file provided — running with sample data.\n", file=sys.stderr)
        data = sample_data()

    result = run(data)

    if args.json:
        output = {
            "product_name": data.get("product_name"),
            "business_model": data.get("business_model"),
            "overall_score": round(result["overall"], 4),
            "overall_pct": f"{result['overall']:.0%}",
            "status": result["status"],
            "dimensions": {
                dim: {
                    "score": round(result["dim_scores"][dim], 4),
                    "pct": f"{result['dim_scores'][dim]:.0%}",
                    "weight": f"{DIMENSION_WEIGHTS[dim]:.0%}",
                    "findings": result["dim_findings"][dim],
                }
                for dim in DIMENSION_WEIGHTS
            },
        }
        print(json.dumps(output, indent=2))
    else:
        print(render_report(data, result["dim_scores"], result["dim_findings"], result["overall"]))


if __name__ == "__main__":
    main()
