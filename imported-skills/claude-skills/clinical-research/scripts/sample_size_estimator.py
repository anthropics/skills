#!/usr/bin/env python3
"""sample_size_estimator.py - Closed-form sample-size / power estimates for common trial designs.

Stdlib-only. Deterministic. NO LLM calls. This is an ESTIMATE, not a protocol:
every output prints a banner instructing the user to confirm with a biostatistician.

Supported designs (normal-approximation closed forms):
  - means        two-sample comparison of means (Cohen's d effect size)
  - proportions  two-sample comparison of proportions (arcsine-free normal approx)
  - survival     two-arm log-rank, Schoenfeld events approximation

z-values come from a small built-in lookup table (no scipy dependency).

Usage:
    python3 sample_size_estimator.py --sample
    python3 sample_size_estimator.py --design means --effect 0.5 --alpha 0.05 --power 0.8
    python3 sample_size_estimator.py --design proportions --p1 0.30 --p2 0.45 --dropout 0.15
    python3 sample_size_estimator.py --design survival --hr 0.65 --power 0.9 --output json
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover - skill always ships config_loader
    _cfg = None

BANNER = "ESTIMATE ONLY — confirm with a biostatistician before finalizing the protocol."

# Two-sided z for alpha, and one-sided z for power (1 - beta). Lookup avoids scipy.
Z_ALPHA_TWO_SIDED = {0.10: 1.6449, 0.05: 1.9600, 0.025: 2.2414, 0.01: 2.5758}
Z_POWER = {0.80: 0.8416, 0.85: 1.0364, 0.90: 1.2816, 0.95: 1.6449, 0.975: 1.9600}


def _z_alpha(alpha: float) -> float:
    if alpha not in Z_ALPHA_TWO_SIDED:
        raise ValueError(f"alpha must be one of {sorted(Z_ALPHA_TWO_SIDED)} (two-sided).")
    return Z_ALPHA_TWO_SIDED[alpha]


def _z_power(power: float) -> float:
    if power not in Z_POWER:
        raise ValueError(f"power must be one of {sorted(Z_POWER)}.")
    return Z_POWER[power]


def _inflate(n: float, dropout: float) -> int:
    if not 0.0 <= dropout < 1.0:
        raise ValueError("dropout must be in [0, 1).")
    return math.ceil(n / (1.0 - dropout))


def estimate_means(effect: float, alpha: float, power: float, allocation: float, dropout: float) -> dict:
    """Two-sample means. effect = Cohen's d (standardized mean difference)."""
    if effect <= 0:
        raise ValueError("effect (Cohen's d) must be > 0.")
    za, zb = _z_alpha(alpha), _z_power(power)
    # Equal-n per-arm: n = 2 * ((za + zb) / d)^2 ; unequal handled via allocation ratio k.
    k = allocation
    base = ((za + zb) / effect) ** 2
    n1 = (1 + 1.0 / k) * base
    n2 = (1 + k) * base
    return {
        "design": "means",
        "effect_size_cohens_d": effect,
        "alpha_two_sided": alpha,
        "power": power,
        "allocation_ratio_k": k,
        "n_group1_raw": math.ceil(n1),
        "n_group2_raw": math.ceil(n2),
        "n_group1_with_dropout": _inflate(n1, dropout),
        "n_group2_with_dropout": _inflate(n2, dropout),
        "dropout_assumed": dropout,
        "formula": "n_i = (1 + 1/k or k) * ((z_alpha + z_beta)/d)^2",
    }


def estimate_proportions(p1: float, p2: float, alpha: float, power: float, dropout: float) -> dict:
    """Two-sample proportions, normal approximation (pooled + unpooled variance term)."""
    for p in (p1, p2):
        if not 0.0 < p < 1.0:
            raise ValueError("p1 and p2 must be in (0, 1).")
    if p1 == p2:
        raise ValueError("p1 and p2 must differ.")
    za, zb = _z_alpha(alpha), _z_power(power)
    pbar = (p1 + p2) / 2.0
    delta = abs(p1 - p2)
    num = (za * math.sqrt(2 * pbar * (1 - pbar)) + zb * math.sqrt(p1 * (1 - p1) + p2 * (1 - p2))) ** 2
    n_per_arm = num / (delta ** 2)
    return {
        "design": "proportions",
        "p1": p1,
        "p2": p2,
        "absolute_difference": round(delta, 4),
        "alpha_two_sided": alpha,
        "power": power,
        "n_per_arm_raw": math.ceil(n_per_arm),
        "n_per_arm_with_dropout": _inflate(n_per_arm, dropout),
        "n_total_with_dropout": 2 * _inflate(n_per_arm, dropout),
        "dropout_assumed": dropout,
        "formula": "n = [z_a*sqrt(2*pbar*qbar) + z_b*sqrt(p1q1+p2q2)]^2 / (p1-p2)^2",
    }


def estimate_survival(hr: float, alpha: float, power: float, prob_event: float, dropout: float) -> dict:
    """Two-arm log-rank, Schoenfeld events approximation + n from event probability."""
    if hr <= 0 or hr == 1.0:
        raise ValueError("hazard ratio must be > 0 and != 1.")
    if not 0.0 < prob_event <= 1.0:
        raise ValueError("prob_event (overall probability of event) must be in (0, 1].")
    za, zb = _z_alpha(alpha), _z_power(power)
    log_hr = math.log(hr)
    # Schoenfeld: total events E = 4*(za+zb)^2 / (log HR)^2  (1:1 allocation)
    events = 4.0 * ((za + zb) ** 2) / (log_hr ** 2)
    n_total = events / prob_event
    return {
        "design": "survival",
        "hazard_ratio": hr,
        "alpha_two_sided": alpha,
        "power": power,
        "required_events_raw": math.ceil(events),
        "overall_event_probability": prob_event,
        "n_total_raw": math.ceil(n_total),
        "n_total_with_dropout": _inflate(n_total, dropout),
        "dropout_assumed": dropout,
        "formula": "E = 4*(z_a+z_b)^2 / (ln HR)^2 ; n = E / P(event)",
    }


def _render_human(result: dict) -> str:
    lines = [f"!! {BANNER}", "", f"Design: {result['design']}", ""]
    for k, v in result.items():
        if k == "design":
            continue
        lines.append(f"  {k:28s} : {v}")
    lines += [
        "",
        "Assumptions block (state these in the protocol statistical section):",
        f"  - alpha (two-sided): {result.get('alpha_two_sided')}",
        f"  - power (1 - beta):  {result.get('power')}",
        f"  - dropout inflation: {result.get('dropout_assumed')}",
        "  - The effect/difference/HR must trace to a published or anchor-based source.",
        "",
        f"Named owner required: {result.get('_biostatistician') or 'a biostatistician (run onboard.py to name one)'} "
        "must sign the final sample-size justification.",
    ]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Closed-form clinical sample-size / power estimates (ESTIMATE ONLY).")
    p.add_argument("--design", choices=["means", "proportions", "survival"], default="means")
    p.add_argument("--alpha", type=float, default=None, help="two-sided alpha (0.10/0.05/0.025/0.01)")
    p.add_argument("--power", type=float, default=None, help="target power (0.80/0.85/0.90/0.95/0.975)")
    p.add_argument("--dropout", type=float, default=None, help="anticipated dropout fraction [0,1)")
    # means
    p.add_argument("--effect", type=float, default=0.5, help="Cohen's d (means design)")
    p.add_argument("--allocation", type=float, default=1.0, help="allocation ratio k = n2/n1 (means)")
    # proportions
    p.add_argument("--p1", type=float, default=0.30, help="control proportion")
    p.add_argument("--p2", type=float, default=0.45, help="treatment proportion")
    # survival
    p.add_argument("--hr", type=float, default=0.65, help="hazard ratio (survival)")
    p.add_argument("--prob-event", type=float, default=0.60, help="overall probability of event (survival)")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="run the embedded sample (means design)")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    alpha = args.alpha if args.alpha is not None else conf.get("default_alpha", 0.05)
    power = args.power if args.power is not None else conf.get("default_power", 0.80)
    dropout = args.dropout if args.dropout is not None else conf.get("default_dropout", 0.0)
    biostat = (conf.get("owners") or {}).get("biostatistician")

    try:
        if args.sample:
            result = estimate_means(0.5, alpha, power, 1.0, dropout if dropout else 0.15)
        elif args.design == "means":
            result = estimate_means(args.effect, alpha, power, args.allocation, dropout)
        elif args.design == "proportions":
            result = estimate_proportions(args.p1, args.p2, alpha, power, dropout)
        else:
            result = estimate_survival(args.hr, alpha, power, args.prob_event, dropout)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    result["_biostatistician"] = biostat

    if args.output == "json":
        result["_banner"] = BANNER
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
