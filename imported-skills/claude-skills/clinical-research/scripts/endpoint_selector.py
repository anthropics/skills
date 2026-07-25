#!/usr/bin/env python3
"""endpoint_selector.py - Score candidate clinical endpoints and classify each.

Stdlib-only. Deterministic. NO LLM calls. ESTIMATE / decision-support only —
endpoint selection must be confirmed by a clinician + biostatistician + regulatory owner.

Each candidate endpoint is scored 0-100 across 5 weighted dimensions:
  1. clinical_relevance     does it measure benefit patients care about?       (weight 0.30)
  2. measurability          validated instrument, low measurement error?       (weight 0.20)
  3. regulatory_acceptance  precedent acceptance by FDA/EMA for this indication (weight 0.25)
  4. sensitivity_to_change  can it detect treatment effect in the trial window? (weight 0.15)
  5. burden                 patient/site burden (inverted: low burden = high)  (weight 0.10)

Classification:
  - top composite           -> PRIMARY
  - composite >= 60         -> KEY-SECONDARY
  - else                    -> EXPLORATORY
Surrogate endpoints flagged when is_surrogate=true and not validated.

Profiles tune the regulatory-acceptance prior by development area.

Usage:
    python3 endpoint_selector.py --sample
    python3 endpoint_selector.py --input endpoints.json --profile drug
    python3 endpoint_selector.py --input endpoints.json --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

BANNER = "ESTIMATE ONLY — endpoint selection must be confirmed by clinician + biostatistician + regulatory owner."

WEIGHTS = {
    "clinical_relevance": 0.30,
    "measurability": 0.20,
    "regulatory_acceptance": 0.25,
    "sensitivity_to_change": 0.15,
    "burden": 0.10,
}

# Per-area regulatory-acceptance multiplier applied to the regulatory_acceptance score.
PROFILES = {
    "drug": 1.00,
    "device": 0.95,
    "biologic": 1.00,
    "diagnostic": 0.90,
    "digital-therapeutic": 0.80,
}

SAMPLE = {
    "indication": "moderate-to-severe plaque psoriasis",
    "endpoints": [
        {
            "name": "PASI-75 at week 16",
            "is_surrogate": False,
            "validated": True,
            "scores": {"clinical_relevance": 90, "measurability": 85, "regulatory_acceptance": 95,
                       "sensitivity_to_change": 90, "burden": 80},
        },
        {
            "name": "Serum cytokine level at week 4",
            "is_surrogate": True,
            "validated": False,
            "scores": {"clinical_relevance": 40, "measurability": 90, "regulatory_acceptance": 30,
                       "sensitivity_to_change": 85, "burden": 50},
        },
        {
            "name": "DLQI (quality of life) at week 16",
            "is_surrogate": False,
            "validated": True,
            "scores": {"clinical_relevance": 75, "measurability": 70, "regulatory_acceptance": 70,
                       "sensitivity_to_change": 65, "burden": 75},
        },
    ],
}


def score_endpoint(ep: dict, profile_mult: float) -> dict:
    raw = ep.get("scores", {})
    flags: list[str] = []
    composite = 0.0
    breakdown = {}
    for dim, w in WEIGHTS.items():
        s = float(raw.get(dim, 0.0))
        if dim == "regulatory_acceptance":
            s = min(100.0, s * profile_mult)
        composite += s * w
        breakdown[dim] = round(s, 1)
    if ep.get("is_surrogate") and not ep.get("validated"):
        flags.append("UNVALIDATED SURROGATE — not on a validated-surrogate table; confirm acceptability")
        composite *= 0.7  # heavy penalty: unvalidated surrogate cannot anchor a primary endpoint
    return {
        "name": ep.get("name", "UNNAMED"),
        "composite": round(composite, 1),
        "breakdown": breakdown,
        "is_surrogate": bool(ep.get("is_surrogate")),
        "validated": bool(ep.get("validated")),
        "flags": flags,
    }


def classify(scored: list[dict]) -> list[dict]:
    if not scored:
        return scored
    ordered = sorted(scored, key=lambda x: x["composite"], reverse=True)
    top = ordered[0]["composite"]
    for i, s in enumerate(ordered):
        if i == 0 and not s["flags"]:
            s["classification"] = "PRIMARY"
        elif i == 0 and s["flags"]:
            s["classification"] = "KEY-SECONDARY (flagged — cannot be primary)"
        elif s["composite"] >= 60.0:
            s["classification"] = "KEY-SECONDARY"
        else:
            s["classification"] = "EXPLORATORY"
    return ordered


def evaluate(data: dict, profile: str) -> dict:
    if profile not in PROFILES:
        raise ValueError(f"Unknown profile '{profile}'. Choose from {list(PROFILES)}.")
    mult = PROFILES[profile]
    scored = [score_endpoint(ep, mult) for ep in data.get("endpoints", [])]
    scored = classify(scored)
    return {
        "indication": data.get("indication", "UNSPECIFIED"),
        "profile": profile,
        "endpoints": scored,
        "note": "Multiplicity control (e.g., hierarchical alpha allocation) required if >1 primary endpoint.",
    }


def _render_human(result: dict) -> str:
    lines = [f"!! {BANNER}", "", f"Indication: {result['indication']}  (profile: {result['profile']})", ""]
    for ep in result["endpoints"]:
        lines.append(f"[{ep['classification']}] {ep['name']}  — composite {ep['composite']}/100")
        for dim, s in ep["breakdown"].items():
            lines.append(f"      {dim:24s} {s}")
        for f in ep["flags"]:
            lines.append(f"      ! {f}")
        lines.append("")
    lines.append(f"note: {result['note']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Score and classify candidate clinical endpoints (ESTIMATE ONLY).")
    p.add_argument("--input", help="Path to JSON with {indication, endpoints[]}")
    p.add_argument("--profile", default=None, choices=list(PROFILES),
                   help="overrides onboarding default_profile")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    profile = args.profile or conf.get("default_profile", "drug")
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    try:
        result = evaluate(data, profile)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output == "json":
        result["_banner"] = BANNER
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
