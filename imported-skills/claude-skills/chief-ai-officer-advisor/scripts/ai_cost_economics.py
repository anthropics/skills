#!/usr/bin/env python3
"""ai_cost_economics.py — API vs self-hosted inference breakeven analysis.

Stdlib-only. Takes a workload profile and outputs:
  - Monthly API cost at three tiers (frontier-premium, frontier-economy, open-hosted)
  - Monthly self-hosted cost (GPU rental + ops, at chosen model size)
  - Breakeven point: where API and self-hosted cross
  - Sensitivity: low/mid/high GPU rate scenarios
  - Recommended path with explicit caveats

Deterministic logic derived from the profile.

Input schema (JSON):
{
  "workload_name": "Customer support generation",
  "monthly_input_tokens_m": 600,        # millions of input tokens per month
  "monthly_output_tokens_m": 150,
  "quality_tier_required": "frontier-economy",  # frontier-premium | frontier-economy | open-hosted
  "model_size_class_self_host": "70b-class",    # 7b-13b | 70b-class
  "latency_p95_target_ms": 1500,
  "utilization_assumed_pct": 70,                # realistic GPU utilization for self-hosting
  "include_ops_attribution": true               # 30% of an engineer attributed to self-hosted ops
}

Usage:
    python ai_cost_economics.py                       # uses embedded 5M tokens/day sample
    python ai_cost_economics.py path/to/workload.json
    python ai_cost_economics.py workload.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "workload_name": "B2B SaaS customer-support generation (5M tokens/day)",
    "monthly_input_tokens_m": 600,
    "monthly_output_tokens_m": 150,
    "quality_tier_required": "frontier-economy",
    "model_size_class_self_host": "70b-class",
    "latency_p95_target_ms": 1500,
    "utilization_assumed_pct": 70,
    "include_ops_attribution": True,
}


# 2026 API pricing per million tokens, $USD (input / output)
API_PRICING = {
    "frontier-premium": {"input": 3.00, "output": 15.00, "label": "Claude Sonnet 4.6 / GPT-4o-tier"},
    "frontier-economy": {"input": 1.25, "output": 5.00, "label": "Gemini 2.5 Flash / Claude Haiku 4.5-tier"},
    "open-hosted": {"input": 0.50, "output": 1.50, "label": "Llama 3.1 70B / Qwen 2.5 72B via hosted endpoint"},
}

# GPU spot pricing 2026 ($/hour). Mid-range; varies by provider and commitment.
GPU_PRICING = {
    "A100-spot-low": 1.50,
    "A100-spot-mid": 2.50,
    "A100-spot-high": 3.50,
    "H100-spot-low": 3.50,
    "H100-spot-mid": 5.00,
    "H100-spot-high": 8.00,
}

# Tokens per second per GPU at 70% utilization (rough)
TOKENS_PER_GPU_PER_SEC = {
    "7b-13b": {"A100": 1500, "H100": 3500},
    "70b-class": {"A100": 200, "H100": 600},
}

# Number of GPUs needed for model (minimum, with KV cache)
GPUS_PER_MODEL = {
    "7b-13b": 1,
    "70b-class": 4,   # 70B at FP16 needs ~140GB; 4xA100-40GB or 2xH100-80GB
}

# Engineer fully-loaded cost (annual)
ENGINEER_FULLY_LOADED = 250_000
OPS_ATTRIBUTION_PCT = 0.30   # 30% of an engineer attributed to self-hosted ops


def api_monthly_cost(profile: Dict[str, Any], tier: str) -> float:
    pricing = API_PRICING.get(tier, API_PRICING["frontier-economy"])
    return (
        profile.get("monthly_input_tokens_m", 0) * pricing["input"]
        + profile.get("monthly_output_tokens_m", 0) * pricing["output"]
    )


def self_hosted_monthly_cost(profile: Dict[str, Any], gpu_type: str, gpu_pricing_tier: str) -> Dict[str, Any]:
    """Compute self-hosted monthly cost for given GPU type and pricing tier."""
    model_class = profile.get("model_size_class_self_host", "70b-class")
    utilization = profile.get("utilization_assumed_pct", 70) / 100
    monthly_tokens_total_m = profile.get("monthly_input_tokens_m", 0) + profile.get("monthly_output_tokens_m", 0)
    monthly_tokens_total = monthly_tokens_total_m * 1_000_000

    gpus_needed = GPUS_PER_MODEL[model_class]
    tokens_per_sec_per_gpu = TOKENS_PER_GPU_PER_SEC[model_class][gpu_type]
    effective_tokens_per_sec = gpus_needed * tokens_per_sec_per_gpu * utilization

    # Hours of GPU time needed per month
    seconds_per_month = monthly_tokens_total / effective_tokens_per_sec
    hours_per_month = seconds_per_month / 3600

    # But minimum: GPUs must be warm 24/7 if we want consistent latency
    # So actual hours = max(hours_per_month, 24 * 30 * gpus_needed)
    hours_warm = 24 * 30 * gpus_needed
    hours_billable = max(hours_per_month, hours_warm)

    gpu_pricing_key = f"{gpu_type}-spot-{gpu_pricing_tier}"
    rate = GPU_PRICING[gpu_pricing_key]
    gpu_cost = hours_billable * rate / gpus_needed * gpus_needed  # already per GPU

    ops_cost = (ENGINEER_FULLY_LOADED * OPS_ATTRIBUTION_PCT) / 12 if profile.get("include_ops_attribution", True) else 0

    return {
        "gpu_cost": round(gpu_cost, 0),
        "ops_cost": round(ops_cost, 0),
        "total": round(gpu_cost + ops_cost, 0),
        "hours_warm_required": int(hours_warm),
        "hours_compute_required": int(hours_per_month),
        "gpus_needed": gpus_needed,
        "gpu_rate_per_hr": rate,
    }


def find_breakeven(profile: Dict[str, Any], api_tier: str, gpu_type: str, gpu_pricing_tier: str) -> Dict[str, Any]:
    """Find the monthly token volume where API and self-hosted cost cross."""
    # API cost is linear in tokens; self-hosted has fixed (warm GPU) + linear component
    model_class = profile.get("model_size_class_self_host", "70b-class")
    utilization = profile.get("utilization_assumed_pct", 70) / 100
    gpus_needed = GPUS_PER_MODEL[model_class]
    tokens_per_sec_per_gpu = TOKENS_PER_GPU_PER_SEC[model_class][gpu_type]
    effective_tokens_per_sec = gpus_needed * tokens_per_sec_per_gpu * utilization

    gpu_pricing_key = f"{gpu_type}-spot-{gpu_pricing_tier}"
    rate = GPU_PRICING[gpu_pricing_key]

    # Self-hosted: warm 24/7 fixed cost, plus ops
    monthly_fixed = 24 * 30 * gpus_needed * rate
    ops_cost = (ENGINEER_FULLY_LOADED * OPS_ATTRIBUTION_PCT) / 12 if profile.get("include_ops_attribution", True) else 0
    self_hosted_floor = monthly_fixed + ops_cost  # cost even at zero tokens (because warm)

    # When tokens exceed warm capacity, additional cost is more GPU hours
    # But up to warm capacity, total cost is just monthly_fixed + ops_cost
    warm_capacity_tokens_per_month = effective_tokens_per_sec * 24 * 30 * 3600

    # API cost per million tokens (weighted by I/O ratio)
    monthly_in = profile.get("monthly_input_tokens_m", 1)
    monthly_out = profile.get("monthly_output_tokens_m", 1)
    total_m = monthly_in + monthly_out
    in_ratio = monthly_in / total_m if total_m else 0.8
    out_ratio = monthly_out / total_m if total_m else 0.2

    api_per_m = API_PRICING[api_tier]["input"] * in_ratio + API_PRICING[api_tier]["output"] * out_ratio

    # Breakeven: api_per_m * tokens_m = self_hosted_floor
    if api_per_m > 0:
        breakeven_tokens_m = self_hosted_floor / api_per_m
    else:
        breakeven_tokens_m = None

    return {
        "breakeven_monthly_tokens_m": round(breakeven_tokens_m, 0) if breakeven_tokens_m else None,
        "self_hosted_floor_monthly": round(self_hosted_floor, 0),
        "warm_capacity_monthly_tokens_m": round(warm_capacity_tokens_per_month / 1_000_000, 0),
        "api_per_m_blended": round(api_per_m, 2),
    }


def analyze(profile: Dict[str, Any]) -> Dict[str, Any]:
    api_tier = profile.get("quality_tier_required", "frontier-economy")
    monthly_tokens_total_m = profile.get("monthly_input_tokens_m", 0) + profile.get("monthly_output_tokens_m", 0)

    # API costs at all 3 tiers
    api_costs = {tier: round(api_monthly_cost(profile, tier), 0) for tier in API_PRICING}

    # Self-hosted at chosen GPU type, 3 pricing tiers
    gpu_type = "A100" if profile.get("latency_p95_target_ms", 2000) > 1000 else "H100"
    self_hosted_low = self_hosted_monthly_cost(profile, gpu_type, "low")
    self_hosted_mid = self_hosted_monthly_cost(profile, gpu_type, "mid")
    self_hosted_high = self_hosted_monthly_cost(profile, gpu_type, "high")

    # Breakeven analysis at mid pricing
    breakeven = find_breakeven(profile, api_tier, gpu_type, "mid")

    # Recommendation
    api_chosen_cost = api_costs[api_tier]
    self_hosted_chosen_cost = self_hosted_mid["total"]

    if monthly_tokens_total_m < breakeven["breakeven_monthly_tokens_m"]:
        rec = "API"
        reasoning = (
            f"Current volume ({monthly_tokens_total_m:.0f}M tokens/mo) is BELOW breakeven "
            f"({breakeven['breakeven_monthly_tokens_m']:.0f}M tokens/mo). API tier '{api_tier}' is cheaper "
            f"({_fmt_money(api_chosen_cost)}/mo) than self-hosted "
            f"({_fmt_money(self_hosted_chosen_cost)}/mo at mid GPU rates)."
        )
        caveats = [
            "API costs scale linearly with token volume; revisit when volume doubles",
            "Build multi-vendor abstraction (LiteLLM / OpenRouter) for failover",
            "Pin model IDs; run regression evals on every model upgrade",
        ]
    elif self_hosted_high["total"] < api_chosen_cost:
        rec = "SELF_HOSTED"
        reasoning = (
            f"Current volume ({monthly_tokens_total_m:.0f}M tokens/mo) is well above breakeven. "
            f"Self-hosted at {_fmt_money(self_hosted_chosen_cost)}/mo (mid GPU rates) is cheaper than API "
            f"at {_fmt_money(api_chosen_cost)}/mo across all GPU pricing scenarios."
        )
        caveats = [
            "Quality lags frontier by ~6 months; budget refresh cycle",
            "24/7 on-call required; 30% engineer attribution may underestimate at scale",
            "GPU spot pricing volatile; negotiate reserved capacity at this scale",
            "Eval discipline non-negotiable for self-hosted; without it you cannot detect quality degradation",
        ]
    else:
        rec = "HYBRID"
        reasoning = (
            f"Current volume ({monthly_tokens_total_m:.0f}M tokens/mo) is above breakeven but self-hosted "
            f"cost ({_fmt_money(self_hosted_chosen_cost)}/mo) is close to API ({_fmt_money(api_chosen_cost)}/mo). "
            "Consider hybrid: API for tail / low-volume use cases, self-hosted for high-volume / latency-sensitive paths."
        )
        caveats = [
            "Migration to self-hosted typically takes 3-6 months of engineering time — model in TCO",
            "Hybrid increases operational complexity; ensure routing logic is testable",
            "At this margin, capability differences between API and 70B-class may matter more than cost",
        ]

    return {
        "recommendation": rec,
        "reasoning": reasoning,
        "caveats": caveats,
        "monthly_costs": {
            "api_frontier_premium": api_costs["frontier-premium"],
            "api_frontier_economy": api_costs["frontier-economy"],
            "api_open_hosted": api_costs["open-hosted"],
            "self_hosted_low_gpu_rate": self_hosted_low,
            "self_hosted_mid_gpu_rate": self_hosted_mid,
            "self_hosted_high_gpu_rate": self_hosted_high,
        },
        "breakeven_analysis": breakeven,
        "gpu_type_recommended": gpu_type,
        "current_monthly_tokens_m": monthly_tokens_total_m,
    }


def render_text(result: Dict[str, Any], profile: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("AI COST ECONOMICS — API vs SELF-HOSTED")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Workload: {profile.get('workload_name')}")
    lines.append(f"  Volume: {profile.get('monthly_input_tokens_m')}M input + {profile.get('monthly_output_tokens_m')}M output tokens/mo")
    lines.append(f"  Quality tier required: {profile.get('quality_tier_required')}")
    lines.append(f"  Model size for self-host: {profile.get('model_size_class_self_host')}")
    lines.append(f"  Latency p95 target: {profile.get('latency_p95_target_ms')}ms")
    lines.append(f"  Utilization assumed: {profile.get('utilization_assumed_pct')}%")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"RECOMMENDATION: {result['recommendation']}")
    lines.append("")
    for line in _wrap(result["reasoning"], 2):
        lines.append(line)
    lines.append("")
    lines.append("Caveats:")
    for c in result["caveats"]:
        lines.append(f"  • {c}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("MONTHLY COST COMPARISON:")
    lines.append("")
    mc = result["monthly_costs"]
    lines.append(f"  API frontier-premium:  {_fmt_money(mc['api_frontier_premium']):>15}    ({API_PRICING['frontier-premium']['label']})")
    lines.append(f"  API frontier-economy:  {_fmt_money(mc['api_frontier_economy']):>15}    ({API_PRICING['frontier-economy']['label']})")
    lines.append(f"  API open-hosted:       {_fmt_money(mc['api_open_hosted']):>15}    ({API_PRICING['open-hosted']['label']})")
    lines.append("")
    lines.append(f"  Self-hosted ({result['gpu_type_recommended']}), low GPU rates:   {_fmt_money(mc['self_hosted_low_gpu_rate']['total']):>15}    (GPU @ ${mc['self_hosted_low_gpu_rate']['gpu_rate_per_hr']}/hr × {mc['self_hosted_low_gpu_rate']['gpus_needed']} GPUs)")
    lines.append(f"  Self-hosted ({result['gpu_type_recommended']}), mid GPU rates:   {_fmt_money(mc['self_hosted_mid_gpu_rate']['total']):>15}    (GPU @ ${mc['self_hosted_mid_gpu_rate']['gpu_rate_per_hr']}/hr × {mc['self_hosted_mid_gpu_rate']['gpus_needed']} GPUs)")
    lines.append(f"  Self-hosted ({result['gpu_type_recommended']}), high GPU rates:  {_fmt_money(mc['self_hosted_high_gpu_rate']['total']):>15}    (GPU @ ${mc['self_hosted_high_gpu_rate']['gpu_rate_per_hr']}/hr × {mc['self_hosted_high_gpu_rate']['gpus_needed']} GPUs)")
    lines.append("")
    lines.append(f"  Self-hosted ops attribution: {_fmt_money(mc['self_hosted_mid_gpu_rate']['ops_cost'])}/mo (30% of one engineer)")
    lines.append("")
    lines.append("-" * 72)
    be = result["breakeven_analysis"]
    lines.append("BREAKEVEN ANALYSIS:")
    lines.append("")
    if be["breakeven_monthly_tokens_m"]:
        lines.append(f"  API '{profile.get('quality_tier_required')}' vs self-hosted at mid GPU rates:")
        lines.append(f"    Breakeven: ~{be['breakeven_monthly_tokens_m']:,.0f}M tokens/month")
        lines.append(f"    Current volume: {result['current_monthly_tokens_m']:,.0f}M tokens/month")
        lines.append(f"    Self-hosted floor (warm GPUs + ops, even at zero tokens): {_fmt_money(be['self_hosted_floor_monthly'])}/mo")
        lines.append(f"    Self-hosted warm capacity ceiling: ~{be['warm_capacity_monthly_tokens_m']:,.0f}M tokens/month")
        lines.append(f"    API blended cost: ${be['api_per_m_blended']}/M tokens")
    lines.append("")
    lines.append("-" * 72)
    lines.append("REMINDER: This analysis uses 2026 pricing. Pricing changes; re-run quarterly.")
    lines.append("Migration to self-hosted is 3-6 months of engineering work — model that in your TCO.")
    return "\n".join(lines)


def _fmt_money(amount: float) -> str:
    return f"${amount:,.0f}"


def _wrap(text: str, indent: int, width: int = 70) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="API vs self-hosted inference breakeven + sensitivity analysis.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to workload JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                profile = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        profile = SAMPLE
        source = "<embedded sample: 5M tokens/day customer support workload>"

    result = analyze(profile)

    if args.output == "json":
        print(json.dumps({"source": source, "profile": profile, **result}, indent=2))
    else:
        print(render_text(result, profile, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
