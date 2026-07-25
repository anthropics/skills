#!/usr/bin/env python3
"""model_buildvsbuy_calculator.py — Decide API vs fine-tune vs build for a use case.

Stdlib-only. Takes a use case profile and outputs:
  - Recommendation (API / FINE_TUNE / BUILD) with reasoning
  - 3-year TCO comparison across all 3 paths
  - Breakeven analysis (where API stops being cheapest)
  - Failure modes for the chosen path

Deterministic logic derived from the profile.

Input schema (JSON):
{
  "use_case": "Customer support response generation",
  "expected_qps": 5,                           # queries per second peak
  "monthly_volume_queries": 4000000,           # queries per month
  "avg_tokens_in": 800,
  "avg_tokens_out": 200,
  "latency_budget_ms": 2000,
  "accuracy_required": "frontier",             # frontier | high | acceptable
  "domain_specific": false,                    # need specific vocabulary / format / behavior
  "data_for_finetune_available": false,        # do we have labeled data for fine-tune?
  "team_ml_capacity_engineers": 1,
  "compliance_requires_self_host": false       # data residency / sovereignty constraint
}

Usage:
    python model_buildvsbuy_calculator.py                       # uses embedded customer-support sample
    python model_buildvsbuy_calculator.py path/to/use_case.json
    python model_buildvsbuy_calculator.py use_case.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Tuple


SAMPLE: Dict[str, Any] = {
    "use_case": "Customer support response generation (B2B SaaS)",
    "expected_qps": 5,
    "monthly_volume_queries": 4_000_000,
    "avg_tokens_in": 800,
    "avg_tokens_out": 200,
    "latency_budget_ms": 2000,
    "accuracy_required": "high",
    "domain_specific": True,
    "data_for_finetune_available": False,
    "team_ml_capacity_engineers": 1,
    "compliance_requires_self_host": False,
}


# 2026 API pricing per million tokens, $USD (input / output). These are illustrative;
# real pricing changes; rerun this calculator quarterly.
API_PRICING = {
    "frontier-premium": {"input": 3.00, "output": 15.00, "label": "Claude Sonnet 4.6 / GPT-4o-tier"},
    "frontier-economy": {"input": 1.25, "output": 5.00, "label": "Gemini 2.5 Flash / Claude Haiku 4.5-tier"},
    "open-router-hosted": {"input": 0.50, "output": 1.50, "label": "Llama 3.1 70B / Qwen 2.5 72B via hosted endpoint"},
}

# Fine-tune cost (one-time + ongoing)
FINETUNE_ONE_TIME = 25_000          # data prep + initial training + eval harness
FINETUNE_ANNUAL_RETRAIN = 15_000    # quarterly retraining + ops
FINETUNE_INFERENCE_PER_M = 0.40     # cost per M tokens at moderate scale on hosted endpoint

# Self-hosted inference cost (per million tokens, including GPU + ops at 70% utilization)
SELF_HOSTED_PER_M = {
    "7b-13b": 0.15,
    "70b-class": 1.50,
    "frontier-class": 12.00,   # very expensive without massive scale; included for completeness
}

# Build-from-scratch cost (one-time + ongoing) — illustrative; usually NOT recommended
BUILD_FROM_SCRATCH_ONE_TIME = 8_000_000
BUILD_FROM_SCRATCH_ANNUAL = 3_000_000


def compute_api_cost_3yr(profile: Dict[str, Any], tier: str) -> float:
    """3-year API cost given workload."""
    monthly_queries = profile.get("monthly_volume_queries", 0)
    tokens_in = profile.get("avg_tokens_in", 0)
    tokens_out = profile.get("avg_tokens_out", 0)

    monthly_input_tokens_m = (monthly_queries * tokens_in) / 1_000_000
    monthly_output_tokens_m = (monthly_queries * tokens_out) / 1_000_000

    pricing = API_PRICING.get(tier, API_PRICING["frontier-premium"])
    monthly_cost = (
        monthly_input_tokens_m * pricing["input"]
        + monthly_output_tokens_m * pricing["output"]
    )
    return monthly_cost * 36  # 3 years


def compute_finetune_cost_3yr(profile: Dict[str, Any]) -> float:
    monthly_queries = profile.get("monthly_volume_queries", 0)
    tokens_total = profile.get("avg_tokens_in", 0) + profile.get("avg_tokens_out", 0)
    monthly_tokens_m = (monthly_queries * tokens_total) / 1_000_000

    monthly_inference = monthly_tokens_m * FINETUNE_INFERENCE_PER_M
    annual_inference = monthly_inference * 12
    return FINETUNE_ONE_TIME + (annual_inference + FINETUNE_ANNUAL_RETRAIN) * 3


def compute_self_hosted_cost_3yr(profile: Dict[str, Any], model_class: str) -> float:
    """3-year self-hosted cost including GPU + ops."""
    monthly_queries = profile.get("monthly_volume_queries", 0)
    tokens_total = profile.get("avg_tokens_in", 0) + profile.get("avg_tokens_out", 0)
    monthly_tokens_m = (monthly_queries * tokens_total) / 1_000_000

    per_m = SELF_HOSTED_PER_M.get(model_class, SELF_HOSTED_PER_M["70b-class"])
    monthly_inference = monthly_tokens_m * per_m

    # Add fixed ops cost: 1 engineer * 30% load * fully-loaded $250K/yr = $75K/yr ops attribution
    annual_ops = 75_000
    return (monthly_inference * 36) + (annual_ops * 3)


def compute_build_cost_3yr() -> float:
    return BUILD_FROM_SCRATCH_ONE_TIME + (BUILD_FROM_SCRATCH_ANNUAL * 3)


def pick_recommendation(profile: Dict[str, Any], costs: Dict[str, float]) -> Tuple[str, str, List[str]]:
    """Pick API / FINE_TUNE / BUILD with reasoning and failure modes."""
    accuracy = profile.get("accuracy_required", "high")
    domain_specific = profile.get("domain_specific", False)
    finetune_data = profile.get("data_for_finetune_available", False)
    ml_capacity = profile.get("team_ml_capacity_engineers", 0)
    self_host_required = profile.get("compliance_requires_self_host", False)
    latency_ms = profile.get("latency_budget_ms", 2000)
    monthly_q = profile.get("monthly_volume_queries", 0)

    # Special case: compliance forces self-host
    if self_host_required:
        return (
            "FINE_TUNE",
            (
                "Compliance / data residency forces self-host. Fine-tune a 70B-class open model "
                f"({_fmt_money(costs['finetune_3yr'])}/3yr) rather than build from scratch "
                f"({_fmt_money(costs['build_3yr'])}/3yr) — the gap is two orders of magnitude with "
                "comparable quality for most use cases."
            ),
            [
                "Quality lags frontier by ~6 months; budget for refresh every 12-18mo",
                "Self-hosting requires 24/7 on-call; budget 30%+ of an engineer FTE",
                "Eval discipline becomes non-negotiable; without an eval set you cannot tell when retraining is needed",
            ],
        )

    # Build from scratch — almost never
    if accuracy == "frontier" and monthly_q > 1_000_000_000 and ml_capacity >= 20:
        return (
            "BUILD",
            (
                "Edge case where frontier accuracy + extreme volume + large ML team justify pre-training. "
                "Cost still extreme. Most companies here are foundation-model startups, not application companies."
            ),
            [
                "By the time you ship, frontier models have caught up — sunk cost risk",
                "Requires sustained $50M+ investment over 18+ months",
                "Unless model IS your product, do not build",
            ],
        )

    # Fine-tune cases
    if domain_specific and finetune_data and ml_capacity >= 2:
        return (
            "FINE_TUNE",
            (
                "Domain-specific behavior + labeled data + ML engineering capacity available. "
                f"Fine-tune cost ({_fmt_money(costs['finetune_3yr'])}) competes with API at this volume."
            ),
            [
                "Fine-tuned model lags frontier by ~6 months; quality drift is inevitable",
                "Retraining cadence (quarterly typical) is a recurring engineering cost",
                "Without eval set, fine-tune drift is invisible until customer complains",
            ],
        )

    # Latency-driven fine-tune (sub-500ms with 70B-class)
    if latency_ms < 500 and monthly_q > 1_000_000:
        return (
            "FINE_TUNE",
            (
                f"Latency budget {latency_ms}ms below frontier-API median (~600-1500ms). "
                "Fine-tuned 70B-class on dedicated infra is the path to sub-500ms at scale."
            ),
            [
                "Sub-500ms requires GPU co-location and warm pools (idle time penalty)",
                "Quality must be re-verified at every model swap",
                "Streaming responses can buy headroom on latency budget; consider before committing to fine-tune",
            ],
        )

    # Default to API for everything else
    economy_acceptable = accuracy in ("acceptable", "high")
    if economy_acceptable and costs["api_economy_3yr"] < costs["finetune_3yr"]:
        return (
            "API",
            (
                f"Frontier-economy API tier ({API_PRICING['frontier-economy']['label']}) at "
                f"{_fmt_money(costs['api_economy_3yr'])}/3yr beats fine-tune ({_fmt_money(costs['finetune_3yr'])}/3yr). "
                "Iterate on prompt engineering and eval discipline before committing to fine-tune."
            ),
            [
                "Vendor lock-in: build abstraction layer (LiteLLM, OpenRouter) for multi-vendor failover",
                "Capability drift between model versions: pin model IDs and run regression evals on upgrades",
                "Rate limits at QPS spikes: confirm Tier-4+ pricing with provider",
            ],
        )
    return (
        "API",
        (
            f"Frontier-premium API at {_fmt_money(costs['api_premium_3yr'])}/3yr is the right starting point. "
            "Revisit fine-tune at ≥10M queries/month OR domain-specific behavior the API can't be prompted into."
        ),
        [
            "Vendor lock-in: build abstraction layer for multi-vendor failover",
            "Capability drift between model versions; pin model IDs",
            "Rate limits at QPS spikes; confirm pricing tier with provider",
        ],
    )


def analyze(profile: Dict[str, Any]) -> Dict[str, Any]:
    costs = {
        "api_premium_3yr": compute_api_cost_3yr(profile, "frontier-premium"),
        "api_economy_3yr": compute_api_cost_3yr(profile, "frontier-economy"),
        "api_open_hosted_3yr": compute_api_cost_3yr(profile, "open-router-hosted"),
        "finetune_3yr": compute_finetune_cost_3yr(profile),
        "self_hosted_70b_3yr": compute_self_hosted_cost_3yr(profile, "70b-class"),
        "build_3yr": compute_build_cost_3yr(),
    }

    recommendation, reasoning, failure_modes = pick_recommendation(profile, costs)

    # Compute breakeven volume where API and fine-tune cross
    monthly_q = profile.get("monthly_volume_queries", 1)
    tokens_per_q = profile.get("avg_tokens_in", 0) + profile.get("avg_tokens_out", 0)
    annual_q = monthly_q * 12

    # Find breakeven where API economy total == fine-tune total over 3 years
    if tokens_per_q and annual_q:
        api_economy_per_query = costs["api_economy_3yr"] / (annual_q * 3) if annual_q else 0
        # finetune_cost = ONE_TIME + (queries * tokens * inference_per_m / 1M + ANNUAL_RETRAIN) * 3
        # Solve for queries where api_cost == finetune_cost
        # api_economy_per_query * Q = FINETUNE_ONE_TIME + (Q * tokens_per_q * FINETUNE_INFERENCE_PER_M / 1M + RETRAIN) * 3
        # api_economy_per_query * Q - 3 * Q * tokens_per_q * FINETUNE_INFERENCE_PER_M / 1M = FINETUNE_ONE_TIME + 3 * RETRAIN
        # Q * (api_economy_per_query - 3 * tokens_per_q * FINETUNE_INFERENCE_PER_M / 1M) = ONE_TIME + 3 * RETRAIN
        coefficient = (
            api_economy_per_query
            - 3 * tokens_per_q * FINETUNE_INFERENCE_PER_M / 1_000_000
        )
        rhs = FINETUNE_ONE_TIME + 3 * FINETUNE_ANNUAL_RETRAIN
        breakeven_3yr_queries = int(rhs / coefficient) if coefficient > 0 else None
        breakeven_monthly_queries = int(breakeven_3yr_queries / 36) if breakeven_3yr_queries else None
    else:
        breakeven_monthly_queries = None

    return {
        "recommendation": recommendation,
        "reasoning": reasoning,
        "failure_modes": failure_modes,
        "costs_3yr_usd": {k: round(v, 0) for k, v in costs.items()},
        "breakeven_monthly_queries_api_vs_finetune": breakeven_monthly_queries,
        "current_monthly_volume": profile.get("monthly_volume_queries", 0),
    }


def render_text(result: Dict[str, Any], profile: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("MODEL BUILD-VS-BUY ANALYSIS")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Use case: {profile.get('use_case')}")
    lines.append(f"  Volume: {profile.get('monthly_volume_queries'):,} queries/mo @ {profile.get('expected_qps')} QPS peak")
    lines.append(f"  Tokens: {profile.get('avg_tokens_in')} in / {profile.get('avg_tokens_out')} out per query")
    lines.append(f"  Latency budget: {profile.get('latency_budget_ms')}ms | Accuracy: {profile.get('accuracy_required')}")
    lines.append(f"  Domain-specific: {profile.get('domain_specific')} | Fine-tune data available: {profile.get('data_for_finetune_available')}")
    lines.append(f"  ML capacity: {profile.get('team_ml_capacity_engineers')} engineers | Compliance forces self-host: {profile.get('compliance_requires_self_host')}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"RECOMMENDATION: {result['recommendation']}")
    lines.append("")
    for line in _wrap(result["reasoning"], 2):
        lines.append(line)
    lines.append("")
    lines.append("Failure modes to plan for:")
    for fm in result["failure_modes"]:
        lines.append(f"  • {fm}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("3-YEAR TCO COMPARISON ($ USD):")
    lines.append("")
    costs = result["costs_3yr_usd"]
    lines.append(f"  API (frontier-premium, {API_PRICING['frontier-premium']['label']}):  {_fmt_money(costs['api_premium_3yr']):>15}")
    lines.append(f"  API (frontier-economy, {API_PRICING['frontier-economy']['label']}):   {_fmt_money(costs['api_economy_3yr']):>15}")
    lines.append(f"  API (open-router-hosted, {API_PRICING['open-router-hosted']['label']}): {_fmt_money(costs['api_open_hosted_3yr']):>15}")
    lines.append(f"  Fine-tune (70B-class, hosted inference):                                  {_fmt_money(costs['finetune_3yr']):>15}")
    lines.append(f"  Self-hosted (70B-class on rented H100/A100):                              {_fmt_money(costs['self_hosted_70b_3yr']):>15}")
    lines.append(f"  Build from scratch (pre-train + ops):                                     {_fmt_money(costs['build_3yr']):>15}")
    lines.append("")
    if result["breakeven_monthly_queries_api_vs_finetune"]:
        lines.append(f"Breakeven: API (economy) vs fine-tune crosses at ~{result['breakeven_monthly_queries_api_vs_finetune']:,} queries/month")
        if result["current_monthly_volume"] < result["breakeven_monthly_queries_api_vs_finetune"]:
            lines.append(f"  Current volume ({result['current_monthly_volume']:,}/mo) is BELOW breakeven → API still cheaper.")
        else:
            lines.append(f"  Current volume ({result['current_monthly_volume']:,}/mo) is ABOVE breakeven → fine-tune economics favorable.")
    lines.append("")
    lines.append("-" * 72)
    lines.append("REMINDER: TCO does not capture quality cost. Fine-tune quality lags frontier by ~6 months;")
    lines.append("self-hosted requires eval discipline you may not have. Re-run quarterly with updated pricing.")
    return "\n".join(lines)


def _fmt_money(amount: float) -> str:
    return f"${amount:,.0f}"


def _wrap(text: str, indent: int, width: int = 70) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Decide API vs fine-tune vs build with 3-year TCO comparison.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to use_case JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: B2B SaaS customer-support generation, 4M queries/mo>"

    result = analyze(profile)

    if args.output == "json":
        print(json.dumps({"source": source, "profile": profile, **result}, indent=2))
    else:
        print(render_text(result, profile, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
