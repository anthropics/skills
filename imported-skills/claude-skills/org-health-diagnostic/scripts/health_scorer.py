#!/usr/bin/env python3
"""
Org Health Diagnostic — Multi-Dimension Health Scorer
Scores 8 organizational dimensions on 1-10 scale with traffic lights.
Stdlib only. Run with: python health_scorer.py
"""

import json
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum


class Stage(Enum):
    SEED = "seed"
    SERIES_A = "series_a"
    SERIES_B = "series_b"
    SERIES_C = "series_c"


class Trend(Enum):
    IMPROVING = "improving"
    STABLE = "stable"
    DECLINING = "declining"
    UNKNOWN = "unknown"


class TrafficLight(Enum):
    GREEN = "green"
    YELLOW = "yellow"
    RED = "red"


# Stage weights: how much each dimension contributes to overall score
STAGE_WEIGHTS = {
    Stage.SEED: {
        "financial": 0.30, "revenue": 0.20, "people": 0.20,
        "product": 0.15, "engineering": 0.10, "operations": 0.05,
        "market": 0.00, "security": 0.00
    },
    Stage.SERIES_A: {
        "financial": 0.25, "revenue": 0.25, "people": 0.15,
        "product": 0.15, "engineering": 0.10, "operations": 0.05,
        "market": 0.05, "security": 0.00
    },
    Stage.SERIES_B: {
        "financial": 0.20, "revenue": 0.25, "people": 0.15,
        "product": 0.15, "engineering": 0.10, "operations": 0.08,
        "market": 0.05, "security": 0.02
    },
    Stage.SERIES_C: {
        "financial": 0.20, "revenue": 0.25, "people": 0.15,
        "product": 0.15, "engineering": 0.10, "operations": 0.08,
        "market": 0.05, "security": 0.02
    },
}


@dataclass
class Metric:
    name: str
    value: Optional[float]
    unit: str
    green_threshold: float    # value at or above this = green
    red_threshold: float      # value at or below this = red
    higher_is_better: bool = True

    def score(self) -> Optional[float]:
        """Score 1-10. Returns None if no value."""
        if self.value is None:
            return None
        v = self.value
        g = self.green_threshold
        r = self.red_threshold

        if self.higher_is_better:
            if v >= g:
                # Scale 7-10 based on how far above green
                excess = min((v - g) / max(g * 0.3, 0.01), 1.0)
                return 7.0 + (3.0 * excess)
            elif v <= r:
                # Scale 1-3 based on how far below red
                deficit = min((r - v) / max(r * 0.5, 0.01), 1.0)
                return max(1.0, 3.0 - (2.0 * deficit))
            else:
                # Between red and green → 4-6
                if g == r:
                    return 5.0
                position = (v - r) / (g - r)
                return 4.0 + (2.0 * position)
        else:
            # Lower is better — invert
            if v <= g:
                excess = min((g - v) / max(g * 0.3, 0.01), 1.0)
                return 7.0 + (3.0 * excess)
            elif v >= r:
                deficit = min((v - r) / max(r * 0.5, 0.01), 1.0)
                return max(1.0, 3.0 - (2.0 * deficit))
            else:
                if g == r:
                    return 5.0
                position = (r - v) / (r - g)
                return 4.0 + (2.0 * position)

    def traffic_light(self) -> Optional[TrafficLight]:
        s = self.score()
        if s is None:
            return None
        if s >= 7:
            return TrafficLight.GREEN
        elif s >= 4:
            return TrafficLight.YELLOW
        return TrafficLight.RED


@dataclass
class Dimension:
    key: str
    name: str
    owner: str
    emoji: str
    metrics: List[Metric]
    trend: Trend = Trend.UNKNOWN
    notes: str = ""

    def score(self) -> Optional[float]:
        """Average of available metric scores."""
        scores = [m.score() for m in self.metrics if m.score() is not None]
        if not scores:
            return None
        return round(sum(scores) / len(scores), 1)

    def traffic_light(self) -> TrafficLight:
        s = self.score()
        if s is None:
            return TrafficLight.YELLOW  # Unknown = watch
        if s >= 7:
            return TrafficLight.GREEN
        elif s >= 4:
            return TrafficLight.YELLOW
        return TrafficLight.RED

    def coverage(self) -> float:
        """% of metrics with data."""
        filled = sum(1 for m in self.metrics if m.value is not None)
        return filled / len(self.metrics) if self.metrics else 0.0

    def missing_metrics(self) -> List[str]:
        return [m.name for m in self.metrics if m.value is None]


def build_financial_dimension(stage: Stage, **kwargs) -> Dimension:
    # Thresholds vary by stage
    runway_green = {Stage.SEED: 18, Stage.SERIES_A: 12, Stage.SERIES_B: 12, Stage.SERIES_C: 18}
    runway_red = {Stage.SEED: 9, Stage.SERIES_A: 6, Stage.SERIES_B: 6, Stage.SERIES_C: 9}
    burn_green = {Stage.SEED: 3.0, Stage.SERIES_A: 2.0, Stage.SERIES_B: 1.5, Stage.SERIES_C: 1.0}
    burn_red = {Stage.SEED: 5.0, Stage.SERIES_A: 3.0, Stage.SERIES_B: 2.5, Stage.SERIES_C: 1.5}

    return Dimension(
        key="financial",
        name="Financial Health",
        owner="CFO",
        emoji="💰",
        metrics=[
            Metric("Runway (months)", kwargs.get("runway"),
                   "months", runway_green[stage], runway_red[stage]),
            Metric("Burn multiple", kwargs.get("burn_multiple"),
                   "x", burn_green[stage], burn_red[stage], higher_is_better=False),
            Metric("Gross margin (%)", kwargs.get("gross_margin"),
                   "%", 70, 55),
            Metric("MoM growth (%)", kwargs.get("mom_growth"),
                   "%", 10, 4),
            Metric("Revenue concentration (%)", kwargs.get("revenue_concentration"),
                   "%", 15, 30, higher_is_better=False),
        ],
        trend=kwargs.get("financial_trend", Trend.UNKNOWN),
    )


def build_revenue_dimension(stage: Stage, **kwargs) -> Dimension:
    nrr_green = {Stage.SEED: 100, Stage.SERIES_A: 110, Stage.SERIES_B: 115, Stage.SERIES_C: 120}
    nrr_red = {Stage.SEED: 90, Stage.SERIES_A: 100, Stage.SERIES_B: 105, Stage.SERIES_C: 110}

    return Dimension(
        key="revenue",
        name="Revenue Health",
        owner="CRO",
        emoji="📈",
        metrics=[
            Metric("NRR (%)", kwargs.get("nrr"),
                   "%", nrr_green[stage], nrr_red[stage]),
            Metric("Logo churn (%/yr)", kwargs.get("logo_churn"),
                   "%/yr", 5, 15, higher_is_better=False),
            Metric("Pipeline coverage", kwargs.get("pipeline_coverage"),
                   "x", 3.0, 1.5),
            Metric("CAC payback (months)", kwargs.get("cac_payback"),
                   "months", 12, 24, higher_is_better=False),
            Metric("Win rate (%)", kwargs.get("win_rate"),
                   "%", 25, 15),
        ],
        trend=kwargs.get("revenue_trend", Trend.UNKNOWN),
    )


def build_product_dimension(**kwargs) -> Dimension:
    return Dimension(
        key="product",
        name="Product Health",
        owner="CPO",
        emoji="🚀",
        metrics=[
            Metric("NPS", kwargs.get("nps"), "score", 40, 20),
            Metric("DAU/MAU (%)", kwargs.get("dau_mau"), "%", 35, 15),
            Metric("Core feature adoption (%)", kwargs.get("feature_adoption"), "%", 60, 30),
            Metric("CSAT", kwargs.get("csat"), "/5", 4.2, 3.5),
            Metric("Time-to-value (days)", kwargs.get("ttv_days"), "days", 3, 14, higher_is_better=False),
        ],
        trend=kwargs.get("product_trend", Trend.UNKNOWN),
    )


def build_engineering_dimension(**kwargs) -> Dimension:
    # Deploy frequency encoded: 5=multiple/day, 4=daily, 3=weekly, 2=monthly, 1=<monthly
    return Dimension(
        key="engineering",
        name="Engineering Health",
        owner="CTO",
        emoji="⚙️",
        metrics=[
            Metric("Deploy frequency (1-5)", kwargs.get("deploy_freq"), "scale", 4, 2),
            Metric("Change failure rate (%)", kwargs.get("change_failure_rate"), "%", 5, 15, higher_is_better=False),
            Metric("MTTR (hours)", kwargs.get("mttr_hours"), "hours", 1, 4, higher_is_better=False),
            Metric("Tech debt ratio (%)", kwargs.get("tech_debt_pct"), "%", 15, 35, higher_is_better=False),
            Metric("P0/P1 incidents/month", kwargs.get("incidents_monthly"), "count", 1, 5, higher_is_better=False),
        ],
        trend=kwargs.get("engineering_trend", Trend.UNKNOWN),
    )


def build_people_dimension(stage: Stage, **kwargs) -> Dimension:
    attrition_green = {Stage.SEED: 15, Stage.SERIES_A: 12, Stage.SERIES_B: 10, Stage.SERIES_C: 8}
    attrition_red = {Stage.SEED: 25, Stage.SERIES_A: 18, Stage.SERIES_B: 15, Stage.SERIES_C: 12}

    return Dimension(
        key="people",
        name="People Health",
        owner="CHRO",
        emoji="👥",
        metrics=[
            Metric("Regrettable attrition (%/yr)", kwargs.get("attrition"),
                   "%/yr", attrition_green[stage], attrition_red[stage], higher_is_better=False),
            Metric("eNPS", kwargs.get("enps"), "score", 30, 0),
            Metric("Time-to-fill (days)", kwargs.get("ttf_days"), "days", 45, 90, higher_is_better=False),
            Metric("Internal promotion rate (%)", kwargs.get("internal_promo_rate"), "%", 25, 10),
        ],
        trend=kwargs.get("people_trend", Trend.UNKNOWN),
    )


def build_operations_dimension(**kwargs) -> Dimension:
    return Dimension(
        key="operations",
        name="Operational Health",
        owner="COO",
        emoji="🔄",
        metrics=[
            Metric("OKR completion rate (%)", kwargs.get("okr_completion"), "%", 70, 50),
            Metric("Decision cycle time (hours)", kwargs.get("decision_hours"), "hours", 48, 168, higher_is_better=False),
            Metric("Process maturity (1-5)", kwargs.get("process_maturity"), "level", 3, 1.5),
            Metric("Cross-functional delivery (%)", kwargs.get("xfn_delivery_rate"), "%", 70, 50),
        ],
        trend=kwargs.get("ops_trend", Trend.UNKNOWN),
    )


def build_security_dimension(**kwargs) -> Dimension:
    return Dimension(
        key="security",
        name="Security Health",
        owner="CISO",
        emoji="🔒",
        metrics=[
            Metric("Security incidents (90 days)", kwargs.get("incidents_90d"), "count", 0, 1, higher_is_better=False),
            Metric("MFA coverage (%)", kwargs.get("mfa_coverage"), "%", 95, 80),
            Metric("Security training completion (%)", kwargs.get("training_completion"), "%", 95, 80),
            Metric("Critical CVE patch rate (%)", kwargs.get("cve_patch_rate"), "%", 100, 85),
            Metric("Pen test recency (months)", kwargs.get("pentest_months"), "months", 12, 24, higher_is_better=False),
        ],
        trend=kwargs.get("security_trend", Trend.UNKNOWN),
    )


def build_market_dimension(**kwargs) -> Dimension:
    return Dimension(
        key="market",
        name="Market Health",
        owner="CMO",
        emoji="📣",
        metrics=[
            Metric("Organic pipeline % ", kwargs.get("organic_pipeline_pct"), "%", 40, 20),
            Metric("Competitive win rate (%)", kwargs.get("competitive_win_rate"), "%", 45, 30),
            Metric("CAC trend (1=worsening, 5=improving)", kwargs.get("cac_trend_score"), "scale", 4, 2),
        ],
        trend=kwargs.get("market_trend", Trend.UNKNOWN),
    )


def calculate_overall(dimensions: List[Dimension], stage: Stage) -> Optional[float]:
    weights = STAGE_WEIGHTS[stage]
    total_weight = 0.0
    weighted_sum = 0.0
    for dim in dimensions:
        score = dim.score()
        w = weights.get(dim.key, 0.0)
        if score is not None and w > 0:
            weighted_sum += score * w
            total_weight += w
    if total_weight == 0:
        return None
    return round(weighted_sum / total_weight, 1)


def trend_arrow(trend: Trend) -> str:
    return {
        Trend.IMPROVING: "↑",
        Trend.STABLE: "→",
        Trend.DECLINING: "↓",
        Trend.UNKNOWN: "?",
    }[trend]


def traffic_light_icon(tl: TrafficLight) -> str:
    return {"green": "🟢", "yellow": "🟡", "red": "🔴"}[tl.value]


def print_dashboard(dimensions: List[Dimension], overall: Optional[float],
                    stage: Stage, company: str = "Company") -> None:
    """Print the full health dashboard."""
    print("\n" + "=" * 65)
    print(f"ORG HEALTH DIAGNOSTIC — {company.upper()}")
    print(f"Stage: {stage.value.replace('_', ' ').title()}")
    if overall is not None:
        overall_tl = TrafficLight.GREEN if overall >= 7 else (TrafficLight.YELLOW if overall >= 4 else TrafficLight.RED)
        print(f"Overall: {traffic_light_icon(overall_tl)} {overall}/10")
    print("=" * 65)

    print("\nDIMENSION SCORES")
    print("─" * 65)

    priority_reds = []
    priority_yellows = []

    for dim in dimensions:
        score = dim.score()
        tl = dim.traffic_light()
        icon = traffic_light_icon(tl)
        trend = trend_arrow(dim.trend)
        coverage = int(dim.coverage() * 100)

        score_str = f"{score:.1f}" if score is not None else "N/A"
        cov_str = f"({coverage}% data)" if coverage < 100 else ""
        print(f"{dim.emoji} {dim.name:<22} {icon} {score_str:<5} {trend}  {dim.owner}  {cov_str}")

        if tl == TrafficLight.RED and score is not None:
            priority_reds.append(dim)
        elif tl == TrafficLight.YELLOW and score is not None:
            priority_yellows.append(dim)

    # Top priorities
    if priority_reds or priority_yellows:
        print(f"\n{'─' * 65}")
        print("PRIORITIES")
        print("─" * 65)

        idx = 1
        for dim in priority_reds[:3]:
            print(f"\n🔴 [{idx}] {dim.name} — Score: {dim.score():.1f}/10")
            # Show worst metric
            worst = min(
                [m for m in dim.metrics if m.score() is not None],
                key=lambda m: m.score(),
                default=None
            )
            if worst:
                print(f"   Worst metric: {worst.name} = {worst.value}{worst.unit}")
            missing = dim.missing_metrics()
            if missing:
                print(f"   Missing data: {', '.join(missing)}")
            idx += 1

        for dim in priority_yellows[:2]:
            print(f"\n🟡 [{idx}] {dim.name} — Score: {dim.score():.1f}/10 — {trend_arrow(dim.trend)}")
            idx += 1

    # Data gaps
    all_missing = [(dim.name, dim.missing_metrics()) for dim in dimensions if dim.missing_metrics()]
    if all_missing:
        print(f"\n{'─' * 65}")
        print("DATA GAPS (fill to improve diagnostic accuracy)")
        for dim_name, metrics in all_missing:
            print(f"  {dim_name}: {', '.join(metrics)}")

    # Cascade warnings
    print(f"\n{'─' * 65}")
    print("CASCADE RISK")
    red_keys = {d.key for d in dimensions if d.traffic_light() == TrafficLight.RED}
    if "people" in red_keys:
        print("  ⚠️  People RED → Engineering velocity drop expected in 60-90 days")
    if "engineering" in red_keys:
        print("  ⚠️  Engineering RED → Product quality at risk; roadmap will slip")
    if "product" in red_keys:
        print("  ⚠️  Product RED → Revenue retention at risk within 2 quarters")
    if "revenue" in red_keys:
        print("  ⚠️  Revenue RED → Financial pressure mounting; watch runway")
    if "financial" in red_keys:
        print("  🚨 Financial RED → All dimensions at risk; immediate board action needed")
    if not red_keys:
        print("  ✅ No active cascade risks detected")

    print(f"\n{'=' * 65}\n")


def to_json(dimensions: List[Dimension], overall: Optional[float], stage: Stage) -> Dict:
    result = {
        "stage": stage.value,
        "overall_score": overall,
        "overall_traffic_light": (
            TrafficLight.GREEN if overall and overall >= 7
            else TrafficLight.YELLOW if overall and overall >= 4
            else TrafficLight.RED
        ).value if overall else "unknown",
        "dimensions": {}
    }
    for dim in dimensions:
        result["dimensions"][dim.key] = {
            "name": dim.name,
            "owner": dim.owner,
            "score": dim.score(),
            "traffic_light": dim.traffic_light().value,
            "trend": dim.trend.value,
            "coverage_pct": round(dim.coverage() * 100),
            "missing_metrics": dim.missing_metrics(),
            "metrics": [
                {
                    "name": m.name,
                    "value": m.value,
                    "unit": m.unit,
                    "score": m.score(),
                    "traffic_light": m.traffic_light().value if m.traffic_light() else None,
                }
                for m in dim.metrics
            ]
        }
    return result


def build_sample_data(stage: Stage) -> Dict:
    """Sample Series A company data."""
    return dict(
        # Financial
        runway=14, burn_multiple=1.8, gross_margin=68, mom_growth=8.5,
        revenue_concentration=28, financial_trend=Trend.STABLE,
        # Revenue
        nrr=104, logo_churn=8, pipeline_coverage=1.9, cac_payback=16,
        win_rate=22, revenue_trend=Trend.DECLINING,
        # Product
        nps=38, dau_mau=32, feature_adoption=52, csat=4.1,
        ttv_days=6, product_trend=Trend.STABLE,
        # Engineering
        deploy_freq=3, change_failure_rate=9, mttr_hours=2.8,
        tech_debt_pct=30, incidents_monthly=2, engineering_trend=Trend.STABLE,
        # People
        attrition=21, enps=12, ttf_days=58, internal_promo_rate=18,
        people_trend=Trend.DECLINING,
        # Operations
        okr_completion=62, decision_hours=72, process_maturity=2.5,
        xfn_delivery_rate=65, ops_trend=Trend.STABLE,
        # Security
        incidents_90d=0, mfa_coverage=88, training_completion=82,
        cve_patch_rate=95, pentest_months=14, security_trend=Trend.IMPROVING,
        # Market
        organic_pipeline_pct=35, competitive_win_rate=42,
        cac_trend_score=3, market_trend=Trend.STABLE,
    )


def interactive_mode(stage: Stage) -> Dict:
    """Guided metric entry."""
    print("\nEnter metrics (press Enter to skip):\n")
    data = {}

    def ask(prompt: str, key: str, default=None):
        val = input(f"  {prompt}: ").strip()
        if val:
            try:
                data[key] = float(val)
            except ValueError:
                pass

    print("💰 FINANCIAL")
    ask("Runway (months)", "runway")
    ask("Burn multiple (e.g. 1.8)", "burn_multiple")
    ask("Gross margin (%)", "gross_margin")
    ask("MoM growth (%)", "mom_growth")
    ask("Top customer % of ARR", "revenue_concentration")

    print("\n📈 REVENUE")
    ask("NRR (%)", "nrr")
    ask("Logo churn (%/yr)", "logo_churn")
    ask("Pipeline coverage (x)", "pipeline_coverage")
    ask("CAC payback (months)", "cac_payback")
    ask("Win rate (%)", "win_rate")

    print("\n🚀 PRODUCT")
    ask("NPS score", "nps")
    ask("DAU/MAU (%)", "dau_mau")
    ask("Core feature adoption (%)", "feature_adoption")

    print("\n⚙️  ENGINEERING")
    ask("Deploy frequency (1=rare, 5=multiple/day)", "deploy_freq")
    ask("Change failure rate (%)", "change_failure_rate")
    ask("MTTR (hours)", "mttr_hours")
    ask("Tech debt % of sprint", "tech_debt_pct")

    print("\n👥 PEOPLE")
    ask("Regrettable attrition (%/yr)", "attrition")
    ask("eNPS score", "enps")
    ask("Time-to-fill (days)", "ttf_days")

    print("\n🔄 OPERATIONS")
    ask("OKR completion rate (%)", "okr_completion")

    print("\n🔒 SECURITY")
    ask("MFA coverage (%)", "mfa_coverage")
    ask("Security training completion (%)", "training_completion")

    return data


def main():
    print("\n🏥 ORG HEALTH DIAGNOSTIC")
    print("Multi-dimension organizational health scorer\n")

    # Determine stage
    stage_map = {
        "seed": Stage.SEED, "a": Stage.SERIES_A, "series_a": Stage.SERIES_A,
        "b": Stage.SERIES_B, "series_b": Stage.SERIES_B,
        "c": Stage.SERIES_C, "series_c": Stage.SERIES_C,
    }
    stage_arg = next((a for a in sys.argv[1:] if a.lower() in stage_map), None)
    stage = stage_map.get(stage_arg.lower(), Stage.SERIES_A) if stage_arg else Stage.SERIES_A

    if "--interactive" in sys.argv or "-i" in sys.argv:
        company = input("Company name: ").strip() or "Company"
        stage_input = input("Stage (seed/a/b/c): ").strip().lower()
        stage = stage_map.get(stage_input, Stage.SERIES_A)
        data = interactive_mode(stage)
    else:
        print(f"Running sample Series A company data.")
        print("(Use --interactive or -i for custom data, --stage seed/a/b/c for stage)\n")
        company = "Sample Co"
        data = build_sample_data(stage)

    # Build dimensions
    dimensions = [
        build_financial_dimension(stage, **data),
        build_revenue_dimension(stage, **data),
        build_product_dimension(**data),
        build_engineering_dimension(**data),
        build_people_dimension(stage, **data),
        build_operations_dimension(**data),
        build_security_dimension(**data),
        build_market_dimension(**data),
    ]

    overall = calculate_overall(dimensions, stage)
    print_dashboard(dimensions, overall, stage, company)

    if "--json" in sys.argv:
        print(json.dumps(to_json(dimensions, overall, stage), indent=2))


if __name__ == "__main__":
    main()
