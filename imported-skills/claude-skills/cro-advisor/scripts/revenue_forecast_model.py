#!/usr/bin/env python3
"""
Revenue Forecast Model
======================
Pipeline-based revenue forecasting for B2B SaaS.

Models:
  - Weighted pipeline (stage probability × deal value)
  - Historical win rate adjustment (calibrate to actuals)
  - Scenario analysis (conservative / base / upside)
  - Monthly and quarterly projection with confidence ranges

Usage:
  python revenue_forecast_model.py
  python revenue_forecast_model.py --csv pipeline.csv
  python revenue_forecast_model.py --scenario conservative

Input format (CSV):
  deal_id, name, stage, arr_value, close_date, rep, segment

Stdlib only. No dependencies.
"""

import csv
import sys
import json
import argparse
import statistics
from datetime import date, datetime, timedelta
from collections import defaultdict
from io import StringIO


# ---------------------------------------------------------------------------
# Stage configuration
# ---------------------------------------------------------------------------

DEFAULT_STAGE_PROBABILITIES = {
    "discovery":     0.10,
    "qualification": 0.25,
    "demo":          0.40,
    "proposal":      0.55,
    "poc":           0.65,
    "negotiation":   0.80,
    "verbal_commit": 0.92,
    "closed_won":    1.00,
    "closed_lost":   0.00,
}

SCENARIO_MULTIPLIERS = {
    "conservative": 0.85,  # Win rate 15% below historical
    "base":         1.00,  # Historical win rate
    "upside":       1.15,  # Win rate 15% above historical
}


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

class Deal:
    def __init__(self, deal_id, name, stage, arr_value, close_date, rep="", segment=""):
        self.deal_id = deal_id
        self.name = name
        self.stage = stage.lower().replace(" ", "_").replace("/", "_")
        self.arr_value = float(arr_value)
        self.close_date = self._parse_date(close_date)
        self.rep = rep
        self.segment = segment

    @staticmethod
    def _parse_date(value):
        for fmt in ("%Y-%m-%d", "%m/%d/%Y", "%d/%m/%Y", "%Y/%m/%d"):
            try:
                return datetime.strptime(str(value), fmt).date()
            except ValueError:
                continue
        raise ValueError(f"Cannot parse date: {value!r}")

    @property
    def quarter(self):
        q = (self.close_date.month - 1) // 3 + 1
        return f"Q{q} {self.close_date.year}"

    @property
    def month_key(self):
        return self.close_date.strftime("%Y-%m")

    def weighted_value(self, stage_probs, scenario="base"):
        prob = stage_probs.get(self.stage, 0.0)
        multiplier = SCENARIO_MULTIPLIERS.get(scenario, 1.0)
        # Clamp probability to [0, 1]
        adjusted = min(1.0, max(0.0, prob * multiplier))
        return self.arr_value * adjusted

    def is_open(self):
        return self.stage not in ("closed_won", "closed_lost")

    def is_closed_won(self):
        return self.stage == "closed_won"


# ---------------------------------------------------------------------------
# Win rate calibration
# ---------------------------------------------------------------------------

def calculate_historical_win_rates(deals):
    """
    Calculate actual win rates per stage from closed deals.
    Returns a dict: stage → win_rate (float).
    Requires deals that were at each stage and are now closed won/lost.
    """
    # In a real implementation, you'd have historical stage-at-point-in-time data.
    # Here we approximate: among closed deals, what fraction were won?
    closed = [d for d in deals if not d.is_open()]
    if not closed:
        return {}

    won = [d for d in closed if d.is_closed_won()]
    overall_rate = len(won) / len(closed) if closed else 0.0

    # Stage-level calibration: adjust default probs by actual overall rate
    # (In production: use CRM historical stage-level conversion data)
    calibrated = {}
    for stage, default_prob in DEFAULT_STAGE_PROBABILITIES.items():
        if overall_rate > 0:
            calibrated[stage] = min(1.0, default_prob * (overall_rate / 0.25))
        else:
            calibrated[stage] = default_prob

    return calibrated


# ---------------------------------------------------------------------------
# Forecast engine
# ---------------------------------------------------------------------------

class ForecastEngine:
    def __init__(self, deals, stage_probs=None):
        self.deals = deals
        self.stage_probs = stage_probs or DEFAULT_STAGE_PROBABILITIES

    def open_deals(self):
        return [d for d in self.deals if d.is_open()]

    def closed_won_deals(self):
        return [d for d in self.deals if d.is_closed_won()]

    def pipeline_by_month(self, scenario="base"):
        """Returns dict: month_key → weighted ARR."""
        result = defaultdict(float)
        for deal in self.open_deals():
            result[deal.month_key] += deal.weighted_value(self.stage_probs, scenario)
        return dict(sorted(result.items()))

    def pipeline_by_quarter(self, scenario="base"):
        """Returns dict: quarter → weighted ARR."""
        result = defaultdict(float)
        for deal in self.open_deals():
            result[deal.quarter] += deal.weighted_value(self.stage_probs, scenario)
        return dict(sorted(result.items()))

    def coverage_ratio(self, quota, period_filter=None):
        """
        Pipeline coverage = total pipeline ÷ quota.
        period_filter: if set, only include deals with close_date in that period.
        """
        pipeline = sum(
            d.arr_value for d in self.open_deals()
            if period_filter is None or d.quarter == period_filter
        )
        return pipeline / quota if quota else 0.0

    def scenario_summary(self, periods=None):
        """
        Returns dict: period → {conservative, base, upside, open_pipeline}.
        periods: list of month_keys to include; if None, all months.
        """
        summaries = {}
        all_months = sorted(set(d.month_key for d in self.open_deals()))
        target_months = periods or all_months

        for month in target_months:
            deals_in_month = [d for d in self.open_deals() if d.month_key == month]
            if not deals_in_month:
                continue
            summaries[month] = {
                "deal_count":    len(deals_in_month),
                "open_pipeline": sum(d.arr_value for d in deals_in_month),
                "conservative":  sum(d.weighted_value(self.stage_probs, "conservative") for d in deals_in_month),
                "base":          sum(d.weighted_value(self.stage_probs, "base") for d in deals_in_month),
                "upside":        sum(d.weighted_value(self.stage_probs, "upside") for d in deals_in_month),
            }
        return summaries

    def rep_performance(self):
        """Returns dict: rep → {pipeline, weighted_base, deal_count, avg_deal_size}."""
        rep_data = defaultdict(lambda: {"pipeline": 0.0, "weighted_base": 0.0,
                                        "deal_count": 0, "deals": []})
        for deal in self.open_deals():
            rep_data[deal.rep]["pipeline"] += deal.arr_value
            rep_data[deal.rep]["weighted_base"] += deal.weighted_value(self.stage_probs, "base")
            rep_data[deal.rep]["deal_count"] += 1
            rep_data[deal.rep]["deals"].append(deal.arr_value)

        result = {}
        for rep, data in rep_data.items():
            deals = data["deals"]
            result[rep] = {
                "pipeline":      data["pipeline"],
                "weighted_base": data["weighted_base"],
                "deal_count":    data["deal_count"],
                "avg_deal_size": statistics.mean(deals) if deals else 0.0,
            }
        return result

    def segment_breakdown(self, scenario="base"):
        """Returns dict: segment → weighted ARR."""
        result = defaultdict(float)
        for deal in self.open_deals():
            result[deal.segment or "unspecified"] += deal.weighted_value(self.stage_probs, scenario)
        return dict(result)

    def stage_distribution(self):
        """Returns dict: stage → {count, total_arr, avg_arr}."""
        result = defaultdict(lambda: {"count": 0, "total_arr": 0.0})
        for deal in self.open_deals():
            result[deal.stage]["count"] += 1
            result[deal.stage]["total_arr"] += deal.arr_value
        out = {}
        for stage, data in result.items():
            out[stage] = {
                "count":     data["count"],
                "total_arr": data["total_arr"],
                "avg_arr":   data["total_arr"] / data["count"] if data["count"] else 0,
                "probability": self.stage_probs.get(stage, 0.0),
            }
        return out

    def confidence_interval(self, scenario="base", iterations=1000):
        """
        Monte Carlo simulation to generate confidence interval around base forecast.
        Each deal wins/loses based on its probability; runs iterations times.
        Returns (p10, p50, p90) of total expected ARR.
        """
        import random
        random.seed(42)

        totals = []
        for _ in range(iterations):
            total = 0.0
            for deal in self.open_deals():
                prob = min(1.0, self.stage_probs.get(deal.stage, 0.0) * SCENARIO_MULTIPLIERS[scenario])
                if random.random() < prob:
                    total += deal.arr_value
            totals.append(total)

        totals.sort()
        n = len(totals)
        return (
            totals[int(n * 0.10)],  # P10 (conservative)
            totals[int(n * 0.50)],  # P50 (median)
            totals[int(n * 0.90)],  # P90 (upside)
        )


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fmt_currency(value):
    if value >= 1_000_000:
        return f"${value / 1_000_000:.2f}M"
    if value >= 1_000:
        return f"${value / 1_000:.1f}K"
    return f"${value:.0f}"


def fmt_pct(value):
    return f"{value * 100:.1f}%"


def print_header(title):
    width = 70
    print()
    print("=" * width)
    print(f"  {title}")
    print("=" * width)


def print_section(title):
    print(f"\n--- {title} ---")


def print_report(engine, quota=None, current_quarter=None):
    open_deals = engine.open_deals()
    won_deals = engine.closed_won_deals()

    print_header("REVENUE FORECAST MODEL")
    print(f"  Generated: {date.today().isoformat()}")
    print(f"  Open deals: {len(open_deals)}")
    print(f"  Closed Won (in dataset): {len(won_deals)}")
    total_pipeline = sum(d.arr_value for d in open_deals)
    total_won = sum(d.arr_value for d in won_deals)
    print(f"  Total open pipeline: {fmt_currency(total_pipeline)}")
    print(f"  Total closed won:    {fmt_currency(total_won)}")

    # ── Coverage ratio
    if quota:
        print_section("PIPELINE COVERAGE")
        q = current_quarter or "this quarter"
        ratio = engine.coverage_ratio(quota, period_filter=current_quarter)
        status = "✅ Healthy" if ratio >= 3.0 else ("⚠️  Thin" if ratio >= 2.0 else "🔴 Critical")
        print(f"  Quota target:    {fmt_currency(quota)}")
        print(f"  Coverage ratio:  {ratio:.1f}x  {status}")
        print(f"  (Minimum healthy = 3x; < 2x = pipeline emergency)")

    # ── Stage distribution
    print_section("STAGE DISTRIBUTION")
    stage_dist = engine.stage_distribution()
    col_w = [28, 8, 14, 12, 10]
    header = f"  {'Stage':<{col_w[0]}} {'Deals':>{col_w[1]}} {'Pipeline':>{col_w[2]}} {'Avg Size':>{col_w[3]}} {'Win Prob':>{col_w[4]}}"
    print(header)
    print("  " + "-" * (sum(col_w) + 4))
    for stage, data in sorted(stage_dist.items(), key=lambda x: -x[1]["total_arr"]):
        print(f"  {stage:<{col_w[0]}} {data['count']:>{col_w[1]}} "
              f"{fmt_currency(data['total_arr']):>{col_w[2]}} "
              f"{fmt_currency(data['avg_arr']):>{col_w[3]}} "
              f"{fmt_pct(data['probability']):>{col_w[4]}}")

    # ── Scenario forecast by month
    print_section("MONTHLY FORECAST — ALL SCENARIOS")
    summaries = engine.scenario_summary()
    col_w2 = [10, 8, 14, 14, 14, 14]
    h2 = (f"  {'Month':<{col_w2[0]}} {'Deals':>{col_w2[1]}} "
          f"{'Pipeline':>{col_w2[2]}} {'Conservative':>{col_w2[3]}} "
          f"{'Base':>{col_w2[4]}} {'Upside':>{col_w2[5]}}")
    print(h2)
    print("  " + "-" * (sum(col_w2) + 5))
    for month, data in summaries.items():
        print(f"  {month:<{col_w2[0]}} {data['deal_count']:>{col_w2[1]}} "
              f"{fmt_currency(data['open_pipeline']):>{col_w2[2]}} "
              f"{fmt_currency(data['conservative']):>{col_w2[3]}} "
              f"{fmt_currency(data['base']):>{col_w2[4]}} "
              f"{fmt_currency(data['upside']):>{col_w2[5]}}")

    # ── Quarterly rollup
    print_section("QUARTERLY FORECAST ROLLUP")
    q_conservative = defaultdict(float)
    q_base = defaultdict(float)
    q_upside = defaultdict(float)
    q_pipeline = defaultdict(float)
    q_count = defaultdict(int)
    for deal in open_deals:
        q_conservative[deal.quarter] += deal.weighted_value(engine.stage_probs, "conservative")
        q_base[deal.quarter] += deal.weighted_value(engine.stage_probs, "base")
        q_upside[deal.quarter] += deal.weighted_value(engine.stage_probs, "upside")
        q_pipeline[deal.quarter] += deal.arr_value
        q_count[deal.quarter] += 1

    quarters = sorted(q_base.keys())
    col_w3 = [10, 8, 14, 14, 14, 14]
    h3 = (f"  {'Quarter':<{col_w3[0]}} {'Deals':>{col_w3[1]}} "
          f"{'Pipeline':>{col_w3[2]}} {'Conservative':>{col_w3[3]}} "
          f"{'Base':>{col_w3[4]}} {'Upside':>{col_w3[5]}}")
    print(h3)
    print("  " + "-" * (sum(col_w3) + 5))
    for q in quarters:
        print(f"  {q:<{col_w3[0]}} {q_count[q]:>{col_w3[1]}} "
              f"{fmt_currency(q_pipeline[q]):>{col_w3[2]}} "
              f"{fmt_currency(q_conservative[q]):>{col_w3[3]}} "
              f"{fmt_currency(q_base[q]):>{col_w3[4]}} "
              f"{fmt_currency(q_upside[q]):>{col_w3[5]}}")

    # ── Monte Carlo confidence interval
    print_section("CONFIDENCE INTERVAL (Monte Carlo, 1,000 simulations)")
    p10, p50, p90 = engine.confidence_interval("base")
    print(f"  P10 (conservative floor): {fmt_currency(p10)}")
    print(f"  P50 (median expected):    {fmt_currency(p50)}")
    print(f"  P90 (upside ceiling):     {fmt_currency(p90)}")
    print(f"  Range spread: {fmt_currency(p90 - p10)}")

    # ── Rep performance
    print_section("REP PIPELINE PERFORMANCE")
    rep_perf = engine.rep_performance()
    if rep_perf:
        col_w4 = [20, 8, 14, 14, 12]
        h4 = (f"  {'Rep':<{col_w4[0]}} {'Deals':>{col_w4[1]}} "
              f"{'Pipeline':>{col_w4[2]}} {'Weighted':>{col_w4[3]}} {'Avg Size':>{col_w4[4]}}")
        print(h4)
        print("  " + "-" * (sum(col_w4) + 4))
        for rep, data in sorted(rep_perf.items(), key=lambda x: -x[1]["pipeline"]):
            print(f"  {rep:<{col_w4[0]}} {data['deal_count']:>{col_w4[1]}} "
                  f"{fmt_currency(data['pipeline']):>{col_w4[2]}} "
                  f"{fmt_currency(data['weighted_base']):>{col_w4[3]}} "
                  f"{fmt_currency(data['avg_deal_size']):>{col_w4[4]}}")

    # ── Segment breakdown
    print_section("SEGMENT BREAKDOWN (Base Forecast)")
    seg = engine.segment_breakdown("base")
    for segment, value in sorted(seg.items(), key=lambda x: -x[1]):
        bar_len = int((value / total_pipeline) * 30) if total_pipeline else 0
        bar = "█" * bar_len
        print(f"  {segment:<20} {fmt_currency(value):>12}  {bar}")

    # ── Red flags
    print_section("FORECAST HEALTH FLAGS")
    flags = []
    if total_pipeline > 0:
        coverage = total_pipeline / quota if quota else None
        if coverage and coverage < 2.0:
            flags.append("🔴 Pipeline coverage below 2x — serious shortfall risk this quarter")
        elif coverage and coverage < 3.0:
            flags.append("⚠️  Pipeline coverage below 3x — limited buffer for slippage")

        # Stage concentration risk
        early_stage_pct = sum(
            d.arr_value for d in open_deals
            if engine.stage_probs.get(d.stage, 0) < 0.30
        ) / total_pipeline
        if early_stage_pct > 0.60:
            flags.append(f"⚠️  {fmt_pct(early_stage_pct)} of pipeline in early stages (< 30% probability)")

        # Deal concentration
        deal_values = sorted([d.arr_value for d in open_deals], reverse=True)
        if deal_values and deal_values[0] / total_pipeline > 0.25:
            flags.append(f"⚠️  Top deal is {fmt_pct(deal_values[0]/total_pipeline)} of pipeline — concentration risk")

        # Spread between scenarios
        total_conservative = sum(d.weighted_value(engine.stage_probs, "conservative") for d in open_deals)
        total_upside = sum(d.weighted_value(engine.stage_probs, "upside") for d in open_deals)
        spread = (total_upside - total_conservative) / total_conservative if total_conservative else 0
        if spread > 0.40:
            flags.append(f"⚠️  High scenario spread ({fmt_pct(spread)}) — forecast confidence is low")

    if flags:
        for f in flags:
            print(f"  {f}")
    else:
        print("  ✅ No critical flags detected")

    print()


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

SAMPLE_CSV = """deal_id,name,stage,arr_value,close_date,rep,segment
D001,Acme Corp ERP Integration,negotiation,85000,2026-03-15,Sarah Chen,Enterprise
D002,TechStart PLG Expansion,proposal,28000,2026-03-28,Marcus Webb,Mid-Market
D003,Global Retail Co,verbal_commit,220000,2026-03-10,Sarah Chen,Enterprise
D004,BioLab Analytics,poc,62000,2026-04-05,Jamie Park,Mid-Market
D005,FinServ Holdings,demo,150000,2026-04-20,Sarah Chen,Enterprise
D006,MidWest Logistics,qualification,35000,2026-04-30,Marcus Webb,Mid-Market
D007,Edu Platform Inc,negotiation,42000,2026-03-25,Jamie Park,SMB
D008,Healthcare Connect,proposal,95000,2026-05-15,Sarah Chen,Enterprise
D009,Startup Hub Network,demo,18000,2026-04-10,Marcus Webb,SMB
D010,CloudOps Systems,poc,75000,2026-05-01,Jamie Park,Mid-Market
D011,National Bank Corp,verbal_commit,310000,2026-03-31,Sarah Chen,Enterprise
D012,RetailTech Co,qualification,22000,2026-05-20,Marcus Webb,SMB
D013,InsurTech Platform,negotiation,88000,2026-04-15,Jamie Park,Mid-Market
D014,GovTech Solutions,proposal,175000,2026-06-01,Sarah Chen,Enterprise
D015,AgriData Systems,demo,31000,2026-05-10,Marcus Webb,Mid-Market
D016,Legal AI Corp,poc,55000,2026-04-25,Jamie Park,Mid-Market
D017,Closed Won Deal,closed_won,120000,2026-02-15,Sarah Chen,Enterprise
D018,Lost Deal,closed_lost,45000,2026-02-20,Marcus Webb,Mid-Market
"""


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def load_deals_from_csv(csv_text):
    reader = csv.DictReader(StringIO(csv_text))
    deals = []
    errors = []
    for i, row in enumerate(reader, start=2):
        try:
            deal = Deal(
                deal_id=row.get("deal_id", f"row_{i}"),
                name=row.get("name", ""),
                stage=row.get("stage", ""),
                arr_value=row.get("arr_value", 0),
                close_date=row.get("close_date", ""),
                rep=row.get("rep", ""),
                segment=row.get("segment", ""),
            )
            deals.append(deal)
        except (ValueError, KeyError) as e:
            errors.append(f"  Row {i}: {e}")
    if errors:
        print("⚠️  Skipped rows with errors:")
        for err in errors:
            print(err)
    return deals


def main():
    parser = argparse.ArgumentParser(
        description="Revenue Forecast Model — pipeline-based ARR forecasting"
    )
    parser.add_argument(
        "--csv", metavar="FILE",
        help="CSV file with pipeline data (uses sample data if not provided)"
    )
    parser.add_argument(
        "--quota", type=float, default=1_000_000,
        help="Quarterly quota target in ARR (default: $1,000,000)"
    )
    parser.add_argument(
        "--quarter", metavar="QUARTER",
        help='Current quarter filter e.g. "Q2 2026" (optional)'
    )
    parser.add_argument(
        "--scenario", choices=["conservative", "base", "upside"],
        default="base",
        help="Primary scenario to report (default: base)"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output forecast as JSON instead of formatted report"
    )
    args = parser.parse_args()

    # Load data
    if args.csv:
        try:
            with open(args.csv, "r", encoding="utf-8") as f:
                csv_text = f.read()
        except FileNotFoundError:
            print(f"Error: File not found: {args.csv}", file=sys.stderr)
            sys.exit(1)
    else:
        print("No --csv provided. Using sample pipeline data.\n")
        csv_text = SAMPLE_CSV

    deals = load_deals_from_csv(csv_text)
    if not deals:
        print("No deals loaded. Exiting.", file=sys.stderr)
        sys.exit(1)

    # Calibrate win rates from closed deals
    historical_probs = calculate_historical_win_rates(deals)
    stage_probs = historical_probs if historical_probs else DEFAULT_STAGE_PROBABILITIES

    engine = ForecastEngine(deals, stage_probs=stage_probs)

    if args.json:
        output = {
            "generated": date.today().isoformat(),
            "quota": args.quota,
            "open_pipeline": sum(d.arr_value for d in engine.open_deals()),
            "coverage_ratio": engine.coverage_ratio(args.quota, args.quarter),
            "monthly_forecast": engine.scenario_summary(),
            "quarterly_base": engine.pipeline_by_quarter("base"),
            "confidence_interval": dict(zip(
                ["p10", "p50", "p90"],
                engine.confidence_interval("base")
            )),
            "rep_performance": engine.rep_performance(),
            "segment_breakdown": engine.segment_breakdown("base"),
        }
        print(json.dumps(output, indent=2))
    else:
        print_report(engine, quota=args.quota, current_quarter=args.quarter)


if __name__ == "__main__":
    main()
