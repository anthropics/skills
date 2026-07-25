#!/usr/bin/env python3
"""
Churn & Retention Analyzer
===========================
Customer-level churn and Net Revenue Retention (NRR) analysis for B2B SaaS.

Calculates:
  - Gross Revenue Retention (GRR) and Net Revenue Retention (NRR)
  - Monthly and annual churn rates (logo + revenue)
  - Cohort-based retention curves
  - At-risk account identification
  - Expansion revenue segmentation
  - ARR waterfall (new / expansion / contraction / churn)

Usage:
  python churn_analyzer.py
  python churn_analyzer.py --csv customers.csv
  python churn_analyzer.py --period 2026-Q1 --output summary

Input format (CSV):
  customer_id, name, segment, arr, start_date, [churn_date], [expansion_arr], [contraction_arr]

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
from itertools import groupby


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

class Customer:
    def __init__(self, customer_id, name, segment, arr, start_date,
                 churn_date=None, expansion_arr=0.0, contraction_arr=0.0,
                 health_score=None):
        self.customer_id = customer_id
        self.name = name
        self.segment = segment
        self.arr = float(arr)
        self.start_date = self._parse_date(start_date)
        self.churn_date = self._parse_date(churn_date) if churn_date else None
        self.expansion_arr = float(expansion_arr or 0)
        self.contraction_arr = float(contraction_arr or 0)
        self.health_score = float(health_score) if health_score else None

    @staticmethod
    def _parse_date(value):
        if not value or str(value).strip() in ("", "None", "null"):
            return None
        for fmt in ("%Y-%m-%d", "%m/%d/%Y", "%d/%m/%Y", "%Y/%m/%d"):
            try:
                return datetime.strptime(str(value).strip(), fmt).date()
            except ValueError:
                continue
        raise ValueError(f"Cannot parse date: {value!r}")

    def is_churned(self):
        return self.churn_date is not None

    def is_active(self, as_of=None):
        as_of = as_of or date.today()
        if self.churn_date and self.churn_date <= as_of:
            return False
        return self.start_date <= as_of

    def tenure_days(self, as_of=None):
        as_of = as_of or date.today()
        end = self.churn_date if self.churn_date else as_of
        return (end - self.start_date).days

    def tenure_months(self, as_of=None):
        return self.tenure_days(as_of) / 30.44

    def cohort_month(self):
        """Acquisition cohort: YYYY-MM of start_date."""
        return self.start_date.strftime("%Y-%m")

    def cohort_quarter(self):
        q = (self.start_date.month - 1) // 3 + 1
        return f"Q{q} {self.start_date.year}"

    def net_arr(self):
        """Current ARR + expansion - contraction."""
        return self.arr + self.expansion_arr - self.contraction_arr

    def days_since_acquisition(self, as_of=None):
        as_of = as_of or date.today()
        return (as_of - self.start_date).days


# ---------------------------------------------------------------------------
# Core metrics
# ---------------------------------------------------------------------------

class RetentionAnalyzer:
    def __init__(self, customers, as_of=None):
        self.customers = customers
        self.as_of = as_of or date.today()

    def active_customers(self, as_of=None):
        as_of = as_of or self.as_of
        return [c for c in self.customers if c.is_active(as_of)]

    def churned_customers(self, start=None, end=None):
        """Customers who churned in [start, end]."""
        result = []
        for c in self.customers:
            if not c.churn_date:
                continue
            if start and c.churn_date < start:
                continue
            if end and c.churn_date > end:
                continue
            result.append(c)
        return result

    def arr_waterfall(self, period_start, period_end):
        """
        Calculate ARR waterfall for a given period.
        Returns dict with opening_arr, new_arr, expansion_arr, contraction_arr,
        churned_arr, closing_arr, nrr, grr.
        """
        # Opening: active at period start
        opening_customers = [c for c in self.customers if c.is_active(period_start)]
        opening_arr = sum(c.arr for c in opening_customers)
        opening_ids = {c.customer_id for c in opening_customers}

        # New: started during the period
        new_customers = [
            c for c in self.customers
            if period_start < c.start_date <= period_end
        ]
        new_arr = sum(c.arr for c in new_customers)

        # Churned: were active at start, churn_date within period
        churned = [
            c for c in opening_customers
            if c.churn_date and period_start < c.churn_date <= period_end
        ]
        churned_arr = sum(c.arr for c in churned)

        # Expansion and contraction: from customers active at opening
        expansion = sum(
            c.expansion_arr for c in opening_customers
            if not c.is_churned() or (c.churn_date and c.churn_date > period_end)
        )
        contraction = sum(
            c.contraction_arr for c in opening_customers
            if not c.is_churned() or (c.churn_date and c.churn_date > period_end)
        )

        closing_arr = opening_arr + new_arr + expansion - contraction - churned_arr

        grr = (opening_arr - contraction - churned_arr) / opening_arr if opening_arr else 0
        nrr = (opening_arr + expansion - contraction - churned_arr) / opening_arr if opening_arr else 0

        return {
            "period_start":   period_start.isoformat(),
            "period_end":     period_end.isoformat(),
            "opening_arr":    opening_arr,
            "new_arr":        new_arr,
            "expansion_arr":  expansion,
            "contraction_arr": contraction,
            "churned_arr":    churned_arr,
            "closing_arr":    closing_arr,
            "net_new_arr":    new_arr + expansion - contraction - churned_arr,
            "grr":            max(0.0, grr),
            "nrr":            max(0.0, nrr),
        }

    def logo_churn_rate(self, period_start, period_end):
        """Logo churn rate for a period."""
        opening = [c for c in self.customers if c.is_active(period_start)]
        churned = [
            c for c in opening
            if c.churn_date and period_start < c.churn_date <= period_end
        ]
        return len(churned) / len(opening) if opening else 0.0

    def revenue_churn_rate(self, period_start, period_end):
        """Gross revenue churn rate for a period."""
        opening = [c for c in self.customers if c.is_active(period_start)]
        opening_arr = sum(c.arr for c in opening)
        churned_arr = sum(
            c.arr for c in opening
            if c.churn_date and period_start < c.churn_date <= period_end
        )
        contraction = sum(c.contraction_arr for c in opening)
        return (churned_arr + contraction) / opening_arr if opening_arr else 0.0


# ---------------------------------------------------------------------------
# Cohort analysis
# ---------------------------------------------------------------------------

class CohortAnalyzer:
    def __init__(self, customers):
        self.customers = customers

    def build_cohorts(self):
        """Group customers by acquisition cohort (month)."""
        cohorts = defaultdict(list)
        for c in self.customers:
            cohorts[c.cohort_month()].append(c)
        return dict(sorted(cohorts.items()))

    def retention_at_month(self, cohort_customers, months_after):
        """
        What fraction of cohort ARR remains `months_after` months after acquisition?
        """
        if not cohort_customers:
            return None

        opening_arr = sum(c.arr for c in cohort_customers)
        if opening_arr == 0:
            return None

        earliest_start = min(c.start_date for c in cohort_customers)
        check_date = earliest_start + timedelta(days=int(months_after * 30.44))

        if check_date > date.today():
            return None  # Future — no data

        retained_arr = sum(
            c.arr for c in cohort_customers
            if c.is_active(check_date)
        )
        return retained_arr / opening_arr

    def retention_curve(self, cohort_customers, max_months=24):
        """Return retention at months 0, 3, 6, 9, 12, 18, 24."""
        checkpoints = [0, 3, 6, 9, 12, 18, 24]
        checkpoints = [m for m in checkpoints if m <= max_months]
        curve = {}
        for m in checkpoints:
            rate = self.retention_at_month(cohort_customers, m)
            if rate is not None:
                curve[m] = rate
        return curve

    def cohort_report(self):
        """Returns dict: cohort → {size, opening_arr, retention_curve}."""
        cohorts = self.build_cohorts()
        report = {}
        for cohort_month, customers in cohorts.items():
            curve = self.retention_curve(customers)
            report[cohort_month] = {
                "customer_count": len(customers),
                "opening_arr":    sum(c.arr for c in customers),
                "churned_count":  sum(1 for c in customers if c.is_churned()),
                "current_retention": curve.get(12, curve.get(max(curve.keys()) if curve else 0)),
                "retention_curve": curve,
            }
        return report

    def identify_at_risk(self, tenure_months_max=6, health_threshold=60):
        """
        Identify at-risk customers based on:
        - Low health score (if available)
        - Short tenure (haven't proved long-term value)
        - High contraction signals
        """
        at_risk = []
        for c in self.customers:
            if c.is_churned():
                continue
            reasons = []
            score = 0

            # Health score signal
            if c.health_score is not None and c.health_score < health_threshold:
                reasons.append(f"Health score {c.health_score:.0f} < {health_threshold}")
                score += 40

            # Early tenure risk
            tenure = c.tenure_months()
            if tenure < tenure_months_max:
                reasons.append(f"Tenure {tenure:.1f} months (< {tenure_months_max})")
                score += 20

            # Contraction signal
            if c.contraction_arr > 0:
                contraction_pct = c.contraction_arr / c.arr
                reasons.append(f"Contraction {contraction_pct:.0%} of ARR")
                score += 30

            # No expansion in mature account
            if tenure > 12 and c.expansion_arr == 0:
                reasons.append("No expansion after 12+ months (stagnant)")
                score += 10

            if score > 0:
                at_risk.append({
                    "customer_id": c.customer_id,
                    "name":        c.name,
                    "segment":     c.segment,
                    "arr":         c.arr,
                    "tenure_months": round(tenure, 1),
                    "health_score": c.health_score,
                    "risk_score":  score,
                    "risk_reasons": reasons,
                })

        return sorted(at_risk, key=lambda x: -x["risk_score"])


# ---------------------------------------------------------------------------
# Expansion analysis
# ---------------------------------------------------------------------------

class ExpansionAnalyzer:
    def __init__(self, customers):
        self.customers = customers

    def expansion_summary(self):
        active = [c for c in self.customers if not c.is_churned()]
        expanding = [c for c in active if c.expansion_arr > 0]
        contracting = [c for c in active if c.contraction_arr > 0]

        total_arr = sum(c.arr for c in active)
        total_expansion = sum(c.expansion_arr for c in active)
        total_contraction = sum(c.contraction_arr for c in active)

        return {
            "active_customers":   len(active),
            "total_arr":          total_arr,
            "expanding_count":    len(expanding),
            "contracting_count":  len(contracting),
            "expansion_arr":      total_expansion,
            "contraction_arr":    total_contraction,
            "expansion_rate":     total_expansion / total_arr if total_arr else 0,
            "contraction_rate":   total_contraction / total_arr if total_arr else 0,
            "net_expansion_rate": (total_expansion - total_contraction) / total_arr if total_arr else 0,
        }

    def expansion_by_segment(self):
        active = [c for c in self.customers if not c.is_churned()]
        by_segment = defaultdict(lambda: {"arr": 0.0, "expansion": 0.0,
                                          "contraction": 0.0, "count": 0})
        for c in active:
            seg = c.segment or "Unspecified"
            by_segment[seg]["arr"] += c.arr
            by_segment[seg]["expansion"] += c.expansion_arr
            by_segment[seg]["contraction"] += c.contraction_arr
            by_segment[seg]["count"] += 1

        result = {}
        for seg, data in by_segment.items():
            arr = data["arr"]
            result[seg] = {
                "customer_count":  data["count"],
                "arr":             arr,
                "expansion_arr":   data["expansion"],
                "contraction_arr": data["contraction"],
                "expansion_rate":  data["expansion"] / arr if arr else 0,
                "net_nrr_contribution": (arr + data["expansion"] - data["contraction"]) / arr if arr else 0,
            }
        return result

    def top_expansion_candidates(self, min_tenure_months=6, min_arr=5000):
        """
        Customers who are active, healthy tenure, but have zero expansion.
        These are upsell/expansion targets.
        """
        active = [c for c in self.customers if not c.is_churned()]
        candidates = []
        for c in active:
            tenure = c.tenure_months()
            if (tenure >= min_tenure_months
                    and c.arr >= min_arr
                    and c.expansion_arr == 0
                    and (c.health_score is None or c.health_score >= 60)):
                candidates.append({
                    "customer_id":   c.customer_id,
                    "name":          c.name,
                    "segment":       c.segment,
                    "arr":           c.arr,
                    "tenure_months": round(tenure, 1),
                    "health_score":  c.health_score,
                })
        return sorted(candidates, key=lambda x: -x["arr"])


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


def nrr_status(nrr):
    if nrr >= 1.20:
        return "✅ World-class"
    if nrr >= 1.10:
        return "✅ Healthy"
    if nrr >= 1.00:
        return "⚠️  Acceptable"
    if nrr >= 0.90:
        return "🔴 Concerning"
    return "🔴 Crisis"


def grr_status(grr):
    if grr >= 0.90:
        return "✅ Strong"
    if grr >= 0.85:
        return "⚠️  Acceptable"
    return "🔴 Below threshold"


def print_header(title):
    width = 70
    print()
    print("=" * width)
    print(f"  {title}")
    print("=" * width)


def print_section(title):
    print(f"\n--- {title} ---")


def print_full_report(customers, period_start, period_end):
    analyzer = RetentionAnalyzer(customers, as_of=period_end)
    cohort_analyzer = CohortAnalyzer(customers)
    expansion_analyzer = ExpansionAnalyzer(customers)

    print_header("CHURN & RETENTION ANALYZER")
    print(f"  Analysis period: {period_start.isoformat()} → {period_end.isoformat()}")
    print(f"  Total customers in dataset: {len(customers)}")
    active = analyzer.active_customers(period_end)
    churned_in_period = analyzer.churned_customers(period_start, period_end)
    print(f"  Active at period end: {len(active)}")
    print(f"  Churned in period:    {len(churned_in_period)}")

    # ── ARR Waterfall
    print_section("ARR WATERFALL")
    wf = analyzer.arr_waterfall(period_start, period_end)
    print(f"  Opening ARR:           {fmt_currency(wf['opening_arr'])}")
    print(f"  + New Logo ARR:       +{fmt_currency(wf['new_arr'])}")
    print(f"  + Expansion ARR:      +{fmt_currency(wf['expansion_arr'])}")
    print(f"  - Contraction ARR:    -{fmt_currency(wf['contraction_arr'])}")
    print(f"  - Churned ARR:        -{fmt_currency(wf['churned_arr'])}")
    print(f"  {'─'*42}")
    print(f"  Closing ARR:           {fmt_currency(wf['closing_arr'])}")
    print(f"  Net New ARR:          {'+' if wf['net_new_arr'] >= 0 else ''}{fmt_currency(wf['net_new_arr'])}")

    # ── NRR / GRR
    print_section("RETENTION METRICS")
    nrr = wf["nrr"]
    grr = wf["grr"]
    logo_churn = analyzer.logo_churn_rate(period_start, period_end)
    rev_churn = analyzer.revenue_churn_rate(period_start, period_end)

    print(f"  NRR (Net Revenue Retention):   {fmt_pct(nrr)}   {nrr_status(nrr)}")
    print(f"  GRR (Gross Revenue Retention): {fmt_pct(grr)}   {grr_status(grr)}")
    print(f"  Logo Churn Rate (period):      {fmt_pct(logo_churn)}")
    print(f"  Revenue Churn Rate (period):   {fmt_pct(rev_churn)}")
    if wf["opening_arr"] > 0:
        expansion_rate = wf["expansion_arr"] / wf["opening_arr"]
        print(f"  Expansion Rate (period):       {fmt_pct(expansion_rate)}")
    print()
    print(f"  NRR Benchmark: >120% world-class | 100-120% healthy | <100% fix immediately")

    # ── Expansion summary
    print_section("EXPANSION REVENUE")
    exp = expansion_analyzer.expansion_summary()
    print(f"  Expanding customers:  {exp['expanding_count']} / {exp['active_customers']} ({fmt_pct(exp['expanding_count']/exp['active_customers']) if exp['active_customers'] else '—'})")
    print(f"  Contracting:          {exp['contracting_count']} / {exp['active_customers']}")
    print(f"  Expansion ARR:        {fmt_currency(exp['expansion_arr'])} ({fmt_pct(exp['expansion_rate'])} of base)")
    print(f"  Contraction ARR:      {fmt_currency(exp['contraction_arr'])}")
    print(f"  Net Expansion Rate:   {fmt_pct(exp['net_expansion_rate'])}")

    # ── Segment breakdown
    print_section("SEGMENT BREAKDOWN (NRR Components)")
    seg_data = expansion_analyzer.expansion_by_segment()
    col_w = [18, 8, 12, 10, 10, 10]
    h = (f"  {'Segment':<{col_w[0]}} {'Custs':>{col_w[1]}} {'ARR':>{col_w[2]}} "
         f"{'Expansion':>{col_w[3]}} {'Contraction':>{col_w[4]}} {'NRR':>{col_w[5]}}")
    print(h)
    print("  " + "-" * (sum(col_w) + 5))
    for seg, data in sorted(seg_data.items(), key=lambda x: -x[1]["arr"]):
        print(f"  {seg:<{col_w[0]}} {data['customer_count']:>{col_w[1]}} "
              f"{fmt_currency(data['arr']):>{col_w[2]}} "
              f"{fmt_currency(data['expansion_arr']):>{col_w[3]}} "
              f"{fmt_currency(data['contraction_arr']):>{col_w[4]}} "
              f"{fmt_pct(data['net_nrr_contribution']):>{col_w[5]}}")

    # ── Cohort retention
    print_section("COHORT RETENTION CURVES")
    cohort_report = cohort_analyzer.cohort_report()
    print(f"  {'Cohort':<10} {'Custs':>6} {'Opening ARR':>13} {'Mo.3':>8} {'Mo.6':>8} {'Mo.12':>8}")
    print("  " + "-" * 57)
    for cohort, data in cohort_report.items():
        curve = data["retention_curve"]
        m3 = fmt_pct(curve[3]) if 3 in curve else "  —"
        m6 = fmt_pct(curve[6]) if 6 in curve else "  —"
        m12 = fmt_pct(curve[12]) if 12 in curve else "  —"
        print(f"  {cohort:<10} {data['customer_count']:>6} "
              f"{fmt_currency(data['opening_arr']):>13} "
              f"{m3:>8} {m6:>8} {m12:>8}")

    # ── At-risk accounts
    print_section("AT-RISK ACCOUNTS")
    at_risk = cohort_analyzer.identify_at_risk()
    if at_risk:
        print(f"  {'Customer':<22} {'Segment':<14} {'ARR':>10} {'Tenure':>8} {'Risk':>6}  Reason")
        print("  " + "-" * 80)
        for acct in at_risk[:10]:  # Top 10
            reason_short = acct["risk_reasons"][0] if acct["risk_reasons"] else ""
            tenure_str = f"{acct['tenure_months']}mo"
            print(f"  {acct['name']:<22} {acct['segment']:<14} "
                  f"{fmt_currency(acct['arr']):>10} {tenure_str:>8} "
                  f"{acct['risk_score']:>5}  {reason_short}")
        if len(at_risk) > 10:
            print(f"  ... and {len(at_risk) - 10} more at-risk accounts")
    else:
        print("  ✅ No at-risk accounts identified")

    # ── Expansion candidates
    print_section("EXPANSION CANDIDATES (no expansion yet, healthy tenure)")
    candidates = expansion_analyzer.top_expansion_candidates()
    if candidates:
        print(f"  {'Customer':<22} {'Segment':<14} {'ARR':>10} {'Tenure':>8}  Action")
        print("  " + "-" * 70)
        for c in candidates[:8]:
            action = "Upsell review" if c["arr"] > 20000 else "Seat expansion call"
            tenure_str = f"{c['tenure_months']}mo"
            print(f"  {c['name']:<22} {c['segment']:<14} "
                  f"{fmt_currency(c['arr']):>10} {tenure_str:>8}  {action}")
    else:
        print("  ✅ All eligible accounts have expansion in motion")

    # ── Red flags
    print_section("HEALTH FLAGS")
    flags = []
    if nrr < 1.0:
        flags.append("🔴 NRR below 100% — revenue base is shrinking. Fix before scaling sales.")
    if grr < 0.85:
        flags.append(f"🔴 GRR {fmt_pct(grr)} — gross retention below 85% threshold. Churn is a product/CS problem.")
    if logo_churn > 0.05:
        flags.append(f"⚠️  Logo churn {fmt_pct(logo_churn)} this period — run cohort analysis to find the pattern.")
    if exp["expansion_rate"] < 0.10 and exp["active_customers"] > 10:
        flags.append("⚠️  Expansion rate below 10% — upsell motion is weak or non-existent.")
    churned_arr_pct = wf["churned_arr"] / wf["opening_arr"] if wf["opening_arr"] else 0
    if churned_arr_pct > 0.10:
        flags.append(f"🔴 Revenue churn at {fmt_pct(churned_arr_pct)} of opening ARR this period — high urgency.")
    if len(at_risk) > len(active) * 0.20:
        flags.append(f"⚠️  {len(at_risk)} of {len(active)} active accounts flagged at-risk ({fmt_pct(len(at_risk)/len(active) if active else 0)})")

    if flags:
        for f in flags:
            print(f"  {f}")
    else:
        print("  ✅ No critical health flags")

    print()


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

SAMPLE_CSV = """customer_id,name,segment,arr,start_date,churn_date,expansion_arr,contraction_arr,health_score
C001,Acme Manufacturing,Enterprise,120000,2023-01-15,,45000,0,82
C002,TechStart Inc,Mid-Market,28000,2023-02-01,,8000,0,74
C003,Global Retail Co,Enterprise,250000,2023-01-05,,0,25000,45
C004,MedTech Solutions,Mid-Market,45000,2023-03-10,,15000,0,88
C005,FinServ Holdings,Enterprise,185000,2023-01-20,2023-09-15,0,0,
C006,StartupHub Network,SMB,12000,2023-04-01,,0,3000,55
C007,EduPlatform Inc,Mid-Market,32000,2023-02-15,,10000,0,91
C008,BioLab Analytics,Enterprise,95000,2023-01-10,,20000,0,78
C009,RegionalBank Corp,Enterprise,310000,2023-03-01,,75000,0,85
C010,CloudOps Systems,Mid-Market,38000,2023-05-01,2024-01-10,0,0,
C011,InsurTech Platform,Mid-Market,55000,2023-06-15,,0,0,62
C012,LegalAI Corp,SMB,18000,2023-07-01,,5000,0,79
C013,RetailChain Ltd,Enterprise,140000,2023-04-20,,0,20000,41
C014,DataPipeline Co,Mid-Market,42000,2023-08-01,,12000,0,83
C015,NanoTech Startup,SMB,9500,2023-09-15,2024-02-28,0,0,
C016,MedDevice Corp,Enterprise,220000,2023-02-28,,60000,0,92
C017,ConsultingFirm XYZ,SMB,15000,2023-10-01,,0,5000,38
C018,GovTech Solutions,Enterprise,175000,2023-11-15,,0,0,71
C019,AgriData Systems,Mid-Market,31000,2024-01-10,,8000,0,77
C020,HealthcarePlus,Mid-Market,62000,2024-02-01,,0,0,65
"""


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def load_customers_from_csv(csv_text):
    reader = csv.DictReader(StringIO(csv_text))
    customers = []
    errors = []
    for i, row in enumerate(reader, start=2):
        try:
            c = Customer(
                customer_id=row.get("customer_id", f"row_{i}"),
                name=row.get("name", f"Customer {i}"),
                segment=row.get("segment", ""),
                arr=row.get("arr", 0),
                start_date=row.get("start_date", ""),
                churn_date=row.get("churn_date", None) or None,
                expansion_arr=row.get("expansion_arr", 0) or 0,
                contraction_arr=row.get("contraction_arr", 0) or 0,
                health_score=row.get("health_score", None) or None,
            )
            customers.append(c)
        except (ValueError, KeyError) as e:
            errors.append(f"  Row {i}: {e}")
    if errors:
        print("⚠️  Skipped rows with errors:")
        for err in errors:
            print(err)
    return customers


def parse_period(period_str):
    """Parse 'YYYY-QN' or 'YYYY-MM' into (start_date, end_date)."""
    if not period_str:
        today = date.today()
        q = (today.month - 1) // 3
        start = date(today.year, q * 3 + 1, 1)
        # End of current quarter
        end_month = start.month + 2
        end_year = start.year + (end_month - 1) // 12
        end_month = ((end_month - 1) % 12) + 1
        import calendar
        end_day = calendar.monthrange(end_year, end_month)[1]
        return start, date(end_year, end_month, end_day)

    import calendar
    if "-Q" in period_str:
        year, qpart = period_str.split("-Q")
        year = int(year)
        q = int(qpart)
        start_month = (q - 1) * 3 + 1
        end_month = start_month + 2
        start = date(year, start_month, 1)
        end = date(year, end_month, calendar.monthrange(year, end_month)[1])
        return start, end

    # YYYY-MM
    year, month = period_str.split("-")
    year, month = int(year), int(month)
    start = date(year, month, 1)
    end = date(year, month, calendar.monthrange(year, month)[1])
    return start, end


def main():
    parser = argparse.ArgumentParser(
        description="Churn & Retention Analyzer — NRR, cohort analysis, at-risk detection"
    )
    parser.add_argument(
        "--csv", metavar="FILE",
        help="CSV file with customer data (uses sample data if not provided)"
    )
    parser.add_argument(
        "--period", metavar="PERIOD",
        help='Analysis period: "2026-Q1" or "2026-03" (defaults to current quarter)'
    )
    parser.add_argument(
        "--output", choices=["summary", "full", "json"],
        default="full",
        help="Output format (default: full)"
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
        print("No --csv provided. Using sample customer data.\n")
        csv_text = SAMPLE_CSV

    customers = load_customers_from_csv(csv_text)
    if not customers:
        print("No customers loaded. Exiting.", file=sys.stderr)
        sys.exit(1)

    period_start, period_end = parse_period(args.period)

    if args.output == "json":
        analyzer = RetentionAnalyzer(customers, as_of=period_end)
        cohort_analyzer = CohortAnalyzer(customers)
        expansion_analyzer = ExpansionAnalyzer(customers)
        wf = analyzer.arr_waterfall(period_start, period_end)
        output = {
            "period": {"start": period_start.isoformat(), "end": period_end.isoformat()},
            "arr_waterfall": wf,
            "logo_churn_rate": analyzer.logo_churn_rate(period_start, period_end),
            "revenue_churn_rate": analyzer.revenue_churn_rate(period_start, period_end),
            "cohort_report": {k: {**v, "retention_curve": {str(m): r for m, r in v["retention_curve"].items()}}
                              for k, v in cohort_analyzer.cohort_report().items()},
            "at_risk_accounts": cohort_analyzer.identify_at_risk(),
            "expansion_summary": expansion_analyzer.expansion_summary(),
            "expansion_by_segment": expansion_analyzer.expansion_by_segment(),
            "expansion_candidates": expansion_analyzer.top_expansion_candidates(),
        }
        print(json.dumps(output, indent=2))
    elif args.output == "summary":
        analyzer = RetentionAnalyzer(customers, as_of=period_end)
        wf = analyzer.arr_waterfall(period_start, period_end)
        print_header("NRR SUMMARY")
        print(f"  Period:  {period_start.isoformat()} → {period_end.isoformat()}")
        print(f"  NRR:     {fmt_pct(wf['nrr'])}  {nrr_status(wf['nrr'])}")
        print(f"  GRR:     {fmt_pct(wf['grr'])}  {grr_status(wf['grr'])}")
        print(f"  Opening: {fmt_currency(wf['opening_arr'])}")
        print(f"  Closing: {fmt_currency(wf['closing_arr'])}")
        print(f"  Net New: {fmt_currency(wf['net_new_arr'])}")
        print()
    else:
        print_full_report(customers, period_start, period_end)


if __name__ == "__main__":
    main()
