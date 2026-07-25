#!/usr/bin/env python3
"""
purchasing_cycle_analyzer.py — Per-category cycle-time scorecard with bottleneck flagging.

Input: a list of PO records with timestamps for each step (request, approval, PO,
goods receipt, payment). Output: per-category cycle-time statistics (median, P90)
plus a Goldratt-style bottleneck flag for any category whose cycle time exceeds
2x the cross-category median — the constraint is one specific category, not the
"average procurement process."

Stdlib only. Deterministic. No LLM calls.
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path
from typing import Any


# ---------- Data model ----------

@dataclass
class PORecord:
    category: str
    request_date: date | None
    approval_date: date | None
    po_issued_date: date | None
    goods_received_date: date | None
    payment_date: date | None
    approver_hops: int

    @staticmethod
    def _parse(d: Any) -> date | None:
        if not d:
            return None
        if isinstance(d, date):
            return d
        try:
            return datetime.strptime(str(d)[:10], "%Y-%m-%d").date()
        except ValueError:
            return None

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> "PORecord":
        return cls(
            category=str(d.get("category", "Uncategorized")),
            request_date=cls._parse(d.get("request_date")),
            approval_date=cls._parse(d.get("approval_date")),
            po_issued_date=cls._parse(d.get("po_issued_date")),
            goods_received_date=cls._parse(d.get("goods_received_date")),
            payment_date=cls._parse(d.get("payment_date")),
            approver_hops=int(d.get("approver_hops", 0)),
        )


def _days(a: date | None, b: date | None) -> int | None:
    if a is None or b is None:
        return None
    return (b - a).days


# ---------- Aggregation ----------

@dataclass
class CategoryStats:
    category: str
    n: int
    request_to_po_median: float | None
    request_to_po_p90: float | None
    po_to_pay_median: float | None
    po_to_pay_p90: float | None
    approver_hops_median: float | None


def _p90(values: list[int]) -> float:
    if not values:
        return 0.0
    s = sorted(values)
    # Linear interpolation P90 (stdlib has no quantiles in older pythons; do manually)
    k = (len(s) - 1) * 0.9
    lo = int(k)
    hi = min(lo + 1, len(s) - 1)
    frac = k - lo
    return s[lo] + (s[hi] - s[lo]) * frac


def _median(values: list[int]) -> float | None:
    return statistics.median(values) if values else None


def per_category_stats(records: list[PORecord]) -> dict[str, CategoryStats]:
    by_cat: dict[str, list[PORecord]] = {}
    for r in records:
        by_cat.setdefault(r.category, []).append(r)

    result: dict[str, CategoryStats] = {}
    for cat, recs in by_cat.items():
        r2po = [d for d in (_days(r.request_date, r.po_issued_date) for r in recs) if d is not None]
        po2pay = [d for d in (_days(r.po_issued_date, r.payment_date) for r in recs) if d is not None]
        hops = [r.approver_hops for r in recs if r.approver_hops >= 0]
        result[cat] = CategoryStats(
            category=cat,
            n=len(recs),
            request_to_po_median=_median(r2po),
            request_to_po_p90=(_p90(r2po) if r2po else None),
            po_to_pay_median=_median(po2pay),
            po_to_pay_p90=(_p90(po2pay) if po2pay else None),
            approver_hops_median=_median(hops),
        )
    return result


def overall_median_r2po(stats: dict[str, CategoryStats]) -> float:
    """Cross-category median of request->PO median (used as the bottleneck baseline)."""
    medians = [s.request_to_po_median for s in stats.values() if s.request_to_po_median is not None]
    if not medians:
        return 0.0
    return statistics.median(medians)


# ---------- Rendering ----------

def render_markdown(stats: dict[str, CategoryStats]) -> str:
    baseline = overall_median_r2po(stats)
    threshold = baseline * 2.0 if baseline > 0 else None

    lines: list[str] = []
    lines.append("# Purchasing Cycle-Time Scorecard\n")
    lines.append(f"- **Categories analyzed:** {len(stats)}")
    if baseline > 0:
        lines.append(f"- **Cross-category median (Request → PO):** {baseline:.1f} days")
        lines.append(f"- **Bottleneck threshold (2× median):** {threshold:.1f} days\n")
    else:
        lines.append("- (Insufficient data for cross-category baseline)\n")

    lines.append("## Per-category cycle times\n")
    lines.append("| Category | N | Req→PO median | Req→PO P90 | PO→Pay median | PO→Pay P90 | Hops | Bottleneck? |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|---|")

    sorted_cats = sorted(
        stats.values(),
        key=lambda s: -(s.request_to_po_median or 0),
    )
    for s in sorted_cats:
        is_bottleneck = (
            threshold is not None
            and s.request_to_po_median is not None
            and s.request_to_po_median > threshold
        )
        flag = "**BOTTLENECK**" if is_bottleneck else "—"
        lines.append(
            f"| {s.category} | {s.n} | "
            f"{_fmt(s.request_to_po_median)} | {_fmt(s.request_to_po_p90)} | "
            f"{_fmt(s.po_to_pay_median)} | {_fmt(s.po_to_pay_p90)} | "
            f"{_fmt(s.approver_hops_median)} | {flag} |"
        )
    lines.append("")

    # Goldratt commentary
    bottlenecks = [
        s for s in stats.values()
        if threshold is not None
        and s.request_to_po_median is not None
        and s.request_to_po_median > threshold
    ]
    lines.append("## Goldratt — find the constraint\n")
    if bottlenecks:
        lines.append(
            f"**{len(bottlenecks)}** categor{'y' if len(bottlenecks)==1 else 'ies'} "
            f"exceed the 2× median bottleneck threshold:\n"
        )
        for s in bottlenecks:
            lines.append(
                f"- **{s.category}** — Request→PO median {s.request_to_po_median:.1f}d, "
                f"P90 {_fmt(s.request_to_po_p90)}d, "
                f"approver hops median {_fmt(s.approver_hops_median)}"
            )
        lines.append("")
        lines.append(
            "Improving any non-bottleneck category does not change overall throughput. "
            "Focus on the constraint first — typical fixes per stage:"
        )
        lines.append("")
        lines.append("- **Long Request→Approval:** approval routing, parallel review, raise auto-approve threshold for low-risk categories.")
        lines.append("- **Long Approval→PO:** PO creation friction; consider catalog buys for repeating categories.")
        lines.append("- **High approver hops:** collapse routing tiers; one approver per $-band, not three.")
        lines.append("- **Long PO→Pay:** AP cycle (3-way match, batch runs); negotiate net-terms only after measuring.")
    else:
        lines.append("No category exceeds the 2× bottleneck threshold. The process is uniformly fast (or uniformly slow — check the baseline).\n")

    return "\n".join(lines)


def _fmt(v: float | None) -> str:
    if v is None:
        return "—"
    return f"{v:.1f}"


# ---------- Sample data ----------

SAMPLE_INPUT: list[dict[str, Any]] = [
    # Fast: SaaS / Subscription Software
    {"category": "SaaS / Subscription Software", "request_date": "2026-01-02",
     "approval_date": "2026-01-03", "po_issued_date": "2026-01-04",
     "goods_received_date": "2026-01-04", "payment_date": "2026-01-15",
     "approver_hops": 1},
    {"category": "SaaS / Subscription Software", "request_date": "2026-02-01",
     "approval_date": "2026-02-03", "po_issued_date": "2026-02-05",
     "goods_received_date": "2026-02-05", "payment_date": "2026-02-20",
     "approver_hops": 1},
    {"category": "SaaS / Subscription Software", "request_date": "2026-03-01",
     "approval_date": "2026-03-02", "po_issued_date": "2026-03-04",
     "goods_received_date": "2026-03-04", "payment_date": "2026-03-22",
     "approver_hops": 1},
    # Slow: Outside Counsel (legal review is the bottleneck)
    {"category": "Outside Counsel", "request_date": "2026-01-05",
     "approval_date": "2026-02-15", "po_issued_date": "2026-02-28",
     "goods_received_date": "2026-02-28", "payment_date": "2026-03-30",
     "approver_hops": 4},
    {"category": "Outside Counsel", "request_date": "2026-02-01",
     "approval_date": "2026-03-12", "po_issued_date": "2026-03-30",
     "goods_received_date": "2026-03-30", "payment_date": "2026-04-30",
     "approver_hops": 4},
    {"category": "Outside Counsel", "request_date": "2026-03-01",
     "approval_date": "2026-04-25", "po_issued_date": "2026-05-05",
     "goods_received_date": "2026-05-05", "payment_date": "2026-06-15",
     "approver_hops": 5},
    # Medium: Cloud Infrastructure
    {"category": "Cloud Infrastructure", "request_date": "2026-01-10",
     "approval_date": "2026-01-15", "po_issued_date": "2026-01-22",
     "goods_received_date": "2026-01-22", "payment_date": "2026-02-15",
     "approver_hops": 2},
    {"category": "Cloud Infrastructure", "request_date": "2026-02-05",
     "approval_date": "2026-02-12", "po_issued_date": "2026-02-20",
     "goods_received_date": "2026-02-20", "payment_date": "2026-03-12",
     "approver_hops": 2},
    # Medium: Recruiting
    {"category": "Recruiting Services", "request_date": "2026-01-15",
     "approval_date": "2026-01-22", "po_issued_date": "2026-01-28",
     "goods_received_date": "2026-01-28", "payment_date": "2026-02-20",
     "approver_hops": 2},
    {"category": "Recruiting Services", "request_date": "2026-02-10",
     "approval_date": "2026-02-15", "po_issued_date": "2026-02-22",
     "goods_received_date": "2026-02-22", "payment_date": "2026-03-15",
     "approver_hops": 2},
]


# ---------- CLI ----------

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=str, help="Path to JSON list of PO records")
    p.add_argument("--output", type=str, help="Path to write markdown report")
    p.add_argument("--sample", action="store_true", help="Run with built-in sample data")
    args = p.parse_args(argv)

    if args.sample:
        data = SAMPLE_INPUT
    elif args.input:
        try:
            data = json.loads(Path(args.input).read_text())
        except Exception as e:
            print(f"error reading {args.input}: {e}", file=sys.stderr)
            return 2
    else:
        p.print_help()
        return 0

    records = [PORecord.from_dict(d) for d in data]
    stats = per_category_stats(records)
    md = render_markdown(stats)

    if args.output:
        Path(args.output).write_text(md)
        print(f"wrote {args.output}")
    else:
        print(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
