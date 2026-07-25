#!/usr/bin/env python3
"""
decision_tracker.py — Board Meeting Decision Parser & Reporter
Part of the C-Level Advisor / Decision Logger skill.

Parses the Layer 2 index ~/.claude/decisions/approved/decisions.md and produces actionable reports.
(Legacy location memory/board-meetings/decisions.md still works via --file.)
Stdlib only. No dependencies.

Usage:
    python decision_tracker.py --summary
    python decision_tracker.py --overdue
    python decision_tracker.py --conflicts
    python decision_tracker.py --owner "CMO"
    python decision_tracker.py --search "pricing"
    python decision_tracker.py --due-within 7
    python decision_tracker.py --demo          # Run with sample data
"""

import argparse
import os
import re
import sys
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Optional


# ─────────────────────────────────────────────
# Data structures
# ─────────────────────────────────────────────

class ActionItem:
    def __init__(self, text: str, owner: str, due: Optional[date],
                 review: Optional[date], completed: bool, completed_date: Optional[date],
                 result: str):
        self.text = text
        self.owner = owner
        self.due = due
        self.review = review
        self.completed = completed
        self.completed_date = completed_date
        self.result = result

    def is_overdue(self) -> bool:
        if self.completed:
            return False
        if self.due and self.due < date.today():
            return True
        return False

    def is_due_within(self, days: int) -> bool:
        if self.completed:
            return False
        if self.due:
            return date.today() <= self.due <= date.today() + timedelta(days=days)
        return False


class Decision:
    def __init__(self):
        self.date: Optional[date] = None
        self.title: str = ""
        self.decision: str = ""
        self.owner: str = ""
        self.deadline: Optional[date] = None
        self.review: Optional[date] = None
        self.rationale: str = ""
        self.user_override: str = ""
        self.rejected: list[str] = []
        self.action_items: list[ActionItem] = []
        self.supersedes: str = ""
        self.superseded_by: str = ""
        self.raw_transcript: str = ""

    def is_active(self) -> bool:
        return not bool(self.superseded_by.strip())

    def has_override(self) -> bool:
        return bool(self.user_override.strip())


# ─────────────────────────────────────────────
# Parser
# ─────────────────────────────────────────────

def parse_date(s: str) -> Optional[date]:
    """Parse YYYY-MM-DD or return None."""
    if not s:
        return None
    s = s.strip()
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%d.%m.%Y"):
        try:
            return datetime.strptime(s, fmt).date()
        except ValueError:
            continue
    return None


def parse_action_item(line: str) -> Optional[ActionItem]:
    """
    Parse a line like:
      - [ ] Action text — Owner: CMO — Due: 2026-03-15 — Review: 2026-03-29
      - [x] Action text — Owner: CEO — Completed: 2026-03-10 — Result: Done
    """
    line = line.strip()
    if not line.startswith("- ["):
        return None

    completed = line.startswith("- [x]") or line.startswith("- [X]")
    text_start = line.find("]") + 1
    raw = line[text_start:].strip()

    # Split on " — " (em dash with spaces) or " - " fallback
    parts_raw = re.split(r"\s+[—\-]{1,2}\s+", raw)
    text = parts_raw[0].strip() if parts_raw else raw

    def extract(label: str, parts: list[str]) -> str:
        for p in parts:
            if p.lower().startswith(label.lower() + ":"):
                return p[len(label) + 1:].strip()
        return ""

    owner = extract("Owner", parts_raw[1:])
    due_str = extract("Due", parts_raw[1:])
    review_str = extract("Review", parts_raw[1:])
    completed_str = extract("Completed", parts_raw[1:])
    result = extract("Result", parts_raw[1:])

    return ActionItem(
        text=text,
        owner=owner,
        due=parse_date(due_str),
        review=parse_date(review_str),
        completed=completed,
        completed_date=parse_date(completed_str),
        result=result,
    )


def parse_decisions(content: str) -> list[Decision]:
    """Parse the full decisions.md content into Decision objects."""
    decisions = []
    current: Optional[Decision] = None
    in_rejected = False
    in_actions = False

    for line in content.splitlines():
        # New decision entry
        header_match = re.match(r"^## (\d{4}-\d{2}-\d{2}) — (.+)$", line)
        if header_match:
            if current:
                decisions.append(current)
            current = Decision()
            current.date = parse_date(header_match.group(1))
            current.title = header_match.group(2).strip()
            in_rejected = False
            in_actions = False
            continue

        if current is None:
            continue

        # Field parsing
        def extract_field(label: str) -> Optional[str]:
            pattern = rf"^\*\*{re.escape(label)}:\*\*\s*(.*)$"
            m = re.match(pattern, line)
            return m.group(1).strip() if m else None

        val = extract_field("Decision")
        if val is not None:
            current.decision = val
            in_rejected = False
            in_actions = False
            continue

        val = extract_field("Owner")
        if val is not None:
            current.owner = val
            continue

        val = extract_field("Deadline")
        if val is not None:
            current.deadline = parse_date(val)
            continue

        val = extract_field("Review")
        if val is not None:
            current.review = parse_date(val)
            continue

        val = extract_field("Rationale")
        if val is not None:
            current.rationale = val
            continue

        val = extract_field("User Override")
        if val is not None:
            current.user_override = val
            in_rejected = False
            in_actions = False
            continue

        val = extract_field("Supersedes")
        if val is not None:
            current.supersedes = val
            continue

        val = extract_field("Superseded by")
        if val is not None:
            current.superseded_by = val
            continue

        val = extract_field("Raw transcript")
        if val is not None:
            current.raw_transcript = val
            continue

        # Section headers
        if re.match(r"^\*\*Rejected:\*\*", line):
            in_rejected = True
            in_actions = False
            continue

        if re.match(r"^\*\*Action Items:\*\*", line):
            in_actions = True
            in_rejected = False
            continue

        if line.startswith("**"):
            in_rejected = False
            in_actions = False

        # List items
        if in_rejected and line.strip().startswith("-"):
            item = line.strip().lstrip("- ").strip()
            if item and not item.startswith("<!--"):
                current.rejected.append(item)
            continue

        if in_actions and line.strip().startswith("- ["):
            action = parse_action_item(line)
            if action:
                current.action_items.append(action)
            continue

    if current:
        decisions.append(current)

    return decisions


# ─────────────────────────────────────────────
# Reports
# ─────────────────────────────────────────────

def fmt_date(d: Optional[date]) -> str:
    return d.strftime("%Y-%m-%d") if d else "—"


def fmt_delta(d: Optional[date]) -> str:
    if not d:
        return ""
    delta = (d - date.today()).days
    if delta < 0:
        return f"  ⚠️  {abs(delta)}d overdue"
    if delta == 0:
        return "  🔴 DUE TODAY"
    if delta <= 3:
        return f"  🟡 {delta}d left"
    return f"  ({delta}d)"


def print_section(title: str):
    print(f"\n{'═' * 60}")
    print(f"  {title}")
    print(f"{'═' * 60}")


def report_summary(decisions: list[Decision]):
    active = [d for d in decisions if d.is_active()]
    all_actions = [a for d in decisions for a in d.action_items]
    open_actions = [a for a in all_actions if not a.completed]
    overdue = [a for a in all_actions if a.is_overdue()]
    overrides = [d for d in decisions if d.has_override()]
    dnr_count = sum(len(d.rejected) for d in decisions)

    print_section("DECISION LOG SUMMARY")
    print(f"  Total decisions:      {len(decisions)}")
    print(f"  Active (not super.):  {len(active)}")
    print(f"  Superseded:           {len(decisions) - len(active)}")
    print(f"  Founder overrides:    {len(overrides)}")
    print(f"  DO_NOT_RESURFACE:     {dnr_count}")
    print(f"  Total action items:   {len(all_actions)}")
    print(f"  Open action items:    {len(open_actions)}")
    print(f"  Overdue:              {len(overdue)}")

    if overdue:
        print(f"\n  {'─' * 40}")
        print(f"  ⚠️  OVERDUE ITEMS ({len(overdue)})")
        print(f"  {'─' * 40}")
        for a in overdue:
            print(f"  • [{a.owner}] {a.text}")
            print(f"    Due: {fmt_date(a.due)}{fmt_delta(a.due)}")

    print(f"\n  {'─' * 40}")
    print(f"  RECENT DECISIONS")
    print(f"  {'─' * 40}")
    for d in sorted(active, key=lambda x: x.date or date.min, reverse=True)[:5]:
        print(f"  [{fmt_date(d.date)}] {d.title}")
        print(f"    Owner: {d.owner or '—'}  |  Deadline: {fmt_date(d.deadline)}")
        open_count = sum(1 for a in d.action_items if not a.completed)
        if open_count:
            print(f"    Open actions: {open_count}")


def report_overdue(decisions: list[Decision]):
    print_section("OVERDUE ACTION ITEMS")
    found = False
    for d in sorted(decisions, key=lambda x: x.date or date.min, reverse=True):
        overdue = [a for a in d.action_items if a.is_overdue()]
        if not overdue:
            continue
        found = True
        print(f"\n  📋 {d.title}  [{fmt_date(d.date)}]")
        for a in overdue:
            print(f"    ⚠️  {a.text}")
            print(f"       Owner: {a.owner or '—'}  |  Due: {fmt_date(a.due)}{fmt_delta(a.due)}")
    if not found:
        print("\n  ✅ No overdue items.")


def report_due_within(decisions: list[Decision], days: int):
    print_section(f"ACTION ITEMS DUE WITHIN {days} DAYS")
    found = False
    for d in sorted(decisions, key=lambda x: x.date or date.min, reverse=True):
        upcoming = [a for a in d.action_items if a.is_due_within(days)]
        if not upcoming:
            continue
        found = True
        print(f"\n  📋 {d.title}  [{fmt_date(d.date)}]")
        for a in upcoming:
            print(f"    • {a.text}")
            print(f"      Owner: {a.owner or '—'}  |  Due: {fmt_date(a.due)}{fmt_delta(a.due)}")
    if not found:
        print(f"\n  ✅ Nothing due in the next {days} days.")


def report_by_owner(decisions: list[Decision], owner: str):
    print_section(f"ACTION ITEMS — OWNER: {owner.upper()}")
    found = False
    for d in sorted(decisions, key=lambda x: x.date or date.min, reverse=True):
        items = [a for a in d.action_items
                 if a.owner.lower() == owner.lower() and not a.completed]
        if not items:
            continue
        found = True
        print(f"\n  📋 {d.title}  [{fmt_date(d.date)}]")
        for a in items:
            flag = "⚠️ OVERDUE" if a.is_overdue() else ""
            print(f"    {'[ ]'} {a.text}  {flag}")
            print(f"      Due: {fmt_date(a.due)}{fmt_delta(a.due)}")
    if not found:
        print(f"\n  No open action items for '{owner}'.")


def report_search(decisions: list[Decision], query: str):
    print_section(f"SEARCH: \"{query}\"")
    q = query.lower()
    found = False
    for d in decisions:
        hit_fields = []
        if q in d.title.lower():
            hit_fields.append("title")
        if q in d.decision.lower():
            hit_fields.append("decision")
        if q in d.rationale.lower():
            hit_fields.append("rationale")
        if any(q in r.lower() for r in d.rejected):
            hit_fields.append("rejected")
        if hit_fields:
            found = True
            print(f"\n  [{fmt_date(d.date)}] {d.title}  (match: {', '.join(hit_fields)})")
            if "decision" in hit_fields:
                print(f"    → {d.decision}")
            if "rejected" in hit_fields:
                matches = [r for r in d.rejected if q in r.lower()]
                for r in matches:
                    print(f"    ✗ [REJECTED] {r}")
    if not found:
        print(f"\n  No results for '{query}'.")


def report_conflicts(decisions: list[Decision]):
    """
    Simple conflict detection: look for decisions on the same topic
    (matching title words) that are both active and have different decisions.
    Also flag if a rejected item appears as a new decision.
    """
    print_section("CONFLICT DETECTION")
    conflicts_found = False

    # Check for DO_NOT_RESURFACE violations
    all_rejected_texts = []
    for d in decisions:
        for r in d.rejected:
            clean = re.sub(r"\[DO_NOT_RESURFACE\]", "", r).strip().lower()
            all_rejected_texts.append((clean, d.date, d.title))

    active = [d for d in decisions if d.is_active()]
    for d in active:
        decision_lower = d.decision.lower()
        for rejected_text, rejected_date, rejected_title in all_rejected_texts:
            if rejected_text and rejected_text in decision_lower:
                conflicts_found = True
                print(f"\n  🚫 POTENTIAL DO_NOT_RESURFACE VIOLATION")
                print(f"    Decision [{fmt_date(d.date)}]: {d.decision}")
                print(f"    Matches rejected item from [{fmt_date(rejected_date)}] ({rejected_title}):")
                print(f"    \"{rejected_text}\"")

    # Check for same-topic contradictions (shared keywords in title)
    stop_words = {"the", "a", "an", "and", "or", "to", "for", "of", "in", "on", "with", "vs"}
    for i, d1 in enumerate(active):
        words1 = set(w.lower() for w in d1.title.split() if w.lower() not in stop_words)
        for d2 in active[i+1:]:
            words2 = set(w.lower() for w in d2.title.split() if w.lower() not in stop_words)
            overlap = words1 & words2
            if len(overlap) >= 2 and d1.decision and d2.decision:
                # Different decisions on similar topic
                if d1.decision.lower() != d2.decision.lower():
                    conflicts_found = True
                    print(f"\n  ⚠️  POTENTIAL CONFLICT (shared topic: {overlap})")
                    print(f"    [{fmt_date(d1.date)}] {d1.title}")
                    print(f"    Decision: {d1.decision}")
                    print(f"    [{fmt_date(d2.date)}] {d2.title}")
                    print(f"    Decision: {d2.decision}")
                    if d1.superseded_by or d2.superseded_by:
                        print(f"    ℹ️  One may supersede the other — check Superseded by fields.")

    if not conflicts_found:
        print("\n  ✅ No conflicts detected.")


# ─────────────────────────────────────────────
# Sample data for --demo mode
# ─────────────────────────────────────────────

SAMPLE_DECISIONS_MD = f"""# Board Meeting Decisions — Layer 2

This file contains ONLY founder-approved decisions.

---

## 2026-02-15 — Spain Market Expansion

**Decision:** Expand to Spain in Q3 2026 with a pilot in Madrid and Barcelona.
**Owner:** CMO
**Deadline:** 2026-03-01
**Review:** 2026-04-01
**Rationale:** Market research shows 40% lower CAC than Germany. Two pilot customers already committed.

**User Override:** Founder reduced pilot scope from 5 cities to 2. Reason: reduce operational risk during expansion.

**Rejected:**
- Launch in all of Spain simultaneously — too resource-intensive at current headcount [DO_NOT_RESURFACE]
- Partner with a local distributor instead of direct sales — margins too low [DO_NOT_RESURFACE]

**Action Items:**
- [x] Hire Spanish-speaking CSM — Owner: CHRO — Completed: 2026-02-28 — Result: Hired Maria G., starts March 10
- [ ] Finalize Madrid pilot customer contracts — Owner: CRO — Due: {(date.today() - timedelta(days=3)).strftime('%Y-%m-%d')} — Review: 2026-04-01
- [ ] Translate app to Spanish (ES-ES) — Owner: CTO — Due: {(date.today() + timedelta(days=5)).strftime('%Y-%m-%d')} — Review: 2026-04-15

**Supersedes:** 
**Superseded by:** 
**Raw transcript:** ~/.claude/decisions/raw/2026-02-15-pricing-tier-restructure.md

---

## 2026-02-28 — Pricing Strategy Revision

**Decision:** Move from per-seat to usage-based pricing effective Q2 2026.
**Owner:** CFO
**Deadline:** 2026-03-20
**Review:** 2026-05-01
**Rationale:** Usage-based aligns with customer value. Three enterprise customers requested it explicitly.

**User Override:** 

**Rejected:**
- Freemium tier — not appropriate for enterprise healthcare segment [DO_NOT_RESURFACE]
- Raise prices 30% across the board — too aggressive without usage data [DO_NOT_RESURFACE]

**Action Items:**
- [ ] Model 3 pricing scenarios (conservative/base/aggressive) — Owner: CFO — Due: {(date.today() - timedelta(days=1)).strftime('%Y-%m-%d')} — Review: 2026-03-25
- [ ] Customer interviews on usage patterns (n=10) — Owner: CMO — Due: {(date.today() + timedelta(days=10)).strftime('%Y-%m-%d')} — Review: 2026-04-01
- [ ] Update billing infrastructure for usage tracking — Owner: CTO — Due: 2026-04-01 — Review: 2026-04-15

**Supersedes:** 
**Superseded by:** 
**Raw transcript:** ~/.claude/decisions/raw/2026-02-28-enterprise-sales-hire.md

---

## 2026-03-04 — Engineering Hiring Plan Q2

**Decision:** Hire 2 senior engineers in Q2: one ML/AI, one backend. No contractors.
**Owner:** CTO
**Deadline:** 2026-04-15
**Review:** 2026-05-01
**Rationale:** ML roadmap blocked. Backend capacity at 85%. Contractors rejected due to IP risk in regulated domain.

**User Override:** Founder added: "ML hire must have healthcare AI experience. Non-negotiable."

**Rejected:**
- Contract team of 5 for 3 months — IP risk in regulated domain [DO_NOT_RESURFACE]
- Hire junior engineers to save budget — wrong tradeoff at this stage [DO_NOT_RESURFACE]

**Action Items:**
- [ ] Post ML engineer JD — Owner: CHRO — Due: {(date.today() + timedelta(days=2)).strftime('%Y-%m-%d')} — Review: 2026-03-20
- [ ] Post backend engineer JD — Owner: CHRO — Due: {(date.today() + timedelta(days=2)).strftime('%Y-%m-%d')} — Review: 2026-03-20
- [ ] Define ML role requirements with healthcare AI spec — Owner: CTO — Due: {(date.today() + timedelta(days=1)).strftime('%Y-%m-%d')} — Review: 2026-03-15

**Supersedes:** 
**Superseded by:** 
**Raw transcript:** ~/.claude/decisions/raw/2026-03-04-eu-expansion.md
"""


# ─────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────

def load_decisions(decisions_path: Path, demo: bool) -> list[Decision]:
    if demo:
        content = SAMPLE_DECISIONS_MD
    elif decisions_path.exists():
        content = decisions_path.read_text(encoding="utf-8")
    else:
        print(f"  ⚠️  decisions.md not found at: {decisions_path}")
        print(f"  Run with --demo to see sample output.")
        print(f"  To initialize: mkdir -p ~/.claude/decisions/approved && touch ~/.claude/decisions/approved/decisions.md")
        sys.exit(1)
    return parse_decisions(content)


def main():
    parser = argparse.ArgumentParser(
        description="Board Meeting Decision Tracker",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--file", default=os.path.expanduser("~/.claude/decisions/approved/decisions.md"),
                        help="Path to decisions.md (default: ~/.claude/decisions/approved/decisions.md)")
    parser.add_argument("--demo", action="store_true",
                        help="Run with built-in sample data (no file needed)")
    parser.add_argument("--summary", action="store_true",
                        help="Show overview: counts, overdue, recent decisions")
    parser.add_argument("--overdue", action="store_true",
                        help="List all overdue action items")
    parser.add_argument("--due-within", type=int, metavar="DAYS",
                        help="List items due within N days")
    parser.add_argument("--owner", metavar="ROLE",
                        help="Filter action items by owner")
    parser.add_argument("--search", metavar="QUERY",
                        help="Search decisions and rejected proposals")
    parser.add_argument("--conflicts", action="store_true",
                        help="Check for contradictory decisions or DO_NOT_RESURFACE violations")
    parser.add_argument("--all", action="store_true",
                        help="Show all decisions (summary format)")

    args = parser.parse_args()

    if not any([args.summary, args.overdue, args.due_within, args.owner,
                args.search, args.conflicts, getattr(args, "all")]):
        args.summary = True  # Default action

    decisions_path = Path(args.file)
    decisions = load_decisions(decisions_path, args.demo)

    if not decisions:
        print("  No decisions found in decisions.md.")
        sys.exit(0)

    if args.demo:
        print(f"\n  🎯 DEMO MODE — using built-in sample data ({len(decisions)} decisions)")

    if args.summary:
        report_summary(decisions)

    if args.overdue:
        report_overdue(decisions)

    if args.due_within:
        report_due_within(decisions, args.due_within)

    if args.owner:
        report_by_owner(decisions, args.owner)

    if args.search:
        report_search(decisions, args.search)

    if args.conflicts:
        report_conflicts(decisions)

    if getattr(args, "all"):
        print_section(f"ALL DECISIONS ({len(decisions)} total)")
        for d in sorted(decisions, key=lambda x: x.date or date.min, reverse=True):
            status = "📦 SUPERSEDED" if not d.is_active() else ""
            override = "  [OVERRIDE]" if d.has_override() else ""
            print(f"\n  [{fmt_date(d.date)}] {d.title} {status}{override}")
            print(f"    Decision: {d.decision}")
            print(f"    Owner: {d.owner or '—'}  |  Deadline: {fmt_date(d.deadline)}")
            open_actions = [a for a in d.action_items if not a.completed]
            if open_actions:
                print(f"    Open actions: {len(open_actions)}")

    print()


if __name__ == "__main__":
    main()
