#!/usr/bin/env python3
"""term_sheet_analyzer.py — Score a term sheet on founder-friendliness.

Stdlib-only. Computes a 0-100 score across 12 dimensions and flags
hostile clauses. Outputs human-readable or JSON.

NOT legal advice — surfaces questions for venture / securities counsel.

Input schema (JSON):
{
  "round": "Series A",
  "pre_money": 30000000,
  "raise_amount": 8000000,
  "liquidation_preference": {
    "multiple": 1.0,
    "participating": false,
    "cap": null
  },
  "anti_dilution": "broad_based_weighted_average",  // | "narrow_based_weighted_average" | "full_ratchet" | "none"
  "option_pool": {
    "size_pct": 12.0,
    "pre_money": true
  },
  "board_composition": {
    "investor_seats": 1,
    "founder_seats": 2,
    "independent_seats": 1
  },
  "vesting": {
    "standard_years": 4,
    "cliff_months": 12,
    "single_trigger_acceleration": false,
    "double_trigger_acceleration": true
  },
  "pro_rata": true,
  "drag_along": {
    "exists": true,
    "founder_consent_required": true
  },
  "protective_provisions": "standard",  // | "standard" | "aggressive"
  "information_rights": "standard",     // | "standard" | "aggressive"
  "dividends": "none"                   // | "none" | "non_cumulative_when_declared" | "cumulative"
}

Usage:
    python term_sheet_analyzer.py                            # uses embedded sample
    python term_sheet_analyzer.py path/to/term_sheet.json
    python term_sheet_analyzer.py term_sheet.json --output json
    python term_sheet_analyzer.py --help
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Tuple


SAMPLE = {
    "round": "Series A",
    "pre_money": 30_000_000,
    "raise_amount": 8_000_000,
    "liquidation_preference": {"multiple": 1.0, "participating": False, "cap": None},
    "anti_dilution": "broad_based_weighted_average",
    "option_pool": {"size_pct": 12.0, "pre_money": True},
    "board_composition": {"investor_seats": 1, "founder_seats": 2, "independent_seats": 1},
    "vesting": {
        "standard_years": 4,
        "cliff_months": 12,
        "single_trigger_acceleration": False,
        "double_trigger_acceleration": True,
    },
    "pro_rata": True,
    "drag_along": {"exists": True, "founder_consent_required": True},
    "protective_provisions": "standard",
    "information_rights": "standard",
    "dividends": "none",
}


def score(ts: Dict[str, Any]) -> Tuple[int, List[Dict[str, Any]]]:
    """Returns (total_score_0_to_100, list_of_findings).

    Each dimension is scored 0-100, then averaged. Findings list contains
    per-clause analysis with severity.
    """
    findings: List[Dict[str, Any]] = []
    scores: List[int] = []

    # --- 1. Liquidation Preference (high signal) ---
    lp = ts.get("liquidation_preference", {})
    lp_mult = lp.get("multiple", 1.0)
    lp_part = lp.get("participating", False)
    lp_cap = lp.get("cap")
    if lp_mult == 1.0 and not lp_part:
        lp_score = 100
        findings.append(_ok("liquidation_preference", "1x non-participating — founder-friendly standard."))
    elif lp_mult == 1.0 and lp_part and lp_cap and lp_cap <= 3:
        lp_score = 55
        findings.append(_warn("liquidation_preference",
            f"1x participating with {lp_cap}x cap. Investor double-dips up to cap. "
            "Push for non-participating; if accepted, accept cap < 3x."))
    elif lp_mult == 1.0 and lp_part and not lp_cap:
        lp_score = 25
        findings.append(_crit("liquidation_preference",
            "1x PARTICIPATING UNCAPPED. Investor gets their money back AND a pro-rata share of remaining proceeds, "
            "forever. Hostile. Push to non-participating or at minimum cap at 2x."))
    elif lp_mult > 1.0:
        lp_score = 10
        findings.append(_crit("liquidation_preference",
            f"{lp_mult}x preference. Investor gets {lp_mult}x their money back before founders see a dollar. "
            "Hostile; only acceptable in distressed rounds."))
    else:
        lp_score = 80
        findings.append(_ok("liquidation_preference", f"{lp_mult}x configuration acceptable."))
    scores.append(lp_score)

    # --- 2. Anti-Dilution ---
    ad = ts.get("anti_dilution", "broad_based_weighted_average")
    if ad == "broad_based_weighted_average":
        ad_score = 100
        findings.append(_ok("anti_dilution", "Broad-based weighted average — founder-friendly standard."))
    elif ad == "narrow_based_weighted_average":
        ad_score = 70
        findings.append(_warn("anti_dilution",
            "Narrow-based weighted average. More dilutive to founders than broad-based in a down round. "
            "Push to broad-based."))
    elif ad == "full_ratchet":
        ad_score = 10
        findings.append(_crit("anti_dilution",
            "FULL RATCHET. In a down round, investor's price is reset to the new round price entirely, "
            "massively diluting founders. Hostile; reject."))
    elif ad == "none":
        ad_score = 100
        findings.append(_ok("anti_dilution", "No anti-dilution provision. Unusual but founder-friendly."))
    else:
        ad_score = 50
        findings.append(_warn("anti_dilution", f"Unrecognized anti-dilution type: {ad}. Verify with counsel."))
    scores.append(ad_score)

    # --- 3. Option Pool (pre-money vs post-money) ---
    op = ts.get("option_pool", {})
    op_pre = op.get("pre_money", True)
    op_size = op.get("size_pct", 10.0)
    if not op_pre:
        op_score = 100
        findings.append(_ok("option_pool",
            f"Pool of {op_size}% sits post-money — dilutes all shareholders proportionally."))
    elif op_pre and op_size <= 10.0:
        op_score = 70
        findings.append(_warn("option_pool",
            f"Pool of {op_size}% pre-money — comes out of founders' shares. Reasonable size, but consider "
            "negotiating post-money or sharing the pool top-up across the round."))
    elif op_pre and op_size > 10.0:
        op_score = 30
        findings.append(_crit("option_pool",
            f"Pool of {op_size}% PRE-MONEY. This is the 'option pool shuffle' — typically reduces pre-money "
            f"by ~{op_size}%, diluting founders silently. Negotiate hard: justify the size with a hiring plan "
            "or push for post-money."))
    else:
        op_score = 60
        findings.append(_warn("option_pool", "Option pool structure unclear; verify."))
    scores.append(op_score)

    # --- 4. Board Composition ---
    bc = ts.get("board_composition", {})
    inv = bc.get("investor_seats", 0)
    fnd = bc.get("founder_seats", 0)
    ind = bc.get("independent_seats", 0)
    total = inv + fnd + ind
    if total == 0:
        bc_score = 50
        findings.append(_warn("board_composition", "Board composition unspecified."))
    elif fnd > inv and ind >= 1:
        bc_score = 100
        findings.append(_ok("board_composition",
            f"{fnd} founder / {inv} investor / {ind} independent — founder-friendly; founders retain control "
            "with independent tie-breaker."))
    elif fnd == inv and ind >= 1:
        bc_score = 75
        findings.append(_ok("board_composition",
            f"{fnd} founder / {inv} investor / {ind} independent — balanced, independent is critical."))
    elif inv > fnd:
        bc_score = 30
        findings.append(_crit("board_composition",
            f"{fnd} founder / {inv} investor / {ind} independent — investors control the board at Series A. "
            "This is unusually early; investor control typically arrives at Series B or later."))
    else:
        bc_score = 50
        findings.append(_warn("board_composition", f"Composition: {fnd}F/{inv}I/{ind}Ind — verify with counsel."))
    scores.append(bc_score)

    # --- 5. Vesting & Acceleration ---
    vest = ts.get("vesting", {})
    years = vest.get("standard_years", 4)
    cliff = vest.get("cliff_months", 12)
    single = vest.get("single_trigger_acceleration", False)
    double = vest.get("double_trigger_acceleration", False)
    if years == 4 and cliff == 12 and double and not single:
        vest_score = 100
        findings.append(_ok("vesting",
            "4yr/1yr cliff with double-trigger acceleration — founder-friendly standard. "
            "Single-trigger is rare and not recommended by counsel."))
    elif years == 4 and cliff == 12 and not double:
        vest_score = 60
        findings.append(_warn("vesting",
            "4yr/1yr cliff WITHOUT acceleration. Push for double-trigger (change of control + termination "
            "without cause) to protect founder upside in acquisition scenarios."))
    elif years > 4:
        vest_score = 20
        findings.append(_crit("vesting",
            f"{years}-year vesting. Non-standard; reject. 4 years is industry norm."))
    else:
        vest_score = 70
        findings.append(_warn("vesting", f"{years}yr/{cliff}mo cliff — verify acceleration with counsel."))
    scores.append(vest_score)

    # --- 6. Pro-Rata Rights ---
    if ts.get("pro_rata", True):
        pr_score = 100
        findings.append(_ok("pro_rata", "Pro-rata rights — standard for the lead and major investors."))
    else:
        pr_score = 60
        findings.append(_warn("pro_rata",
            "No pro-rata rights. Unusual; if investor is offering this, ask why (signals weak conviction "
            "or competitive pressure). Pro-rata is generally fine for founders to grant."))
    scores.append(pr_score)

    # --- 7. Drag-Along ---
    drag = ts.get("drag_along", {})
    if drag.get("exists") and drag.get("founder_consent_required"):
        drag_score = 100
        findings.append(_ok("drag_along",
            "Drag-along exists but requires founder consent — balanced."))
    elif drag.get("exists") and not drag.get("founder_consent_required"):
        drag_score = 40
        findings.append(_crit("drag_along",
            "Drag-along WITHOUT founder consent. Investors can force a sale over founder objection. "
            "Push for founder consent OR a minimum price threshold (e.g., 3x preference) to trigger drag."))
    else:
        drag_score = 80
        findings.append(_ok("drag_along", "No drag-along — neutral; common at early stages."))
    scores.append(drag_score)

    # --- 8. Protective Provisions ---
    pp = ts.get("protective_provisions", "standard")
    if pp == "standard":
        pp_score = 100
        findings.append(_ok("protective_provisions",
            "Standard protective provisions (NVCA model) — acceptable."))
    elif pp == "aggressive":
        pp_score = 40
        findings.append(_crit("protective_provisions",
            "Aggressive protective provisions can require investor consent for routine operating "
            "decisions (hiring execs, budget changes, vendor contracts). Push back to NVCA standard."))
    else:
        pp_score = 70
        findings.append(_warn("protective_provisions", f"Verify scope with counsel: {pp}"))
    scores.append(pp_score)

    # --- 9. Information Rights ---
    ir = ts.get("information_rights", "standard")
    if ir == "standard":
        ir_score = 100
        findings.append(_ok("information_rights",
            "Standard information rights (quarterly financials, annual audited, budget) — acceptable."))
    elif ir == "aggressive":
        ir_score = 60
        findings.append(_warn("information_rights",
            "Aggressive information rights (monthly financials, board observer rights, inspection rights). "
            "Reasonable for lead at Series B+; at Series A, push to quarterly."))
    else:
        ir_score = 75
        findings.append(_warn("information_rights", f"Verify: {ir}"))
    scores.append(ir_score)

    # --- 10. Dividends ---
    div = ts.get("dividends", "none")
    if div == "none":
        div_score = 100
        findings.append(_ok("dividends", "No dividend obligation — founder-friendly standard."))
    elif div == "non_cumulative_when_declared":
        div_score = 80
        findings.append(_ok("dividends",
            "Non-cumulative when-declared dividends — acceptable; rare to actually be paid."))
    elif div == "cumulative":
        div_score = 30
        findings.append(_crit("dividends",
            "CUMULATIVE dividends accrue every year regardless of declaration and must be paid at exit. "
            "Hostile; push to non-cumulative or none."))
    else:
        div_score = 60
        findings.append(_warn("dividends", f"Verify dividend type: {div}"))
    scores.append(div_score)

    # --- 11. Valuation Sanity ---
    pre = ts.get("pre_money", 0)
    raise_amt = ts.get("raise_amount", 0)
    if pre and raise_amt:
        post = pre + raise_amt
        dilution = (raise_amt / post) * 100
        if dilution > 30:
            val_score = 40
            findings.append(_crit("valuation",
                f"Round dilutes {dilution:.1f}% (raise ${raise_amt:,} on ${pre:,} pre = ${post:,} post). "
                "Over 30% in a single round is heavy; standard is 15-25%."))
        elif dilution > 25:
            val_score = 70
            findings.append(_warn("valuation",
                f"Round dilutes {dilution:.1f}%. Acceptable but on the high end. Standard 15-25%."))
        else:
            val_score = 100
            findings.append(_ok("valuation",
                f"Round dilutes {dilution:.1f}% — within standard 15-25% range."))
        scores.append(val_score)

    # --- 12. Holistic posture ---
    crit_count = sum(1 for f in findings if f["severity"] == "CRITICAL")
    if crit_count >= 3:
        findings.append(_crit("holistic",
            f"{crit_count} CRITICAL flags. This is a hostile term sheet. Either renegotiate the worst clauses "
            "or walk. Do not sign as-is."))
    elif crit_count >= 1:
        findings.append(_warn("holistic",
            f"{crit_count} CRITICAL flag(s). Address before signing; the rest is negotiable but not "
            "disqualifying."))
    else:
        findings.append(_ok("holistic", "No critical flags. Standard founder-friendly term sheet."))

    total_score = round(sum(scores) / len(scores)) if scores else 0
    return total_score, findings


def _ok(clause: str, msg: str) -> Dict[str, Any]:
    return {"clause": clause, "severity": "OK", "message": msg}

def _warn(clause: str, msg: str) -> Dict[str, Any]:
    return {"clause": clause, "severity": "WARN", "message": msg}

def _crit(clause: str, msg: str) -> Dict[str, Any]:
    return {"clause": clause, "severity": "CRITICAL", "message": msg}


def render_text(score_val: int, findings: List[Dict[str, Any]], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("TERM SHEET ANALYSIS")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    grade = (
        "🟢 FOUNDER-FRIENDLY" if score_val >= 85 else
        "🟡 NEGOTIATE"          if score_val >= 65 else
        "🔴 HOSTILE"
    )
    lines.append(f"Founder-friendliness score: {score_val}/100   {grade}")
    lines.append("")
    lines.append("-" * 72)

    for f in findings:
        sev = f["severity"]
        marker = {"OK": "✅", "WARN": "⚠️ ", "CRITICAL": "🚨"}.get(sev, "•")
        lines.append(f"{marker} [{sev:>8}] {f['clause']}")
        lines.append(f"           {f['message']}")
        lines.append("")

    lines.append("-" * 72)
    lines.append("REMINDER: This tool is not legal advice. Always engage venture / securities counsel.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Score a term sheet on founder-friendliness across 12 dimensions.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to term sheet JSON file (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                ts = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        ts = SAMPLE
        source = "<embedded sample Series A term sheet>"

    score_val, findings = score(ts)

    if args.output == "json":
        print(json.dumps({
            "source": source,
            "score": score_val,
            "grade": "FOUNDER_FRIENDLY" if score_val >= 85 else "NEGOTIATE" if score_val >= 65 else "HOSTILE",
            "findings": findings,
        }, indent=2))
    else:
        print(render_text(score_val, findings, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
