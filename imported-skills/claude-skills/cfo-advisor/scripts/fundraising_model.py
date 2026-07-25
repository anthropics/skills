#!/usr/bin/env python3
"""
Fundraising Model
==================
Cap table management, dilution modeling, and multi-round scenario planning.
Know exactly what you're giving up before you walk into any negotiation.

Covers:
  - Cap table state at each round
  - Dilution per shareholder per round
  - Option pool shuffle impact
  - Multi-round projections (Seed → A → B → C)
  - Return scenarios at different exit valuations

Usage:
    python fundraising_model.py
    python fundraising_model.py --exit 150  # model at $150M exit
    python fundraising_model.py --csv

Stdlib only. No dependencies.
"""

import argparse
import csv
import io
import sys
from dataclasses import dataclass, field
from typing import Optional


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class Shareholder:
    """A shareholder in the cap table."""
    name: str
    share_class: str        # "common", "preferred", "option"
    shares: float
    invested: float = 0.0   # total cash invested
    is_option_pool: bool = False


@dataclass
class RoundConfig:
    """Configuration for a financing round."""
    name: str                       # e.g. "Series A"
    pre_money_valuation: float
    investment_amount: float
    new_option_pool_pct: float = 0.0    # % of POST-money to allocate to new options
    option_pool_pre_round: bool = True  # True = pool created before round (dilutes founders)
    lead_investor_name: str = "New Investor"
    share_price_override: Optional[float] = None  # if None, computed from valuation


@dataclass
class CapTableEntry:
    """A row in the cap table at a point in time."""
    name: str
    share_class: str
    shares: float
    pct_ownership: float
    invested: float
    is_option_pool: bool = False


@dataclass
class RoundResult:
    """Snapshot of cap table after a round closes."""
    round_name: str
    pre_money_valuation: float
    investment_amount: float
    post_money_valuation: float
    price_per_share: float
    new_shares_issued: float
    option_pool_shares_created: float
    total_shares: float
    cap_table: list[CapTableEntry]


@dataclass
class ExitAnalysis:
    """Proceeds to each shareholder at an exit."""
    exit_valuation: float
    shareholder: str
    shares: float
    ownership_pct: float
    proceeds_common: float          # if all preferred converts to common
    invested: float
    moic: float                     # multiple on invested capital (for investors)


# ---------------------------------------------------------------------------
# Core cap table engine
# ---------------------------------------------------------------------------

class CapTable:
    """Manages a cap table through multiple rounds."""

    def __init__(self):
        self.shareholders: list[Shareholder] = []
        self._total_shares: float = 0.0

    def add_shareholder(self, sh: Shareholder) -> None:
        self.shareholders.append(sh)
        self._total_shares += sh.shares

    def total_shares(self) -> float:
        return sum(s.shares for s in self.shareholders)

    def snapshot(self, label: str = "") -> list[CapTableEntry]:
        total = self.total_shares()
        return [
            CapTableEntry(
                name=s.name,
                share_class=s.share_class,
                shares=s.shares,
                pct_ownership=s.shares / total if total > 0 else 0,
                invested=s.invested,
                is_option_pool=s.is_option_pool,
            )
            for s in self.shareholders
        ]

    def execute_round(self, config: RoundConfig) -> RoundResult:
        """
        Execute a financing round:
        1. (Optional) Create option pool pre-round (dilutes existing shareholders)
        2. Issue new shares to investor at round price
        Returns a RoundResult with full cap table snapshot.
        """
        current_total = self.total_shares()

        # Step 1: Option pool shuffle (if pre-round)
        option_pool_shares_created = 0.0
        if config.new_option_pool_pct > 0 and config.option_pool_pre_round:
            # Target: post-round option pool = new_option_pool_pct of total post-money shares
            # Solve: pool_shares / (current_total + pool_shares + new_investor_shares) = target_pct
            # This requires iteration because new_investor_shares also depends on pool_shares
            # Simplification: create pool based on post-round total (slightly approximated)
            target_post_round_pct = config.new_option_pool_pct
            post_money = config.pre_money_valuation + config.investment_amount

            # Estimate shares per dollar (price per share)
            price_per_share = config.pre_money_valuation / current_total
            new_investor_shares_estimate = config.investment_amount / price_per_share

            # Pool shares needed so that pool / total_post = target_pct
            total_post_estimate = current_total + new_investor_shares_estimate
            pool_shares_needed = (target_post_round_pct * total_post_estimate) / (1 - target_post_round_pct)

            # Check if existing pool is sufficient
            existing_pool = next(
                (s.shares for s in self.shareholders if s.is_option_pool), 0
            )
            additional_pool_needed = max(0, pool_shares_needed - existing_pool)

            if additional_pool_needed > 0:
                option_pool_shares_created = additional_pool_needed
                # Add to existing pool or create new
                pool_sh = next((s for s in self.shareholders if s.is_option_pool), None)
                if pool_sh:
                    pool_sh.shares += additional_pool_needed
                else:
                    self.shareholders.append(Shareholder(
                        name="Option Pool",
                        share_class="option",
                        shares=additional_pool_needed,
                        is_option_pool=True,
                    ))

        # Step 2: Price per share (after pool creation)
        current_total_post_pool = self.total_shares()
        if config.share_price_override:
            price_per_share = config.share_price_override
        else:
            price_per_share = config.pre_money_valuation / current_total_post_pool

        # Step 3: New shares for investor
        new_shares = config.investment_amount / price_per_share

        # Step 4: Add investor to cap table
        self.shareholders.append(Shareholder(
            name=config.lead_investor_name,
            share_class="preferred",
            shares=new_shares,
            invested=config.investment_amount,
        ))

        post_money = config.pre_money_valuation + config.investment_amount
        total_post = self.total_shares()

        return RoundResult(
            round_name=config.name,
            pre_money_valuation=config.pre_money_valuation,
            investment_amount=config.investment_amount,
            post_money_valuation=post_money,
            price_per_share=price_per_share,
            new_shares_issued=new_shares,
            option_pool_shares_created=option_pool_shares_created,
            total_shares=total_post,
            cap_table=self.snapshot(),
        )

    def analyze_exit(self, exit_valuation: float) -> list[ExitAnalysis]:
        """
        Simple exit analysis: all preferred converts to common, proceeds split pro-rata.
        (Does not model liquidation preferences — see fundraising_playbook.md for that.)
        """
        total = self.total_shares()
        price_per_share = exit_valuation / total
        results = []
        for s in self.shareholders:
            if s.is_option_pool:
                continue  # unissued options don't receive proceeds
            proceeds = s.shares * price_per_share
            moic = proceeds / s.invested if s.invested > 0 else 0.0
            results.append(ExitAnalysis(
                exit_valuation=exit_valuation,
                shareholder=s.name,
                shares=s.shares,
                ownership_pct=s.shares / total,
                proceeds_common=proceeds,
                invested=s.invested,
                moic=moic,
            ))
        return sorted(results, key=lambda x: x.proceeds_common, reverse=True)


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fmt(value: float, prefix: str = "$") -> str:
    if value == float("inf"):
        return "∞"
    if abs(value) >= 1_000_000:
        return f"{prefix}{value/1_000_000:.2f}M"
    if abs(value) >= 1_000:
        return f"{prefix}{value/1_000:.0f}K"
    return f"{prefix}{value:.2f}"


def print_round_result(result: RoundResult, prev_cap_table: Optional[list[CapTableEntry]] = None) -> None:
    print(f"\n{'='*70}")
    print(f"  {result.round_name.upper()}")
    print(f"{'='*70}")
    print(f"  Pre-money valuation:   {fmt(result.pre_money_valuation)}")
    print(f"  Investment:            {fmt(result.investment_amount)}")
    print(f"  Post-money valuation:  {fmt(result.post_money_valuation)}")
    print(f"  Price per share:       {fmt(result.price_per_share, '$')}")
    print(f"  New shares issued:     {result.new_shares_issued:,.0f}")
    if result.option_pool_shares_created > 0:
        print(f"  Option pool created:   {result.option_pool_shares_created:,.0f} shares")
        print(f"  ⚠️  Pool created pre-round: dilutes existing shareholders, not new investor")
    print(f"  Total shares post:     {result.total_shares:,.0f}")

    print(f"\n  {'Shareholder':<22} {'Shares':>12} {'Ownership':>10}  {'Invested':>10}  {'Δ Ownership':>12}")
    print("  " + "-"*68)

    prev_map = {e.name: e.pct_ownership for e in prev_cap_table} if prev_cap_table else {}

    for entry in result.cap_table:
        delta = ""
        if entry.name in prev_map:
            change = (entry.pct_ownership - prev_map[entry.name]) * 100
            delta = f"{change:+.1f}pp"
        elif not entry.is_option_pool:
            delta = "new"

        invested_str = fmt(entry.invested) if entry.invested > 0 else "-"
        print(
            f"  {entry.name:<22} {entry.shares:>12,.0f} "
            f"{entry.pct_ownership*100:>9.2f}%  {invested_str:>10}  {delta:>12}"
        )


def print_exit_analysis(results: list[ExitAnalysis], exit_valuation: float) -> None:
    print(f"\n{'='*70}")
    print(f"  EXIT ANALYSIS @ {fmt(exit_valuation)} (all preferred converts to common)")
    print(f"{'='*70}")
    print(f"\n  {'Shareholder':<22} {'Ownership':>10} {'Proceeds':>12} {'Invested':>10} {'MOIC':>8}")
    print("  " + "-"*65)
    for r in results:
        moic_str = f"{r.moic:.1f}x" if r.moic > 0 else "n/a"
        invested_str = fmt(r.invested) if r.invested > 0 else "-"
        print(
            f"  {r.shareholder:<22} {r.ownership_pct*100:>9.2f}% "
            f"{fmt(r.proceeds_common):>12} {invested_str:>10} {moic_str:>8}"
        )
    print(f"\n  Note: Does not model liquidation preferences.")
    print(f"  Participating preferred reduces founder proceeds in most real exits.")
    print(f"  See references/fundraising_playbook.md for full liquidation waterfall.")


def print_dilution_summary(rounds: list[RoundResult]) -> None:
    print(f"\n{'='*70}")
    print(f"  DILUTION SUMMARY — FOUNDER PERSPECTIVE")
    print(f"{'='*70}")

    # Find all founders (common shareholders who aren't investors or option pool)
    founder_names = []
    for entry in rounds[0].cap_table:
        if entry.share_class == "common" and not entry.is_option_pool:
            founder_names.append(entry.name)

    if not founder_names:
        print("  No common shareholders found in initial cap table.")
        return

    header = f"  {'Round':<16}" + "".join(f"  {n:<16}" for n in founder_names) + f"  {'Total Inv':>12}"
    print(header)
    print("  " + "-" * (16 + 18 * len(founder_names) + 14))

    for result in rounds:
        cap_map = {e.name: e for e in result.cap_table}
        total_invested = sum(e.invested for e in result.cap_table if not e.is_option_pool)
        row = f"  {result.round_name:<16}"
        for name in founder_names:
            pct = cap_map[name].pct_ownership * 100 if name in cap_map else 0
            row += f"  {pct:>6.2f}%         "
        row += f"  {fmt(total_invested):>12}"
        print(row)


def export_csv_rounds(rounds: list[RoundResult]) -> str:
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["Round", "Shareholder", "Share Class", "Shares", "Ownership Pct",
                     "Invested", "Pre Money", "Post Money", "Price Per Share"])
    for r in rounds:
        for entry in r.cap_table:
            writer.writerow([
                r.round_name, entry.name, entry.share_class,
                round(entry.shares, 0), round(entry.pct_ownership * 100, 4),
                round(entry.invested, 2), round(r.pre_money_valuation, 0),
                round(r.post_money_valuation, 0), round(r.price_per_share, 4),
            ])
    return buf.getvalue()


# ---------------------------------------------------------------------------
# Sample data: typical two-founder Series A/B/C startup
# ---------------------------------------------------------------------------

def build_sample_model() -> tuple[CapTable, list[RoundResult]]:
    """
    Sample company:
      - 2 founders, started with 10M shares each
      - 1M shares for early advisor
      - Raises Pre-seed → Seed → Series A → Series B → Series C
    """
    cap = CapTable()
    SHARES_PER_FOUNDER = 4_000_000
    SHARES_ADVISOR = 200_000

    # Founding state
    cap.add_shareholder(Shareholder("Founder A (CEO)", "common", SHARES_PER_FOUNDER))
    cap.add_shareholder(Shareholder("Founder B (CTO)", "common", SHARES_PER_FOUNDER))
    cap.add_shareholder(Shareholder("Advisor",         "common", SHARES_ADVISOR))

    rounds: list[RoundResult] = []
    prev_cap = cap.snapshot()

    # Round 1: Pre-seed — $500K at $4.5M pre, 10% option pool created
    r1 = cap.execute_round(RoundConfig(
        name="Pre-seed",
        pre_money_valuation=4_500_000,
        investment_amount=500_000,
        new_option_pool_pct=0.10,
        option_pool_pre_round=True,
        lead_investor_name="Angel Syndicate",
    ))
    rounds.append(r1)
    prev_r1 = r1.cap_table[:]

    # Round 2: Seed — $2M at $9M pre, expand option pool to 12%
    r2 = cap.execute_round(RoundConfig(
        name="Seed",
        pre_money_valuation=9_000_000,
        investment_amount=2_000_000,
        new_option_pool_pct=0.12,
        option_pool_pre_round=True,
        lead_investor_name="Seed Fund",
    ))
    rounds.append(r2)

    # Round 3: Series A — $12M at $38M pre, refresh option pool to 15%
    r3 = cap.execute_round(RoundConfig(
        name="Series A",
        pre_money_valuation=38_000_000,
        investment_amount=12_000_000,
        new_option_pool_pct=0.15,
        option_pool_pre_round=True,
        lead_investor_name="Series A Fund",
    ))
    rounds.append(r3)

    # Round 4: Series B — $25M at $95M pre, refresh pool to 12%
    r4 = cap.execute_round(RoundConfig(
        name="Series B",
        pre_money_valuation=95_000_000,
        investment_amount=25_000_000,
        new_option_pool_pct=0.12,
        option_pool_pre_round=True,
        lead_investor_name="Series B Fund",
    ))
    rounds.append(r4)

    # Round 5: Series C — $40M at $185M pre, refresh pool to 10%
    r5 = cap.execute_round(RoundConfig(
        name="Series C",
        pre_money_valuation=185_000_000,
        investment_amount=40_000_000,
        new_option_pool_pct=0.10,
        option_pool_pre_round=True,
        lead_investor_name="Series C Fund",
    ))
    rounds.append(r5)

    return cap, rounds


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Fundraising Model — Cap Table & Dilution")
    parser.add_argument("--exit", type=float, default=250.0,
                        help="Exit valuation in $M for return analysis (default: 250)")
    parser.add_argument("--csv", action="store_true", help="Export round data as CSV to stdout")
    args = parser.parse_args()

    exit_valuation = args.exit * 1_000_000

    print("\n" + "="*70)
    print("  FUNDRAISING MODEL — CAP TABLE & DILUTION ANALYSIS")
    print("  Sample Company: Two-founder SaaS startup")
    print("  Pre-seed → Seed → Series A → Series B → Series C")
    print("="*70)

    cap, rounds = build_sample_model()

    # Print each round
    prev = None
    for r in rounds:
        print_round_result(r, prev)
        prev = r.cap_table

    # Dilution summary table
    print_dilution_summary(rounds)

    # Exit analysis at specified valuation
    exit_results = cap.analyze_exit(exit_valuation)
    print_exit_analysis(exit_results, exit_valuation)

    # Also print at 2x and 5x for sensitivity
    print("\n  Exit Sensitivity — Founder A Proceeds:")
    print(f"  {'Exit Valuation':<20} {'Founder A %':>12} {'Founder A $':>14} {'MOIC':>8}")
    print("  " + "-"*56)
    for mult in [0.5, 1.0, 1.5, 2.0, 3.0, 5.0]:
        val = rounds[-1].post_money_valuation * mult
        ex = cap.analyze_exit(val)
        founder_a = next((r for r in ex if r.shareholder == "Founder A (CEO)"), None)
        if founder_a:
            print(f"  {fmt(val):<20} {founder_a.ownership_pct*100:>11.2f}% "
                  f"{fmt(founder_a.proceeds_common):>14}  {'n/a':>8}")

    print("\n  Key Takeaways:")
    final = rounds[-1].cap_table
    total = sum(e.shares for e in final)
    founder_a_final = next((e for e in final if e.name == "Founder A (CEO)"), None)
    if founder_a_final:
        print(f"    Founder A final ownership: {founder_a_final.pct_ownership*100:.2f}%")
    total_raised = sum(e.invested for e in final)
    print(f"    Total capital raised:      {fmt(total_raised)}")
    print(f"    Total shares outstanding:  {total:,.0f}")
    print(f"    Final post-money:          {fmt(rounds[-1].post_money_valuation)}")
    print("\n    Run with --exit <$M> to model proceeds at different exit valuations.")
    print("    Example: python fundraising_model.py --exit 500")

    if args.csv:
        print("\n\n--- CSV EXPORT ---\n")
        sys.stdout.write(export_csv_rounds(rounds))


if __name__ == "__main__":
    main()
