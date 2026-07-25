# andreessen (skill)

Market-first decision & productivity skill in Marc Andreessen's mold. This is the inner skill
package; see the [plugin README](../../README.md) for the full overview and install notes.

## What it does

- **Pressure-tests a bet** (venture / idea / feature / career move) and issues a hard verdict:
  `BUILD-POUR-FUEL` / `MARKET-FIRST-DERISK` / `KILL-OR-REPICK-MARKET`.
- **Checks product/market fit**: `BEFORE-PMF` / `APPROACHING-PMF` / `AFTER-PMF`.
- **Runs the daily routine**: the 3x5 card (front capped at 3-5 must-dos) + the Anti-Todo log.

It runs on a fixed anti-sycophancy operating prompt (counterargument first, no premise validation,
no disclaimers, explicit confidence levels, no capitulation) preserved verbatim in
[`references/operating_prompt.md`](references/operating_prompt.md).

## Usage

```bash
# Should I build this? (market weighted 0.55; sub-4 market is a hard kill gate)
python scripts/market_first_evaluator.py --size 8 --growth 7 --timing 9 --pull 8 --team 6 --product 5

# Are we at product/market fit? (Sean Ellis 40% gate + 4 qualitative signals)
python scripts/pmf_signal_scorer.py --ellis-pct 45 --retention 8 --organic 7 --demand 8 --frequency 7

# Daily 3x5 card + Anti-Todo
python scripts/anti_todo_card.py --new --must-do "Call 5 churned users" "Ship retention dashboard" "Cut onboarding to 3 steps"
python scripts/anti_todo_card.py --did "Unblocked the data pipeline"
python scripts/anti_todo_card.py --summary

# Every script supports --sample and --output-format json
```

## Layout

| Path | Purpose |
|---|---|
| `SKILL.md` | Master workflow, forcing-question library, hard rules |
| `scripts/market_first_evaluator.py` | Market > team > product; sub-4 market = hard kill gate |
| `scripts/pmf_signal_scorer.py` | PMF felt-signals + Sean Ellis 40% gate |
| `scripts/anti_todo_card.py` | 3x5 card (front 3-5) + Anti-Todo log (back) |
| `references/operating_prompt.md` | Verbatim operating prompt + posture mapping (5 sources) |
| `references/market_first_canon.md` | "The Only Thing That Matters" (7 sources) |
| `references/pmf_and_build_canon.md` | PMF phases, Ellis 40%, "It's Time to Build" (7 sources) |
| `references/personal_productivity_system.md` | 3x5 card + Anti-Todo + scheduling reversal (7 sources) |
| `assets/example_3x5_card.md` | Worked 3x5-card example |

## Attribution

The operating prompt is user-supplied and preserved verbatim. Frameworks are Marc Andreessen's,
cited with explicit confidence levels in the references. Inspired-by skill; **not affiliated with
or endorsed by Marc Andreessen or a16z.**

---

**Version:** 2.9.0 · **License:** MIT
