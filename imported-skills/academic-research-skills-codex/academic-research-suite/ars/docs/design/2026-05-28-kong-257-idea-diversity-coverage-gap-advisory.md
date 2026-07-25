# Kong #257 Idea Diversity / Coverage Gap Advisory

Issue: #257
Parent meta: #255
Related architecture boundary: #134 active conductor

## Problem

Two low-autonomy advisory surfaces are missing:

1. Socratic research-question formulation can accept generic wording shells such as "exploring the impact of X on Y" without showing the user that the phrasing itself is common and low-specificity.
2. Lit-review mode can fill topic gaps through `uncovered_topics` while still returning a source set concentrated in one period, site, method, or venue family.

Both signals are advisory. Neither should generate ideas, rank the user's idea, block output, or displace the scholar's choice.

## Socratic Wording Advisory

The two Socratic mentor agent copies now carry `## Wording-Pattern Advisory (Kong #257)`:

- `deep-research/agents/socratic_mentor_agent.md`
- `academic-paper/agents/socratic_mentor_agent.md`

The section defines 20 surface-pattern families (`WP01`-`WP20`) and the `WORDING_PATTERN_ADVISORY` output tag.

Important boundary:

- The check is on wording and framing only.
- The check is not a novelty judgment.
- The check does not rewrite the research question unless the user asks.
- The check asks one Socratic follow-up so the user can choose domain-native phrasing.

## Lit-Review Distributional Skew Advisory

The lit-review agents now carry `## Distributional Skew Advisory (Kong #257)` or the equivalent Step 4.6 section:

- `deep-research/agents/bibliography_agent.md`
- `academic-paper/agents/literature_strategist_agent.md`

The pass runs after retrieval/screening/deduplication and before final report emission. It extends the existing `uncovered_topics` / search-fills-gap machinery with four dimensions:

- time distribution
- geographic distribution
- methodological distribution
- venue tier distribution

Threshold: emit `DISTRIBUTIONAL_SKEW_ADVISORY` when a single known value accounts for `>= 70%` of known entries for that dimension. The denominator is `known_N` for the dimension, not total source count.

Important boundary:

- Missing metadata is not inferred.
- The advisory does not downgrade sources.
- The advisory does not block bibliography or literature-search output.
- The user can keep the skew when it matches the RQ.

## #134 Boundary

#134 active conductor is a routing and task-envelope layer: it decides what mode should run and how cross-phase work is dispatched. #257 is content-surface advisory:

- Conductor: "What mode should we be in?"
- Wording advisory: "Does this proposed RQ wording resemble an AI-typical shell?"
- Distributional skew advisory: "Does this retrieved corpus over-concentrate on one known distributional value?"

These can coexist. #257 does not add routing logic, autonomous search expansion, or deterministic PreToolUse enforcement. The relevant #134 design context is documented in `docs/design/2026-05-18-ars-v3.9.2-phase-boundary-spec.md#relation-to-134-v310-conductor`.

## Calibration

The repository includes a small hand-curated gold set for the Socratic wording advisory:

- `evals/gold/rq_framing_patterns/gold_set.json`
- `scripts/check_rq_framing_patterns.py`

Gold-set shape:

- 40 RQ framings
- 20 wording-cliche positives
- 20 domain-native negatives

Acceptance thresholds:

- FNR < 0.30
- FPR < 0.20
- balanced accuracy >= 0.75

The checker is intentionally lexical and conservative. It exists to prevent over-warning; the prompt-layer advisory remains scholar-facing and non-blocking.

## Example

`deep-research/examples/idea_diversity_coverage_gap_advisory.md` shows both advisory surfaces:

- `WORDING_PATTERN_ADVISORY` on an "impact of X on Y" RQ shell
- `DISTRIBUTIONAL_SKEW_ADVISORY` on a lit-review corpus concentrated in post-2023 NLP venues
