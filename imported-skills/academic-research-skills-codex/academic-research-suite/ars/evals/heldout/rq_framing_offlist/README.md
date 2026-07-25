# RQ Framing Held-Out Set (off-list shells vs the runtime LLM judge)

Issue: #501 Part 2. Direction from the PR #468 review thread (@brycewang-stanford).

This directory holds the **held-out measurement set** for the Socratic wording-pattern
advisory's **runtime judge** — the LLM applying the `## Wording-Pattern Advisory`
section of the two `socratic_mentor_agent.md` files. It is deliberately **outside**
`evals/gold/` because the judge is an LLM, not a script: it has no `target.entrypoint`,
`scripts/run_evals.py` must not discover it, and its ground-truth labels are not
reproducible by a shipped reducer (the `check_evals_gold_set` I9b invariant cannot
apply). The offline regex detector's calibration set lives at
`evals/gold/rq_framing_patterns/` and is a different measurement target.

## What "held-out" means here

Every `shell` item avoids (a) the twenty WP01–WP20 surface forms and (b) the four
off-list examples quoted inside the post-#503 advisory paragraph ("unpacking the
dynamics of…", "a deep dive into…", "rethinking X in the age of Y", "interrogating
the nexus between…") — those four are in the judge's prompt and are no longer
held out. The shipped regex detector (`scripts.check_rq_framing_patterns`) fires on
none of the **32 shell items**; the 12 generated candidates it did fire on were
excluded as on-list. Four `domain_native` negatives (`dn-003/006/009/019`)
intentionally DO contain listed surface substrings ("mediate the relationship
between…", "effect of X on task performance") inside fully specified designs — the
regex false-fires on them, while the LLM judge correctly stayed silent on all four
in every run. They are hard negatives by design, not a filtering oversight.

## Construction (2026-07-11)

1. **Natural generation.** Codex CLI 0.144.1 (`gpt-5.6-sol`) generated 80 research
   questions "the way you would naturally propose them to a graduate student",
   across ten fields, plus 20 specialist-style domain-native RQs. Cross-model
   generation avoids the judge's own model family authoring its test items.
2. **On-list filter.** The shipped regex detector removed 12 literal-surface-form
   matches. The remaining 68 are held out of the *listed surface forms* by
   construction.
3. **Dual annotation.** The 88 candidates were annotated independently by two
   models: the generator (`gpt-5.6-sol`, noun-swap rubric verbatim) and the
   maintainer-session agent (`claude-fable-5`). Seven disagreement/borderline items
   were dropped (`nat-041/050/052/055/056` name mechanisms or engineering artifacts;
   `nat-064/067` split between annotators). Only agreed labels shipped. Caveat:
   annotator 2 shares a model family with the measured judge (`claude-sonnet-5`);
   the cross-family generator annotation and the mechanical regex filter are the
   independence anchors.
4. **Elicited rewrites (label by construction + re-verification).** Two realistic
   de-cliché flows — "rewrite so it sounds less AI-cliché" (`el-*`) and "give my
   paper a catchy, ambitious title" (`ti-*`) — were run on agreed-shell sources with
   an explicit no-new-specifics constraint. Shell labels inherit from the sources,
   and annotator 2 additionally re-applied the noun-swap judgment to every rewrite
   (not only the no-new-specifics check); one borderline (`ti-005`, brushes the
   "concrete theoretical tension" exemption) was dropped at that step. These flows
   are how off-list shells arise in the wild: users asking an AI to polish an
   already-shell phrasing. **Construct note:** the `ti-*` items are title-form
   phrasings, not interrogative RQs — 8 of the 9 `off_list` shells. They are in
   scope for the advisory (the `academic-paper` twin covers thesis sentences and
   chapter framings, and users paste working titles as directions), but off-list
   conclusions from this set are specifically about decorated title-form shells.
5. **Final selection (enumerated manifest).** From the agreed pool: 15 natural
   family-variants picked by per-field round-robin (fields sorted alphabetically,
   items in id order; `random.seed(501)` for batch shuffling only), plus `nat-044`
   (the only agreed off-list natural); all 32 elicitation source items were excluded
   from the set to avoid near-duplicate pairs. The elicited/title/negative strata
   were picked by maintainer judgment for field spread — the exact selections are
   the manifest: `el-001/003/005/007/010/013/016/017` (8 of 18),
   `ti-001/002/004/007/008/010/012/013` (8 of 13 eligible, `ti-005` dropped as
   borderline), and negatives `nat-059` + `dn-*` all except `dn-004/010/015/017/020`
   (dropped to hit the 16-negative budget while keeping field spread). The committed
   `heldout_set.json` is the authoritative selection record. Selection happened
   before any judging run.
6. **Final set.** 32 shells (23 `family_variant` + 9 `off_list`) + 16 domain-native
   hard negatives = 48 items. `tier` is descriptive metadata; `label` is ground truth.

## Measurement protocol (re-run this for any future advisory change)

- Judge = an isolated LLM agent given ONLY the verbatim `## Wording-Pattern Advisory`
  section (the variant under test) + a batch of 6 items (4 shells + 2 negatives,
  shuffled), instructed to decide fire/silent per item independently. No repo access,
  no labels, no other context.
- 8 batches cover the 48 items once; run ≥2 replicates for the decision-relevant
  variant (single-run flips of 1–2 borderline items were observed).
- Metrics: miss rate (shells not fired on) overall and per tier; false-fire rate
  (negatives fired on). Acceptance line inherited from
  `evals/gold/rq_framing_patterns/manifest.yaml`: FNR < 0.30, FPR < 0.20.

## 2026-07-11 baseline result (see `measurement-2026-07-11.json`)

| variant | overall miss | family_variant | off_list | false-fire |
|---------|-------------|----------------|----------|------------|
| pre-#503 (single run) | 0.375 | 0.261 | 0.667 | 0.000 |
| post-#503 rep1 | 0.375 | 0.217 | 0.778 | 0.000 |
| post-#503 rep2 | 0.344 | 0.174 | 0.778 | 0.000 |

**Verdict: miss rate HIGH** (overall ≥ the 0.30 line). The gap is concentrated in
`off_list` decorated compound-title shells — the same 7 of 9 missed in both post
replicates — where the captured judge reasoning reads generic topical nouns
("cybersecurity training", "nurse workload") as the exemption's "specific
mechanism" (excerpts in `judge_reasoning_excerpts.md`; boolean outcomes in the
measurement JSON). Family-variant generalization is under the line (0.17–0.26),
and false-fire is zero on both variants: the conservative bar over-exempts rather
than over-warns. Per issue #501, this set is therefore the acceptance test for any
future advisory change. Judge model: `claude-sonnet-5`; both the set (English-only,
one generator model) and the judgments are model- and time-specific and drift
across versions — re-run rather than reuse the numbers.

Full write-up: `audits/rq-advisory-heldout-measurement-2026-07-11.md`.

## 2026-07-11 post-#505 result (see `measurement-2026-07-11-505.json`)

The #505 exemption sharpening (narrow named/operationalized-specific exemption +
decorated-compound-title rule; both `socratic_mentor_agent.md` files) was measured
against this set per the protocol above, in two rounds: round 1 on the initial
wording, then — after a cross-model review P2 refined the wording (generic
demographic descriptors excluded from "named population"; the decorated-title
rule extended to single-topic subtitles "X in/among Z") — a fresh 2-replicate
round on the FINAL shipped wording:

| variant | overall miss | family_variant | off_list | false-fire |
|---------|-------------|----------------|----------|------------|
| post-#505 round1 rep1 | 0.094 | 0.043 | 0.222 | 0.000 |
| post-#505 round1 rep2 | 0.094 | 0.087 | 0.111 | 0.000 |
| post-#505 FINAL rep1 | 0.094 | 0.000 | 0.333 | 0.000 |
| post-#505 FINAL rep2 | 0.094 | 0.130 | 0.000 | 0.000 |

**Verdict: PASS** — all four runs sit well under the FNR < 0.30 line and the
zero over-warning property (0/16 false-fire, including the four hard negatives
carrying listed surface substrings) holds in every run. The decorated-title
shape that carried the baseline gap (0.778) is now caught: FINAL rep2 fired on
all 9 off-list items; FINAL rep1's three off-list misses (`ti-002/004/007`)
trace to a single judge whose prose reasoning called the items swappable shells
but whose JSON verdicts said SILENT — the boolean record stands per protocol,
and the run still passes. No shell was missed in both FINAL replicates. All
#505 prompt example strings were substring-checked against every held-out item
before measurement (no hits), so the set remains held out of the in-prompt
examples. Full write-up:
`audits/rq-advisory-505-exemption-sharpening-2026-07-11.md`. The model/time-drift
caveat above applies unchanged — re-run, don't reuse.
