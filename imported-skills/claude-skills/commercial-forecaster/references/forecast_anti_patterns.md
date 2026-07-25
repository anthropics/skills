# Forecast Anti-Patterns

The cataloged failure modes of SaaS commercial forecasting. Source material behind the skill's
warnings, hard rules, and the forcing-question library.

## Core principle

**A forecast without a disclosed assumption block is theatre.** It cannot be evaluated, corrected,
or learned from. Theatre forecasts produce more variance against actuals than disclosed-assumption
forecasts by a factor of 2-3x (Bain commercial-forecasting practice; Forrester pipeline-coverage research).

Every anti-pattern below is a way of producing theatre — sometimes accidentally, sometimes
performatively.

---

## Anti-pattern catalog (≥ 8)

### 1. Single-number forecast with no confidence band

**Symptom:** the board slide says "$8.4M Q3 commit". That's it. No best-case, no pipe-only, no
assumption block.

**Why it fails:** the CFO cannot evaluate whether 8.4 is achievable, conservative, or aspirational
without knowing the dispersion. The forecast is unfalsifiable in advance and unaccountable in retrospect.

**Fix:** present three numbers (commit / best-case / pipe-only) AND the assumption block. Always.

**Canon:** McKinsey on forecast bias — single-number forecasts produce 2-3x higher variance against
actuals than 3-tier forecasts because they suppress disagreement.

### 2. Use last-12-quarter conversion blindly

**Symptom:** the conversion rate applied to each stage is the trailing 12-quarter average. It
hasn't been recomputed since 2024.

**Why it fails:** last-12Q smooths over regime change. If the last 4 quarters show a 10pp drop in
demo-to-proposal conversion (post-funding-correction sales drag, e.g.), the 12Q average will lag
that signal by 2-3 quarters. By the time it shows up, you've missed two forecasts.

**Fix:** blend 70% last-4Q + 30% last-12Q. Disclose the blend on the slide.

**Canon:** Tomasz Tunguz forecasting studies + MIT Sloan / Hyndman *Forecasting: Principles and
Practice* — blended windows outperform either window alone in regime-change environments.

### 3. Report NRR without cohort decomposition

**Symptom:** the QBR slide shows "NRR: 108%". One number. No cohort heatmap, no segment cut.

**Why it fails:** the consolidated NRR is an ARR-weighted average that can hide 5-15pp leaks in
recent cohorts. The leak surfaces in the consolidated number 2-3 quarters after it starts. By
then, the deal is done.

**Fix:** present NRR with the cohort heatmap + the leaky-cohort callout.

**Canon:** Patrick Campbell / ProfitWell + Brian Balfour (Reforge) — "if you can't tell me your
NRR by acquisition cohort, you don't know your NRR."

### 4. Treat best-case as commit

**Symptom:** the commit number quietly includes opps in proposal / negotiation stages weighted
optimistically. The number looks aggressive; the CFO challenges it; the CRO digs in.

**Why it fails:** commit is the number the CRO defends even when the quarter goes sideways. If
commit includes weighted-stage opps, the CRO will miss commit when the quarter does go sideways —
and credibility collapses.

**Fix:** commit = commit-grade stages only (verbal / contract-out / commit). Best-case is the
separate, optimistic number.

**Canon:** Bain commercial-forecasting practice + OpenView SaaS benchmarks — top-quartile teams
hit commit within 5%; bottom-quartile miss by 25%+, almost always because commit was conflated
with best-case.

### 5. Hide the assumption block

**Symptom:** the forecast is presented; someone asks "what conversion rate are you using?"; the
answer is "the historical one" or "trust me, it's calibrated".

**Why it fails:** the slide is now theatre. The forecast is unfalsifiable and unaccountable.

**Fix:** the assumption block is non-optional. It names (a) the conversion rate, (b) the data
window, (c) the weighting choice, (d) the pipeline-coverage ratio. The skill refuses to omit it;
if you remove it manually, you own the theatre.

**Canon:** Bain & Co + Forrester — undisclosed-assumption forecasts have 2.3x higher variance
against actuals than disclosed-assumption forecasts.

### 6. No leaky-cohort callout

**Symptom:** the cohort heatmap is presented, the recent cohort is visibly leaking 15pp, no one
calls it out. Everyone moves on to the next slide.

**Why it fails:** the leak doesn't go away because no one mentioned it. Two quarters later, the
consolidated NRR drops 8pp and the board is angry.

**Fix:** when `cohort_arr_projector.py` flags a cohort, the flag goes on the slide. Root-cause
must follow within the deck or in the next 1:1.

**Canon:** Skok + Campbell — cohort decomposition is the forensic tool; suppressing the finding
makes you the problem.

### 7. Ignore late-stage opp age (stalled = false-positive)

**Symptom:** a "verbal" deal has been verbal for 180 days. It's in commit. Last activity was 60
days ago.

**Why it fails:** verbal-stage opps that haven't moved in 6 months are not commits. They are
either dead, deprioritized, or being shopped against you. Including them in commit inflates the
number and guarantees a miss.

**Fix:** apply the stall rule — opp age > 2x median stage age AND last_activity > 45 days →
contribution × 0.5 in commit. Surface stalled opps explicitly.

**Canon:** David Skok — "stalled-opp identification by stage-age is the #1 forecast-hygiene
practice in top-decile SaaS pipelines."

### 8. No pipeline-coverage check

**Symptom:** the commit is $8.4M. The total pipeline is $18M. Coverage ratio is 2.1x. No one
mentions this.

**Why it fails:** coverage < 3.0x means the commit is structurally unsupported. Even if every
stage-conversion assumption is correct, the math doesn't have enough opps to hit commit if a
normal percentage slip.

**Fix:** the tool calculates the coverage ratio. Below 3.0x → warning. Above 3.0x → confirm.

**Canon:** Pacific Crest / KeyBanc SaaS Survey + Forrester pipeline-coverage research — 3.0x is
the SaaS-industry floor; top-quartile maintains 3.0-4.5x.

### 9. Sandbagging (best-case far below pipe-only)

**Symptom:** pipe-only is $25M; best-case is $9M (36% of pipe-only). The CRO is being "conservative".

**Why it fails:** if best-case is < 50% of pipe-only, the team has effectively given up on most
of the pipeline. Either the stage-conversion priors are pessimistic, or the team isn't working
the pipeline.

**Fix:** the tool flags this ratio. If best-case is < 50% of pipe-only, decompose why before
presenting.

**Canon:** McKinsey on forecast bias + Tomasz Tunguz — sandbagging is the more common failure
mode than hockey-sticking, especially after a missed quarter.

### 10. Hockey-sticking (best-case near pipe-only)

**Symptom:** pipe-only is $20M; best-case is $18M (90% of pipe-only). The team is "all-in" on Q3.

**Why it fails:** if best-case is > 80% of pipe-only, the team is assuming nearly all pipeline
will convert. Conversion math shows this is statistically impossible at any reasonable stage
mix.

**Fix:** the tool flags > 80%. Decompose: which stages are being weighted optimistically?

**Canon:** OpenView SaaS forecasting benchmarks — hockey-stick forecasts have 2x lower realization
rate than disciplined forecasts.

---

## Source register (≥ 7 cited)

1. **McKinsey** — forecast-bias research, especially on single-number vs. 3-tier forecast accuracy
2. **Tomasz Tunguz / Theory Ventures** — sandbagging vs. hockey-sticking analysis across 100+
   SaaS companies; regime-change detection via blended windows
3. **OpenView Partners** — annual SaaS benchmarks on commit accuracy, pipeline coverage, hockey-stick
   realization rates
4. **MIT Sloan** / Hyndman & Athanasopoulos, *Forecasting: Principles and Practice* — CoV-based
   confidence bands, blended-window methodology, minimum sample size for stable forecasting
5. **Bain & Company** — commercial-forecasting practice on disclosed vs. undisclosed assumptions
   (2.3x variance differential)
6. **Forrester Research** — pipeline-coverage myths; the 3x floor is necessary but not sufficient
7. **Pacific Crest / KeyBanc Capital Markets** — Private SaaS Survey, the industry data source
   for pipeline-coverage benchmarks and stage-conversion priors
8. **David Skok / *For Entrepreneurs*** — stalled-opp hygiene as the #1 forecast practice in
   top-decile pipelines

---

## Hard rules

1. **Three numbers, always: commit / best-case / pipe-only.** Never one.
2. **Assumption block on every slide with a forecast number.** Never hidden.
3. **Cohort heatmap accompanies every NRR number.** Never just consolidated.
4. **Pipeline coverage ratio surfaced.** Below 3.0x → warning.
5. **Stalled opps downweighted.** Verbal-for-6-months is not a commit.
6. **Sandbagging and hockey-sticking are both flagged.** The middle is the discipline.
