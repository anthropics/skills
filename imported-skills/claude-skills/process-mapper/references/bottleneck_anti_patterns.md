# Bottleneck Anti-Patterns

Seven plus specific anti-patterns that recur in business-process improvement
work. Each is sourced to primary literature, and each has a corresponding
detection or recommendation in the skill's tools.

## Sources

1. **Goldratt, E. M. (1984). _The Goal._** North River Press. — Theory of Constraints.
2. **Kim, G., Behr, K. & Spafford, G. (2013). _The Phoenix Project: A Novel About IT, DevOps, and Helping Your Business Win._** IT Revolution Press. — TOC applied to IT operations.
3. **Spear, S. J. (2009). _The High-Velocity Edge._** McGraw-Hill. — Toyota-derived discipline for complex operations; explicit treatment of why local optimization fails.
4. **Forsgren, N., Humble, J. & Kim, G. (2018). _Accelerate: The Science of Lean Software and DevOps._** IT Revolution. — DORA research; empirical link between flow metrics and outcomes.
5. **Deming, W. E. (1986). _Out of the Crisis._** MIT Press. — System-of-profound-knowledge framework; root-cause discipline.
6. **van der Aalst, W. M. P. (2016). _Process Mining: Data Science in Action,_ 2nd ed.** Springer. — Empirical methodology for discovering actual process behavior vs. documented behavior.
7. **Reinertsen, D. G. (2009). _The Principles of Product Development Flow._** Celeritas Publishing. — Queueing theory and cost of delay.
8. **Forrester Research. (Multiple years.) _Process Mining: Vendor and Market Analyses._** — Industry research on process-mining adoption and the gap between modeled and actual process.

---

## AP-1. Optimizing the non-constraint

**Source:** Goldratt (1984), Kim et al. (2013).

A team identifies that stage 2 of a process is "slow" (relative to other
non-constraint stages) and optimizes it. The actual constraint is stage 4.
Result: throughput is unchanged; inventory grows in front of stage 4.

**Detection:** Compare every stage's P50 to the value-add mean (Rule R1) but
weight the recommendation by impact on total cycle. The skill's
`bottleneck_detector.py` ranks by impact_minutes_p50 specifically to direct
attention to the binding constraint.

**Counter-pattern:** Always solve the longest wait or longest stage first;
ignore "quick wins" elsewhere until the constraint moves.

---

## AP-2. Adding resources before identifying the constraint

**Source:** Goldratt (1984), Reinertsen (2009).

Symptom: "We need to hire more procurement analysts." Reality: the analysts
are not the constraint; manager approval queues are. Adding analysts increases
WIP, lengthens cycle time (per Little's Law), and makes the queue worse.

**Detection:** Rule R2 (wait-share > 40%) catches the case where the wait —
not capacity — dominates.

**Counter-pattern:** First check whether wait time exceeds value-add time. If
it does, no amount of new staffing will help. Remove the handoff, parallelize
the approval, or apply WIP limits.

---

## AP-3. Mistaking wait time for processing time

**Source:** Rother & Shook (1999), Deming (1986).

A team reports that "manager approval takes two days." On inspection, the
manager spends 10 minutes reviewing each request; the rest is queue time.
Process time is 10 minutes; lead time is two days. Treating them as the same
hides the real problem.

**Detection:** The skill's stage `type` field separates `value-add` from
`wait`. The value-add ratio (VA%) in `cycle_time_analyzer.py` quantifies the
gap.

**Counter-pattern:** Force stages to declare their type honestly. Any stage
where the worker is not actively engaged is a wait stage, regardless of who
"owns" it.

---

## AP-4. Inspection-as-quality

**Source:** Pyzdek (Six Sigma Handbook), Deming (1986), Spear (2009).

Defects keep escaping, so the team adds a final QA review. The defects don't
go down (the upstream stages haven't changed) — but cycle time goes up because
of the new stage. Worse, the QA reviewer is now blamed for misses.

**Detection:** Rule R3 (rework share > 15%) with the hypothesis "defects
escape upstream stages."

**Counter-pattern:** Find the earliest stage that could detect the defect; add
the check there (poka-yoke). Stop the line on detection; don't queue defects
for downstream rework.

---

## AP-5. Optimizing the documented process, not the actual one

**Source:** van der Aalst (2016), Forrester process-mining reports.

The team documents the "official" process and optimizes it. Process-mining
tools then reveal that 60% of cases skip stages, loop back, or take undocumented
routes. The optimization had no effect because it targeted a fiction.

**Detection:** The skill cannot detect this from the input JSON alone — it
relies on the user to report actual stage durations from real cases, not
target durations. The "Assumptions" section in SKILL.md surfaces this
explicitly.

**Counter-pattern:** Use ticket-system data, time-stamps, or event logs to
ground stage durations in actual cases. If the data isn't available, the
first step is instrumentation, not mapping.

---

## AP-6. Batched approvals as the default

**Source:** Reinertsen (2009), Anderson (Kanban, 2010).

Approvers batch requests: "I'll review everyone's POs on Friday afternoon."
This adds half the batch interval (typically 3–4 days) to the average wait
time of every request, with no quality benefit.

**Detection:** Wait stages with P50 durations measured in days (hundreds of
minutes) are almost always batched. The skill flags them via R1 and R2.

**Counter-pattern:** Move to continuous-flow approval. If continuous is
infeasible (e.g., a committee that meets weekly), at least shrink the batch
interval or move approval to a lower level where it can run continuously.

---

## AP-7. Local efficiency metrics

**Source:** Goldratt (1984), Deming (1986), Spear (2009).

Each stage is measured on its own efficiency (e.g., "manager handles 95% of
requests within SLA"). The system as a whole is not measured. Each role
optimizes locally, pushing work as fast as possible to the next queue —
which is exactly where it stalls.

**Detection:** The skill's verdict is always at the **process** level (VA%,
total cycle time), never at the stage level. The `bottleneck_detector.py`
recommendation text explicitly invokes Goldratt's "subordinate everything to
the constraint."

**Counter-pattern:** Measure throughput and total cycle time at the process
level. Stage-level metrics are diagnostic, not goal-setting.

---

## AP-8. Skipping the value-stream map and going straight to automation

**Source:** Kim et al. (2013), Forrester process-mining research.

A team buys an RPA / workflow automation tool, then automates the existing
broken process. Result: the bad process now runs faster, with the same wait
queues and same rework rate. Goldratt's term for this is "automating the
mess."

**Detection:** Outside the skill's automated detection; surfaced in
SKILL.md's "Anti-patterns" list.

**Counter-pattern:** Map the value stream first. Eliminate wait and rework
stages. Then — and only then — consider automating what remains.

---

## AP-9. Treating cycle time as fixed

**Source:** Forsgren, Humble & Kim (2018, _Accelerate_).

A team reports cycle time as a single number ("it takes 5 days"). Real cycle
times are distributions, often log-normal, with heavy P90 / P99 tails. A 5-day
P50 with a 30-day P90 is a wildly different process than a 5-day P50 with a
6-day P90; the first is unpredictable, the second is reliable.

**Detection:** The skill captures both P50 and P90 per stage and reports
both totals. A large P90 / P50 ratio in `cycle_time_analyzer.py` is a flag
for high variability even when total cycle time looks acceptable.

**Counter-pattern:** Always quote P50 and P90 (or P50 and P95). DORA's
_Accelerate_ research finds that lead-time **variability** correlates with
business outcomes as strongly as median lead time.
