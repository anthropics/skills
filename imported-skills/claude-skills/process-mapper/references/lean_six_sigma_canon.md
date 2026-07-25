# Lean / Six Sigma / Theory-of-Constraints Canon

A working reference for the process-mapper skill. The concepts below are the
intellectual foundation for every detection rule and verdict band the skill
emits. Citations are deliberately to the primary sources, not blog posts.

## Sources

1. **Womack, J. P. & Jones, D. T. (1996). _Lean Thinking: Banish Waste and Create Wealth in Your Corporation._** Free Press. — The five-step Lean discipline: specify value, identify the value stream, make value flow, let the customer pull, pursue perfection.
2. **Rother, M. & Shook, J. (1999). _Learning to See: Value Stream Mapping to Add Value and Eliminate Muda._** Lean Enterprise Institute. — The canonical text on Value Stream Mapping (VSM); origin of current-state / future-state map distinction.
3. **Goldratt, E. M. (1984). _The Goal: A Process of Ongoing Improvement._** North River Press. — The Theory of Constraints: identify, exploit, subordinate, elevate, repeat. Every process has exactly one binding constraint at a time.
4. **Ohno, T. (1988). _Toyota Production System: Beyond Large-Scale Production._** Productivity Press. — Origin of the seven wastes (muda), pull system, jidoka, and andon discipline.
5. **Liker, J. K. (2004). _The Toyota Way: 14 Management Principles from the World's Greatest Manufacturer._** McGraw-Hill. — Modern systemic treatment of TPS principles for non-manufacturing operations.
6. **Pyzdek, T. & Keller, P. (2018). _The Six Sigma Handbook,_ 5th ed.** McGraw-Hill. — DMAIC discipline, SIPOC, process-capability indices, defect-rate measurement.
7. **Anderson, D. J. (2010). _Kanban: Successful Evolutionary Change for Your Technology Business._** Blue Hole Press. — WIP limits, pull system applied to knowledge work, cumulative flow diagrams.
8. **Reinertsen, D. G. (2009). _The Principles of Product Development Flow._** Celeritas Publishing. — Queueing theory for knowledge-work product development; cost of delay.

---

## The Seven Wastes (TIMWOOD)

Ohno's original taxonomy, with the eighth ("non-utilized talent") added later:

| Code | Waste | What it looks like in business processes |
|------|-------|--------------------------------------------|
| **T** | Transport | Moving work between systems / inboxes / queues for no reason |
| **I** | Inventory | Backlogs of pending tickets, unprocessed invoices, open POs |
| **M** | Motion | People hunting for information, switching tools, reading email threads to reconstruct context |
| **W** | Waiting | Work sitting in someone's queue (the largest waste in office work) |
| **O** | Over-production | Producing forecasts, reports, or work nobody requested |
| **O** | Over-processing | Approval chains that add no scrutiny, gold-plating |
| **D** | Defects | Errors that force rework downstream |
| **(N)** | Non-utilized talent | Skilled people doing low-skill work |

The process-mapper skill identifies these via stage `type`: `wait` captures
**W** (and often **I**); `rework` captures **D**. Mis-labelling a wait stage as
`value-add` is the most common data-quality failure and will mask the true
constraint.

---

## Value Stream Mapping (Rother & Shook)

VSM separates **process time** (PT) from **lead time** (LT). For each stage:

- **PT** = the time work actually spends being touched.
- **LT** = the elapsed wall-clock time from when work arrives at the stage to
  when it leaves.

In the process-mapper schema, a `value-add` stage's `duration_minutes_p50` is
PT-like; a `wait` stage's duration is the LT component between PT-stages.

The **process cycle efficiency** (PCE) is:

    PCE = Total value-add time / Total lead time

This is exactly what `cycle_time_analyzer.py` computes as the "value-add ratio."
Rother & Shook's published benchmarks: office processes typically score
PCE < 10%; well-run service operations land 10–25%; world-class manufacturing
can clear 25–40%.

---

## Theory of Constraints (Goldratt)

Goldratt's Five Focusing Steps:

1. **Identify** the constraint.
2. **Exploit** it (squeeze every minute of capacity from the constraint).
3. **Subordinate** everything else to the constraint.
4. **Elevate** the constraint (only after step 2 is exhausted, add capacity).
5. **Repeat** — once the constraint moves, return to step 1.

Two implications used in the skill:

- **Optimizing a non-constraint stage produces no system improvement.** It
  builds inventory in front of the constraint. The `bottleneck_detector.py`
  output is ranked by impact specifically so users target the constraint
  first.
- **The constraint is almost always a wait stage in office work.** This is
  why Rule R2 (wait-share > 40%) is heavily weighted.

---

## Kanban WIP Limits (Anderson)

Little's Law:

    L = lambda * W

Where L = items in the system (WIP), lambda = throughput (items per unit time),
and W = average cycle time. Rearranged:

    lambda = L / W

Two practical consequences:

- **Cycle time scales linearly with WIP.** Cutting WIP in half cuts cycle time
  in half (other things equal). This is why the skill computes throughput from
  WIP / cycle time and surfaces a WIP-limit recommendation when wait-share is
  high.
- **Adding people to a wait-bound process makes it worse.** New workers add
  WIP without expanding the constraint, lengthening cycle time. The
  `bottleneck_detector` action text says this explicitly.

---

## Six Sigma DMAIC and Rework

Pyzdek's DMAIC (Define, Measure, Analyze, Improve, Control) treats rework as
a downstream symptom of an upstream defect. The Six-Sigma rule the skill
encodes: **rework is always solved upstream, never downstream.** Adding a
quality-control inspector at the end of the line catches defects but doesn't
prevent them, and inspection-as-quality is itself a TIMWOOD waste
(over-processing).

The poka-yoke (error-proofing) recommendation in Rule R3 follows directly:
add the check at the earliest stage that can detect the defect.

---

## Reinertsen's Queueing Insights

Reinertsen's _Principles of Product Development Flow_ adapts manufacturing
queueing theory to knowledge work. Key results used in the skill:

- **High utilization explodes queue length.** A worker at 90% utilization has
  ~10x the queue of a worker at 50% utilization. Office workflows that pin
  approvers at 100% utilization see wait stages grow without bound.
- **Small batches cut queue time.** Batched approvals (e.g., weekly review
  cycles) inflate P50 wait times by half the batch interval on average.

When the skill recommends "remove the handoff or batch," this is the canon
behind it.
