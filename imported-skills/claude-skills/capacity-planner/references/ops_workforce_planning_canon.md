# Ops Workforce Planning Canon

Capacity sizing is half the answer. The other half is the human reality
of hiring, ramping, retaining, and structuring the people who staff the
queue. This reference assembles the operational-leadership canon needed
to translate an Erlang-C number into an executable 12-month plan.

## The Canon

### 1. Camille Fournier — *The Manager's Path* (O'Reilly, 2017)

Definitive guide to engineering management ladder, but the
**span-of-control** chapters apply to any ops team. Key thresholds the
`hiring_sequencer.py` enforces:

- **5-7 direct reports** is the healthy band for an ops manager.
- **8-9** is the warning zone — the manager starts dropping 1:1s,
  feedback cycles slip, and team-level decisions queue.
- **10+** = you have a coverage problem, not a leadership problem.
  Hire another manager BEFORE crossing 10.

Fournier also formalizes the **player-coach → pure manager → manager of
managers** progression that gates when a team needs a director.

### 2. Will Larson — *Staff Engineer* (Stripe Press, 2021) and *An Elegant Puzzle*

Larson's chapter on **ramp time as a real cost** is the source for the
"productive ~50% during ramp, 100% after" curve in
`hiring_sequencer.py`. Empirical observations:

- Support T1 hires: 6-10 weeks to full ramp.
- BizOps / Finance ops hires: 12-16 weeks (tool sprawl + tribal
  knowledge).
- IT ops on-call rotation: 8-12 weeks before first solo on-call.

Larson's broader point: **hiring during a fire is too late**. The
sequencer's front-loaded weight (Q1 35%, Q4 15%) is the operational
expression of this principle.

### 3. Betsy Beyer, Niall Murphy, et al. — *The Site Reliability Workbook* (O'Reilly, 2018), Chapter 6: "Eliminating Toil"

Google SRE's framework for **toil budgets** maps directly to ops
shrinkage. Key staffing principle:

- An on-call ops engineer should spend **≤50% on toil**, the rest on
  engineering work that reduces toil.
- If the toil fraction exceeds 50% for >1 quarter, you are
  understaffed relative to incident volume.

The capacity-planner sibling skills (incident-coordinator,
process-mapper) feed inputs into this; the workforce-planning
implication is that "100% of paid hours = available capacity" is
**always** wrong.

### 4. Frances Frei & Anne Morriss — *Uncommon Service* (HBR Press, 2012)

Frei's central argument: **you cannot deliver excellent service across
all attributes simultaneously**. Service-design trade-offs — speed vs.
empathy, breadth vs. depth, low cost vs. high quality — directly
constrain how you size a team. A team chasing all four wins zero of
them. Capacity-planner inputs (AHT, SLA, channel mix) implicitly encode
which trade-off is being made; surfacing that explicitly in the
*Forcing-question library* is what separates a competent ops leader
from a guesser.

### 5. Edward Lawler — *Strategic Workforce Planning* (USC Marshall Center for Effective Organizations, 2008)

Lawler's research distinguishes **operational** workforce planning
(this skill: 0-12 months, role-specific, demand-driven) from
**strategic** workforce planning (CHRO's job: 1-5 years, capability
portfolio, talent supply analysis). The hard rule:

- If you are sizing against next quarter's tickets, you need
  capacity-planner.
- If you are sizing against the company's 3-year automation strategy,
  you need a strategic workforce plan (chro-advisor).
- **Conflating them gets you hired into the wrong jobs.**

### 6. Bersin / Deloitte — *Talent Acquisition Maturity Model* and benchmarks (2015-2023)

Source for the empirically reasonable **attrition + replacement-hire
defaults** in `hiring_sequencer.py` profiles. Bersin benchmarks:

- Support frontline: 25-35% annual attrition. The 30% default reflects
  the BPO-industry midpoint.
- CX/Customer success: 22-28%. Slightly stickier than raw support due
  to relationship investment.
- BizOps/Finance ops: 15-22%. Specialist + analytical work has lower
  turnover.
- Open ops headcount fills in 45-90 days for T1, 90-180 days for
  T2/specialist.

These figures must be sanity-checked against your own HR data — they
are starting points, not commitments.

### 7. Gartner Service Delivery Research — annual reports (Customer Service & Support practice)

Gartner's annual ops benchmarks codify the **multi-channel staffing
premium**: a team that handles voice + email + chat needs ~15-25% MORE
FTE than the simple-sum Erlang-C of each channel alone, because:

- Skill switching cost (context loss between channels).
- Non-uniform demand distributions across channels.
- The classic "blended-agent illusion" — agents claim to be 100%
  flexible across channels but their effective handle times degrade.

The `--profile` flag in capacity_modeler is the place to encode this;
support and CX profiles assume multi-channel realities.

### 8. Andy Grove — *High Output Management* (1983, re-issued 1995)

Grove's framework for **leveraged output** — the manager's output is
the output of her team plus the output of every team she influences.
Applied to ops capacity:

- **A manager's "productive" contribution is not their own ticket
  handles** (which should approach zero past 6 directs); it's their
  effect on the team's throughput, accuracy, and retention.
- This is why the hiring_sequencer counts managers separately from ICs
  and triggers manager hires preemptively at span-of-control limits.

## How These Connect to the Tools

| Tool | Primary Canon |
|---|---|
| `capacity_modeler.py` | Frei (service trade-offs encoded in inputs), Gartner (multi-channel) |
| `utilization_analyzer.py` | SRE Workbook (toil budget = ceiling), Grove (manager leverage) |
| `hiring_sequencer.py` | Fournier (span of control), Larson (ramp curves), Bersin (attrition), Lawler (operational vs. strategic) |

## The Hard Truths

1. **Ramp is real and is a 6-16 week tax.** Plans that assume new
   hires are productive day one are works of fiction.
2. **You will lose 15-35% of your team this year.** Hiring plans that
   don't budget replacement hires understaff you by exactly that much.
3. **You cannot manage 10+ direct reports.** Past 7-8, you are picking
   which directs to neglect.
4. **Service trade-offs are non-negotiable.** Pick which dimensions to
   win and accept losses elsewhere — Frei's central thesis.
