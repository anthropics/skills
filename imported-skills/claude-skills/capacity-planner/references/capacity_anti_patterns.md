# Capacity Planning Anti-Patterns

Every ops leader who has missed a peak season has fallen into one or
more of these patterns. The math (queueing-theory-canon.md) and the
people factors (ops-workforce-planning-canon.md) make each of these
predictably destructive. This reference enumerates the eight most
common failure modes with sources and the specific guard each tool
implements.

## The Anti-Patterns

### 1. Plan-to-100%-Utilization

**The mistake:** "We have 10 people billing 40 hours each, so we have
400 hours of capacity. Demand is 380 hours. We're fine."

**Why it fails:** Erlang-C and Hopp & Spearman's VUT equation both show
queue length grows as U/(1-U). At 95% utilization, average wait time is
~19× the service time. At 99%, it's ~99×. Variability turns a
"barely-covered" plan into nightly fires.

**Source:** Donald Reinertsen, *Principles of Product Development
Flow* (2009), Principle 12: "We need to operate at lower levels of
utilization."

**Tool guard:** `capacity_modeler.py` sizes against 70/80/90% scenarios
and flags any sizing point above 85% with a Reinertsen-cited warning.

### 2. Treat-Ramp-as-Instant

**The mistake:** "We approved 8 new hires for Q3, so we have +8 FTE
of capacity starting Q3."

**Why it fails:** A new T1 support hire is ~50% productive in weeks 1-8.
A new BizOps analyst is closer to ~30% productive in weeks 1-12 because
of tool sprawl and tribal knowledge. The "wait, they're not contributing
yet" gap is when your team burns out.

**Source:** Will Larson, *Staff Engineer* (Stripe Press, 2021); Camille
Fournier, *The Manager's Path* (O'Reilly, 2017).

**Tool guard:** `hiring_sequencer.py` applies a productivity factor
that linearly ramps 50% → 100% over `ramp_time_weeks`, and front-loads
hires (Q1 35%, Q2 30%, Q3 20%, Q4 15%) so EOY productivity catches the
adjusted target.

### 3. Ignore-Attrition

**The mistake:** "We have 15 today. We need 35 by EOY. Hire 20."

**Why it fails:** At 30% annual attrition (BPO-industry midpoint), you
will lose 4-5 of the original 15 during the year AND ~3-5 of your new
hires before they fully ramp. The real gap is 28-30 hires, not 20.

**Source:** Bersin / Deloitte talent benchmarks (2015-2023); Edward
Lawler, *Strategic Workforce Planning* (USC CEO, 2008).

**Tool guard:** `hiring_sequencer.py` requires `attrition_rate_annual_pct`
and distributes attrition quarterly via compounded probability, adding
the expected replacement hires to the gap calculation.

### 4. Hire-ICs-Forever

**The mistake:** "We don't need a manager — everyone's an
individual contributor reporting to the director."

**Why it fails:** Fournier's research (and Andy Grove's *High Output
Management* before her) is unambiguous: at 8-10+ direct reports, 1:1s
degrade, feedback cycles slip, attrition climbs, and the director
becomes the bottleneck. The cost shows up as attrition + ramp re-work,
not as a missed SLA.

**Source:** Camille Fournier, *The Manager's Path*, ch. 5; Andy
Grove, *High Output Management* (1983), ch. on managerial output.

**Tool guard:** `hiring_sequencer.py` triggers a manager hire when
projected span of control exceeds 7 ICs per manager, reallocating one
quarter's IC slot to a manager hire.

### 5. Size-to-P50-Demand-Only

**The mistake:** "Average daily volume is 320 tickets. We can handle
that."

**Why it fails:** Demand is a distribution, not a number. If P50 is
320 and P90 is 480, you will be staffed below SLA 10% of business
days. Customers don't care that you hit SLA on average; they
remember the day you didn't.

**Source:** Brad Cleveland, *Call Center Management on Fast Forward*
(4th ed., 2019); A.K. Erlang (1909) on traffic distributions.

**Tool guard:** `capacity_modeler.py` requires P50, P90, AND P99
demand inputs and sizes the recommendation to **P90** with breach
probability reported at all three percentiles.

### 6. No-Shrinkage-Adjustment

**The mistake:** "Our agents work 8 hours a day, so 8 hours of
capacity per agent."

**Why it fails:** 30% shrinkage is industry-typical. The 8 hours
actually delivers ~5.6 productive hours after breaks, training,
1:1s, sync meetings, ad-hoc interrupts, and the unspoken time spent
recovering between high-cognitive-load contacts.

**Source:** Cleveland, *Call Center Management on Fast Forward*;
Google SRE Workbook (2018) ch. 6 on toil budgets.

**Tool guard:** `capacity_modeler.py` requires `shrinkage_pct`,
applies a profile default if not provided (support 30%, BizOps 25%,
finance-ops 22%, IT-ops 28%), and outputs **loaded FTE** (post-shrinkage)
distinct from **raw FTE** (Erlang-C agents).

### 7. Single-Channel-Model-for-Multi-Channel-Work

**The mistake:** "Sum Erlang-C of voice + chat + email = total
required FTE."

**Why it fails:** Skill-switching cost. Demand-distribution mismatch
(chat is bursty; email queues overnight; voice spikes at 10-11am).
Real blended-agent productivity is 15-25% below the simple sum
because handoff context-loss is taxed per switch. Gartner research
consistently finds this premium.

**Source:** Gartner Customer Service & Support practice annual
benchmarks (2015-2023); Sir J.F.C. Kingman (1961) on G/G/1 queues
(variability amplifies wait time).

**Tool guard:** `capacity_modeler.py` `--profile` flag encodes
channel-mix realities (support, cx profiles assume blended channels
with a higher shrinkage default).

### 8. No-Surge-Plan-for-P99-Events

**The mistake:** "We're sized to P90 demand. The P99 day will be bad
but it's only 1% of days."

**Why it fails:** P99 days correlate with the highest-revenue events
(product launches, billing-cycle peaks, security incidents,
regulatory deadlines). Missing SLA on those days has
outsize commercial consequences relative to the calendar share.
You need an explicit surge plan: overflow tiering, on-call rotation,
contracted BPO overflow capacity, or a documented degradation contract.

**Source:** Hopp & Spearman, *Factory Physics* (3rd ed., 2008) on
peak-demand staffing; Reinertsen, *Principles of Product Development
Flow* on capacity-margin discipline.

**Tool guard:** `capacity_modeler.py` reports P(SLA breach) at P99 in
all three utilization scenarios, surfacing whether your 80%-utilization
sizing leaves you exposed on peak days.

## Additional Anti-Patterns Worth Naming

Beyond the eight, three more deserve mention because they appear in
nearly every quarterly planning cycle:

### 9. Use-Last-Year's-AHT

Average handle time creeps. Product complexity grows. Self-service
deflects the easy tickets, leaving harder ones in the queue. **Re-baseline
AHT every quarter**, not annually. (Source: Cleveland.)

### 10. Conflate-Operational-with-Strategic-Planning

This skill is for the *next 12 months*. If you are planning for a 3-year
automation reshape, you need chro-advisor or a strategic workforce plan,
not Erlang-C. (Source: Lawler.)

### 11. Plan-Without-Demand-Forecast-Confidence-Interval

A single point estimate of "we'll handle 4,000 tickets/month next year"
is a fiction. You need a forecast distribution. If sales forecasts a
40% YoY growth, your demand P90 grows faster than your demand P50 (more
variance). (Source: Kingman; Hopp-Spearman.)

## Christensen-Raynor on Resource Allocation

Clayton Christensen and Michael Raynor's *The Innovator's Solution*
(HBR Press, 2003) makes the meta-point: **a company's actual strategy
is what it staffs**, not what it says. If your capacity plan funds
firefighting at 80% and improvement at 20%, your strategy is
firefighting regardless of any PowerPoint deck. The capacity plan is
where strategy meets payroll. Take it seriously.

## Lencioni and Goldratt: The Two Disciplines

Pat Lencioni's *The Five Dysfunctions of a Team* (2002) and Eli
Goldratt's *The Goal* (1984) bookend the operational reality:

- **Lencioni**: trust + healthy conflict are prerequisites for
  capacity discussions to be honest. Teams that can't have direct
  conversations about whether someone is overloaded will silently
  fail the capacity plan.
- **Goldratt**: subordinate everything to the bottleneck. If your
  bottleneck is escalation engineering, don't hire more T1s — you'll
  just queue more work at the choke point.

These appear in the *Forcing-question library* of SKILL.md.

## McKinsey + MIT Sloan on Queueing-Blind Staffing

McKinsey's Customer Care practice (2018-2023 reports) and MIT Sloan's
Service Operations research repeatedly document the gap between
"intuitive" staffing (manager judgment, headcount ratios) and
queueing-theory staffing. The gap is empirically 15-35%: intuitive
plans understaff at peak and overstaff at trough. The fix is not more
intuition; it is the math in `capacity_modeler.py`.

## The Closing Discipline

For every capacity plan, ask three questions:

1. **What's the queueing math?** (Erlang-C, P90 demand, ≤80% util.)
2. **What's the people reality?** (Ramp, attrition, span of control.)
3. **What's the bottleneck?** (Capacity-planner sizes around a
   bottleneck; it does not find it. Use `process-mapper` first.)

Miss any of these and the plan is fiction.
