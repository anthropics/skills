# Queueing Theory Canon for Ops Capacity Planning

Capacity planning for ops teams (Support, CX, BizOps, Finance ops, IT ops)
without queueing theory is guesswork. The fundamental insight: as
utilization approaches 100%, wait time approaches infinity non-linearly.
Plan to 90% and your SLA collapses. Plan to 70-80% and you have surge
capacity. The math is over 100 years old, and ignoring it is the most
expensive mistake an ops leader makes.

## The Canon

### 1. A.K. Erlang (1909) — *The Theory of Probabilities and Telephone Conversations*

Erlang's seminal paper on telephone-traffic load. Introduced the Erlang
unit of offered load (a = arrival_rate × service_time) and gave the
formula now called Erlang-B (loss systems) and Erlang-C (waiting systems).
**Erlang-C** is what you want for any ops queue where tickets/calls wait
rather than being dropped:

```
P(wait) = (a^N / N!) * (N / (N - a)) / [ sum_{k=0..N-1} a^k/k! + (a^N/N!)*(N/(N-a)) ]
```

Where N is the number of agents, a is the offered load. **This is the
single most important formula in ops capacity planning.** Implemented in
`scripts/capacity_modeler.py` in ~30 lines of stdlib Python.

### 2. J.D.C. Little (1961) — *A Proof for the Queuing Formula L = λW*

**Little's Law**: in steady state, the average number of items in a queue
(L) equals the average arrival rate (λ) multiplied by the average time an
item spends in the system (W). Three implications for ops leaders:

- **You cannot pick L, λ, and W independently.** If demand (λ) doubles
  and headcount (L capacity) stays flat, wait time (W) must double — and
  via Erlang-C, it actually grows much faster than that near saturation.
- **Reducing average handle time** is mathematically equivalent to
  hiring, up to the utilization ceiling.
- **WIP limits work** because they put a hard cap on L, which (given fixed
  capacity throughput) directly caps W.

### 3. Hopp & Spearman — *Factory Physics* (3rd ed., 2008)

The bible of operations science applied to manufacturing. Chapters 8-9
cover variability and queueing rigorously. Key takeaway for ops leaders:
**the VUT equation** for cycle time at a workstation,

```
CT_q ≈ V × U × T
```

where V is variability (coefficient-of-variation squared), U is utilization
factor U/(1-U), and T is mean service time. Notice U/(1-U): at U=0.80, the
multiplier is 4. At U=0.90, it's 9. At U=0.95, it's 19. **This is why
"plan to 100% utilization" is the most expensive sentence in ops.**

### 4. Donald Reinertsen — *The Principles of Product Development Flow* (2009)

The most important book on queueing in knowledge work. Principle 7
("Queue size, not capacity utilization, is the primary control variable")
and Principle 12 ("We need to operate at lower levels of utilization")
make the case rigorously: **80% utilization is the safe operating ceiling
for variable-arrival queues**. Past that, queue length and cycle time
explode super-linearly. Reinertsen's diagnostic chart of "% utilization
vs. queue length" should be hanging in every ops leader's office.

### 5. Sir J.F.C. Kingman — *On Queues in Heavy Traffic* (1961)

**Kingman's formula** for a G/G/1 queue (general arrival + general
service distribution, single server):

```
E[W_q] ≈ (ρ / (1-ρ)) × ((c_a^2 + c_s^2) / 2) × τ
```

where ρ is utilization, c_a and c_s are coefficients of variation for
arrivals and service, τ is mean service time. **Implication: variability
in either arrivals or service amplifies wait time as much as utilization
does.** This is why bursty channels (email tickets that all arrive at
9am Monday) require MORE staffing slack than steady channels.

### 6. Brad Cleveland — *Call Center Management on Fast Forward* (4th ed., 2019)

The applied operating manual for service-level queues. Conventions
codified by Cleveland and used in `scripts/capacity_modeler.py`:

- Size to **P90 demand** (not P50, not P99) — P50 leaves you breaking
  SLA half the time; P99 over-staffs by 30-50%.
- **Shrinkage** must be a line item. 30% is a reasonable default for
  support (training, breaks, sync meetings, PTO, ad-hoc interrupts).
- **Service level** is the right SLA metric, not abandon rate alone:
  "answered within T seconds" as a probability.

### 7. ITIL 4 Service Management Practices (Axelos, 2019)

ITIL's *Service Operation* practice guidance codifies the canonical
demand-and-capacity-management process for IT ops teams. Key constructs
borrowed:

- **Demand management** = forecasting + smoothing (e.g., release calendars
  scheduling fewer changes during peak ticket windows).
- **Capacity management** = three sub-processes: business capacity
  (forecast), service capacity (workload analysis), component capacity
  (resource-level).
- **Service-level management** = the SLA contract that ties Erlang-C
  inputs to commitments.

### 8. M. Armony, S. Israelit, A. Mandelbaum, et al. — *On Patient Flow in Hospitals* (Stochastic Systems, 2015)

Modern empirical research on multi-class queues with priorities and
abandonment — directly applicable to multi-tier support (T1/T2/T3 with
escalation paths). Empirically validates that **abandonment plus
priority routing** in a real call/ticket center produces wait-time
distributions very close to G/G/c with class-specific service rates.
Confirms Erlang-C is the right "first model" for capacity sizing.

## How These Connect to the Tools

| Tool | Primary Canon |
|---|---|
| `capacity_modeler.py` | Erlang (1909) Erlang-C, Cleveland (sizing convention) |
| `utilization_analyzer.py` | Reinertsen (>80% threshold), Hopp-Spearman VUT, Little's Law |
| `hiring_sequencer.py` | Cleveland (shrinkage), Kingman (variability premium), ITIL (demand management) |

## The One-Sentence Summary

If you remember nothing else: **never plan an ops team to above 80%
sustained utilization** — Reinertsen Principle 12, validated by Hopp &
Spearman's VUT equation and Erlang's 1909 telephone-traffic math. The
arithmetic is unforgiving.
