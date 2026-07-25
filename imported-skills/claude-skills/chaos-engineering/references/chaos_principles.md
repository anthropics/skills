# The principles of chaos engineering

Chaos engineering is the discipline of experimenting on a system in order to build confidence in its capability to withstand turbulent conditions in production. The phrase comes from Netflix's 2014-2016 work productizing what started as Chaos Monkey.

## The 4 founding principles (Netflix, 2016)

### 1. Build a hypothesis around steady-state behavior

Steady state = a measurable, normal-operations metric (latency, throughput, conversion rate, error rate).

Bad: *"What happens if the database goes down?"*
Good: *"When the primary database fails over, p99 checkout latency stays below 800ms and conversion rate stays within 2% of baseline."*

The hypothesis must be **falsifiable** — there must be a measurement that can disprove it.

### 2. Vary real-world events

Inject realistic failure modes:
- Servers crash
- Networks partition or slow
- Disks fill
- Dependencies time out or return errors
- Caches lose data
- Time skews

Don't inject implausible events (e.g., "what if all 50 zones in 5 regions go down simultaneously"). That's not chaos engineering, that's astronomy.

### 3. Run experiments in production

Staging never reproduces:
- Real traffic patterns
- Real cache hit rates
- Real cross-service dependencies
- Real data volumes
- Real user behavior

The only system that has prod failure modes is prod. Start with tiny blast radius (1%), grow as confidence grows.

### 4. Automate experiments to run continuously

A single chaos experiment is a press release. Continuous chaos is engineering.

Maturity progression:
1. Manual one-offs → 2. Weekly Game Days → 3. Scheduled experiments → 4. Continuous chaos in CI/CD

The 5th principle this skill adds:

### 5. Define abort criteria up front

A chaos experiment with no abort criteria is an outage. Every plan must include:

- A specific signal (metric, threshold)
- A specific action (auto-abort, manual abort, escalate)
- A timeline (within N seconds of breach)

If the threshold is hit, abort immediately. Investigate later.

## When to start

You're ready for chaos engineering when:

- [ ] You have basic monitoring (you can detect a steady-state breach)
- [ ] You have on-call rotations (someone is watching when chaos runs)
- [ ] You have at least one tool to inject the desired fault
- [ ] You have an SLO/SLI defined (so you know what "good" looks like)
- [ ] You have postmortem culture that's blameless
- [ ] You have a leadership champion who'll defend the practice

If any of these are missing, fix them first. Premature chaos = outages with no learning.

## When NOT to do chaos engineering

- During a release freeze
- During a known incident
- During peak traffic events without explicit approval
- On systems that don't have steady-state metrics
- On systems where you can't bound the blast radius
- On the day of a security disclosure
- When the team is already firefighting

## Maturity model

| Level | Description | Cadence | Tooling |
|---|---|---|---|
| L0 | None | n/a | none |
| L1 | Manual one-offs in staging | quarterly | tc, manual scripts |
| L2 | Weekly Game Days in staging | weekly | Chaos Toolkit, internal scripts |
| L3 | Limited prod experiments | weekly | Chaos Toolkit / Mesh / Litmus / FIS |
| L4 | Continuous prod chaos with bounded blast radius | daily | Chaos Mesh / Gremlin scenarios |
| L5 | Chaos in CI/CD pipeline; deploys auto-trigger sweeps | per-deploy | Custom + tooling stack |

Most teams should target L3 within 6-12 months of starting. L5 is rare and only justified for the largest distributed systems.

## Common objections (and counters)

| Objection | Counter |
|---|---|
| "We can't break production!" | You already do, just unintentionally. Chaos is intentional, bounded, observed breaks. |
| "This is a customer-facing system." | Start at 1% blast radius. The 99% are unaffected. |
| "We don't have time." | Chaos finds bugs that would otherwise become 4am pages. Time spent on chaos saves time on incidents. |
| "Our system is too critical." | Critical systems have the most to gain from learning their failure modes. |
| "We have HA already." | HA without chaos is HA in theory. Chaos finds gaps in actual HA. |

## What a steady-state metric looks like

Good steady-state metrics:
- p99 request latency (objective, measurable per second)
- Error rate (objective, measurable)
- Conversion rate (business metric, slow but real)
- Successful logins per minute (business + tech signal)
- Queue depth (system health)

Bad metrics:
- "Things feel slow" (not measurable)
- CPU usage (a means, not an end)
- Number of pods running (not customer-facing)

Pick metrics that customers feel. CPU can spike without customer impact; latency and errors can't.

## History

- 2010: Netflix launches Chaos Monkey (kills random EC2 instances)
- 2011: Simian Army expands (Latency Monkey, Conformity Monkey, etc.)
- 2014: Chaos engineering term coined; principles drafted
- 2016: principlesofchaos.org published
- 2018: Chaos Toolkit released as OSS
- 2019: Chaos Mesh and Litmus mature for Kubernetes
- 2020: AWS launches Fault Injection Simulator (FIS)
- 2023+: Chaos engineering becomes mainstream practice in SRE-heavy orgs

## Further reading

- principlesofchaos.org — the foundational document
- *Chaos Engineering* (Casey Rosenthal, Nora Jones) — O'Reilly, 2020
- *Learning Chaos Engineering* (Russ Miles) — O'Reilly, 2019
- Netflix Tech Blog on Chaos Engineering posts (2016-2020)
