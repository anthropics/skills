# Backend Engineer — Forcing-Question Library

**Discipline (Matt Pocock, derived from `engineering/grill-me`, MIT):** walk these one at a time. Do not skip ahead. Do not bundle. Answers must be written down. If the user cannot answer one, **that is your next investigation** — stop and surface the gap.

These seven questions gate every meaningful backend decision: pattern pick (monolith / modular / services / serverless), database choice, sync vs. async, tenancy model, SLO commitment.

---

## Q1 — "What is your read/write ratio, and what is your one-year QPS forecast at p99?"

**Recommended answer:** two numbers (e.g., "20:1 reads-to-writes; 200 QPS p99 at 12 months, derived from current 30 QPS × 3× growth × 2× peak"). Both must trace to evidence (current production traffic + named growth model), not vibes.

**Why it's the first question:** every database, caching, queue, and sharding decision changes shape based on these numbers. A 100:1 read-heavy workload at < 1000 QPS is a Postgres-with-read-replicas problem — not a Cassandra problem. A 1:1 write-heavy workload at 5000 QPS p99 is a partitioning problem from day one.

**Kill criterion:** "we'll need to scale" with no QPS number — STOP. Pull current traffic from metrics; use the team's funding-stage growth model. Without numbers, every architecture choice is a guess.

**Canon:** Martin Kleppmann, *Designing Data-Intensive Applications* (2017), ch. 1 + ch. 5 (replication); Pat Helland, *Life beyond Distributed Transactions* (2007); Werner Vogels, *Eventually Consistent* (ACM, 2008).

---

## Q2 — "Tenancy model: single-tenant, shared multi-tenant, or isolated multi-tenant?"

**Recommended answer:** one of the three, with explicit rationale tied to data-sensitivity (Q4). B2C → shared multi-tenant default; B2B SaaS → shared multi-tenant with row-level isolation; B2B regulated (healthcare, defense, finance) → isolated multi-tenant or single-tenant.

**Why it matters:** the tenancy model decides 80% of the data-access pattern. Migrating between models is expensive (3–9 months in most cases). Picking implicitly leaves the team rebuilding in year 2 to win an enterprise deal that requires tenancy isolation.

**Kill criterion:** "single-tenant for every customer" without an enterprise-pricing model — STOP. Single-tenant cost economics only work at $100K+ ARR per tenant; for everything else, shared with isolation guarantees.

**Canon:** AWS *SaaS Tenant Isolation Strategies* whitepaper (2021); Tomasz Tunguz, *Multi-tenancy economics for SaaS* (2019); Aaron Patterson + Rails security advisories (2014–2024) on row-level isolation patterns.

---

## Q3 — "Sync request/response, async (queue), or event-driven? Pick a default and a rationale."

**Recommended answer:** one of the three as the default, with the named exception class (e.g., "sync default for all customer-facing APIs; async via Postgres LISTEN/NOTIFY for emails + webhooks; defer event-driven until 2nd team owns 2nd bounded context").

**Why it matters:** premature event-driven architecture is the #1 architecture-failure mode in mid-stage startups. It distributes the problem across nine systems before the team understands the original one. Reinertsen + Helland are both explicit: pick sync default and EARN your way into async.

**Kill criterion:** "event-driven across all services" with team size < 20 — STOP. Reduce to sync-default with an explicit async lane for genuinely-async work (emails, webhooks, batch processing).

**Canon:** Donald Reinertsen, *Principles of Product Development Flow* (2009), Principle Q5 (queueing theory); Pat Helland, *Life beyond Distributed Transactions* (2007); Martin Fowler, *What do you mean by Event-Driven?* (martinfowler.com, 2017); Bernd Rücker, *Practical Process Automation* (2021).

---

## Q4 — "Data sensitivity tier: public, internal, PII, PHI, or PCI?"

**Recommended answer:** the highest tier present in the system. PII triggers GDPR / CCPA / state privacy laws + encryption-at-rest + audit logs. PHI triggers HIPAA + BAA chain + dedicated infrastructure or HIPAA-compliant managed services. PCI triggers PCI-DSS Level 1–4 with attached scope-reduction obligations.

**Why it matters:** data sensitivity changes the floor of every other decision. PHI + a single shared-tenant Postgres + no audit logging = enforcement risk. PCI in scope + handing card data to a startup-built API = avoidable scope. Stripe / Plaid / Auth0 exist specifically to remove scope.

**Kill criterion:** PHI or PCI in scope + no named compliance owner + no encryption-at-rest plan — STOP. Bring in `ra-qm-team` skill (HIPAA / FDA) or escalate to `cs-ciso-advisor`.

**Canon:** HIPAA Security Rule (45 CFR § 164); PCI-DSS v4.0 (2024); GDPR Articles 5, 25, 32 (EU 2016/679); NIST SP 800-53 rev. 5 (security controls); CISA *Secure by Design* guidance (2023+).

---

## Q5 — "Monolith, modular monolith, or microservices — and what is the team-size justification?"

**Recommended answer:** modular monolith default for team size < 30; microservices ONLY when (a) team size ≥ 30 with named domain owners, (b) bounded contexts have provably-independent deployment cadence, AND (c) a platform team exists or is funded. Anything else → modular monolith.

**Why it matters:** Sam Newman's *MonolithFirst* is the canon. Premature microservices distribute the design problem across N services + a network. Andy Hunt's *Pragmatic Programmer* second edition (2019) reaffirms: the cost of a microservice is the cost of a system, not a module.

**Kill criterion:** "microservices because [reason that isn't team-size + bounded-context independence + platform team]" — STOP. Modular monolith with clear module boundaries. Extract a service only when the second team needs to own it.

**Canon:** Sam Newman, *Building Microservices* 2e (2021), ch. 3 "Splitting the Monolith"; Martin Fowler, *MonolithFirst* (2015); Susan Fowler, *Production-Ready Microservices* (2017); Matthew Skelton & Manuel Pais, *Team Topologies* (2019); Eric Evans, *Domain-Driven Design* (2003).

---

## Q6 — "What is your RPO and RTO?"

**Recommended answer:** two numbers (e.g., "RPO 5 min, RTO 30 min for prod database; RPO 24h, RTO 4h for analytics warehouse"). Different surfaces can have different targets. Both must be named in writing.

**Why it matters:** RPO (data loss tolerance) and RTO (recovery time tolerance) decide backup cadence, replication topology, multi-region cost, and runbook ownership. Without them, the team rebuilds the same disaster-recovery surprise during every outage.

**Kill criterion:** customer-facing prod database + no RPO/RTO documented — STOP. Define them. Then implement the runbook + restore drill BEFORE the launch.

**Canon:** Google SRE Workbook (Beyer et al., 2018), ch. 7 + ch. 8 on disaster recovery; ISO 22301 (Business Continuity); AWS *Disaster Recovery of Workloads on AWS* whitepaper (2024).

---

## Q7 — "What is the SLO (service-level objective), and who is the named error-budget consumer?"

**Recommended answer:** an SLO tied to a measurable SLI (e.g., "99.9% of requests succeed in < 500ms over rolling 30 days"), AND a named team that consumes the error budget (e.g., "engineering — when budget is < 25% remaining, feature work halts and reliability work starts").

**Why it matters:** without a named SLO consumer, the error budget is rhetorical. Without a measurable SLO, "reliability" is a vibe. Google's SRE program is built around this loop: SLI → SLO → error budget → budget consumer. Fork into `slo-architect` to formalize the design.

**Kill criterion:** "we want high availability" with no SLO number AND no budget consumer — STOP. Pick a number (99%, 99.5%, 99.9%, 99.99%) and the consumer (engineering, product, executive). No SLO = no error budget = no reliability work prioritization.

**Canon:** Google SRE Workbook (2018), ch. 2–4; Niall Murphy + Betsy Beyer, *Site Reliability Engineering* (2016); Andrew Clay Shafer, *The SLO Handbook* (2019); Google *Implementing SLOs* (engineering.google.com, 2024).

---

## How to use this library in a conversation

1. **State the rule first** — seven questions, one at a time, before any DB / API / pattern recommendation.
2. **One question per turn.** No bundling.
3. **Recommend the answer.** Cite the canon every time.
4. **Surface the kill criterion.** If the user trips one, stop and resolve the gap.
5. **Track the answers.** Write them to `/tmp/backend-grill-<date>.md`.
6. **After Q7, run `backend_decision_engine.py`** with the seven answers as inputs.
