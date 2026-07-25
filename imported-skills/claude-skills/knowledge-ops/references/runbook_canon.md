# Runbook Canon

Internal-operations runbook design discipline — what makes a runbook safe to execute at 3am during an incident, and where the discipline comes from. Seven authoritative sources cited.

## What a runbook is (and is not)

A **runbook** is the executable artifact an operator follows under time pressure. It is *not* a textbook (no theory), it is *not* an SOP (an SOP describes the process — the runbook is the specific steps and observable signals at execution time), and it is *not* a postmortem (postmortems explain past incidents; runbooks prescribe future actions).

Every runbook step must specify six things — and `runbook_validator.py` enforces all six:

1. **Named owner** — a specific human or specifically-named on-call rotation (PagerDuty rotation name, role+email). Not "the team", not "ops".
2. **Expected duration** — concrete number + unit. "5 minutes", "30 seconds". Not "quick" or "fast".
3. **Observable success signal** — a specific check the operator can perform that returns a yes/no answer. "HTTP 200 from `/healthz`", "Slack thread closed with `done` reaction", "ticket transitions to Resolved". Not "service is up", not "looks good".
4. **Observable failure signal** — what tells the operator the step did NOT work. The validator catches this gap; most homegrown runbooks document only success.
5. **Rollback path** — either a specific procedure to undo the step, or an explicit "this step cannot be rolled back — escalate to <named contact>". Silent absence of rollback is the most dangerous gap.
6. **Escalation contact** — named human, role+email, or named on-call rotation. Not "engineering", not "ops".

## Why these six attributes specifically

These six are the union of the requirements imposed by the seven sources below. Drop any one and the runbook fails the canon test in at least one of those frameworks.

## Seven authoritative sources

### 1. Beyer, Murphy, Rensin, Kawahara, Thorne (eds.) — *The Site Reliability Workbook* (O'Reilly, 2018), Ch. 8

Google SRE Workbook on "On-Call". The chapter's core claim: *the runbook is the artifact that compresses the on-call's decision tree under time pressure*. Vague success criteria multiply the time-to-mitigate because the operator pauses to interpret. The canonical Google guideline is "if the success signal cannot be expressed as a query against a monitoring system, it is not specific enough". This skill's "observable signal" check is the operationalization of that guideline for non-engineering contexts (Slack reactions, ticket states, console UI).

### 2. Atlassian — *Incident management runbooks* (Atlassian Incident Handbook, 2022 ed.)

Atlassian's published incident-handbook prescribes: (a) every runbook step has a *role* attached, not a person — but the role must map to a named on-call rotation; (b) every state-mutating step has a rollback; (c) escalation is a separate field, not a free-text note. This skill's `--profile support` variant of `sop_generator.py` follows Atlassian's escalation-matrix convention.

### 3. PagerDuty — *Incident Response Documentation* (PagerDuty open-source, 2017 onwards)

PagerDuty's open-source incident-response framework distinguishes between **major-incident runbooks** (the comms cascade — who's notified, in what order, with what SLA) and **technical-recovery runbooks** (the engineering steps to mitigate). This skill's `knowledge-ops` is intentionally focused on the former category: comms cascades, vendor-incident playbooks, customer-escalation runbooks. Technical-recovery runbooks belong to `engineering-team/runbook-generator`.

### 4. AWS — *Well-Architected Framework, Operational Excellence pillar* (AWS, ongoing)

AWS's Operational Excellence pillar makes the canonical argument for rollback discipline: *"you cannot run a process you cannot reverse without first agreeing what 'reverse' means"*. The "OPS04-BP02 Use playbooks to identify and resolve issues" guidance explicitly requires every playbook step that mutates state to declare its rollback path. The `runbook_validator.py` `ROLLBACK` check enforces this.

### 5. Charity Majors — *Observability Engineering* (O'Reilly, 2022, co-authored with George Miranda and Liz Fong-Jones)

Majors' argument that **runbooks decay faster than the systems they describe** is the canonical justification for `kb_ingester.py`'s stale-page detection. Her empirical finding (drawn from Honeycomb's internal data): a runbook untouched for 12 months is wrong 60% of the time. The default `--stale-days 365` setting in `kb_ingester.py` is calibrated to this.

### 6. Susan Fowler — *Production-Ready Microservices* (O'Reilly, 2016)

Fowler's Ch. 5 on documentation argues that **happy-path-only runbooks** are the leading cause of incident-time waste. Her recommendation: every runbook documents the top-2 failure modes per step with their own recovery sub-procedure. The forcing-question library in `SKILL.md` enforces this at the question-7 stage.

### 7. ITIL v4 — *Service Operation* practice guide (Axelos, 2019)

ITIL v4 makes the formal distinction between *procedure* (the SOP) and *work instruction* (the runbook): the procedure describes what is to be done at a process level; the work instruction describes how to do it at the step level. Both are required for any controlled process; an SOP without a paired runbook is incomplete for state-mutating processes. This is why `knowledge-ops` ships both `sop_generator.py` and `runbook_validator.py` — the same KB needs both artifact types.

## Common runbook anti-patterns

- **"The team owns it"** — no it doesn't. Name a human or an explicitly-defined on-call rotation.
- **"Verify the service is up"** — what does "up" mean to a new operator at 3am? Specify the observable check.
- **"Rollback: see runbook X"** — and runbook X says "see runbook Y". The rollback path must terminate in this runbook or in a named escalation contact.
- **"Escalation: engineering"** — which person, which rotation, what SLA? Engineering is 200 people.
- **Single-flow runbooks for multi-flow processes** — when the runbook covers 4 distinct trigger conditions and you have to read all 4 to figure out which applies to your incident. Split it.
- **Runbooks last reviewed before the system was rearchitected.** The stale check catches these.

## How this skill applies the canon

- `runbook_validator.py` enforces all six attributes per step.
- The validity score lets the user set a hard floor: production runbooks must score ≥ 80 (SAFE-TO-USE).
- `kb_ingester.py` flags stale runbooks (default 12 months) per Majors's decay finding.
- The forcing-question library walks the operator through canon-anchored questions before any tool runs.
