---
name: pre-ship-gate
description: Runs a structured pre-ship safety gate before any production deploy. Executes the pre-flight checklist, scans for the five silent failure modes that pass every local test but surface in production, and delivers a clear go/no-go with specific findings. Use immediately before merging to main or triggering a production deployment.
license: MIT
---

# Pre-Ship Gate

Before shipping anything to production, run this gate. It takes 2–5 minutes and prevents the failure modes that feel impossible to predict until you've shipped one.

## How to use

1. Tell me what you are about to deploy (a brief description of the change is enough).
2. I will run the pre-flight checklist against what you describe.
3. I will scan for the five silent failure modes (see below).
4. You receive a **go** or **no-go** with specific findings and, where relevant, the exact fix.

If anything in the gate is unclear — a missing environment detail, an ambiguous step — I will ask before proceeding, not assume.

---

## Pre-flight checklist

Work through each item for the current change. Answer with the actual state, not yes/no — a one-line description of what you confirmed is more useful than a checkbox.

**Backup** — Is there a recovery point before this change reaches production?
- Database backup taken (or confirmed recent)?
- Prior artifact or image tag retained and reachable?
- Rollback step documented in the deploy runbook?

**Ownership** — Who owns this change in production right now?
- Is the deploying engineer the right person with access to prod?
- Is there a second person aware and reachable if something goes wrong?
- Is on-call coverage confirmed for the rollout window?

**Blast-radius** — How far does this change reach if it fails?
- What percentage of users or traffic is affected on day 1?
- Which downstream services depend on what this change touches?
- Is the blast radius bounded (feature flag, staged rollout, circuit breaker)?

**Mechanism tested on a copy** — Has the change been exercised in a non-production environment that matches prod?
- Did the migration or seed run against a copy of production data?
- Were environment variables, secrets, and feature flags in the test environment aligned with prod values?
- Did the smoke tests cover the exact path that will go live?

**Memory** — Can you recover from a bad deploy without guesswork?
- Rollback command known and tested?
- Time to rollback estimated (is it under your acceptable window)?
- Post-rollback state confirmed: data safe, queues drainable, cache invalidatable?

If any item cannot be answered, resolve it before shipping. A "we'll fix it if something breaks" posture is what makes incidents into outages.

---

## Silent failure modes

These five failure modes pass every local test and surface only in production. Scan for each one:

**1. Migrations that require a manual prod step**
Auto-run in dev, skipped or blocked in prod. Check: does this change include a schema or data migration? Is there a manual apply step in the prod runbook?

**2. Feature gates inverted between environments**
Flag is on in staging, off in prod — so staging tests the new path and prod stays on the old one. Check: does this change sit behind a feature flag? Confirm the flag value in each environment before shipping.

**3. Build cache serving a stale artifact**
The build reports success on the new commit but the artifact in the registry or CDN is from the prior build. Check: was the cache explicitly invalidated? Does the published artifact hash match the expected source commit?

**4. Release pointer not bumped**
A tag, manifest version, or Helm chart version was not updated, so the deploy command pulls the previous image and exits 0. Check: does the deploy reference a mutable pointer (like `latest`) or a version that was not incremented?

**5. Staged rollout confirming the canary, not the full fleet**
The health check passes because it only hits the new canary pods. The full rollout is untested. Check: does this deploy use a staged or canary strategy? Is the health check scoped to the full rollout, not just the first wave?

---

## Verdict format

```
PRE-SHIP GATE — [change description]

STATUS: GO / NO-GO

Pre-flight:
  Backup:                        [one line confirming state]
  Ownership:                     [one line confirming state]
  Blast-radius:                  [one line confirming state]
  Mechanism tested on a copy:    [one line confirming state]
  Memory:                        [one line confirming state]

Silent failure scan:
  Migrations:       CLEAR / RISK — [detail]
  Feature gates:    CLEAR / RISK — [detail]
  Build cache:      CLEAR / RISK — [detail]
  Release pointer:  CLEAR / RISK — [detail]
  Staged rollout:   CLEAR / RISK — [detail]

Findings:
  [Numbered list of issues requiring action before ship, or "None — safe to proceed."]
```

---

*From [operating-kit](https://github.com/Sharrmavishal/operating-kit) — a portable, self-installing operating method for Claude Code and Cursor. Each gate came from a real production failure.*
