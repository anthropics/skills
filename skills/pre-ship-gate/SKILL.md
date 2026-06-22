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

Read `checklist.md` and work through each item for the current change before issuing a verdict.

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
  [ ] Backup: ...
  [ ] Ownership: ...
  [ ] Blast-radius: ...
  [ ] Mechanism tested on a copy: ...
  [ ] Memory (rollback confirmed): ...

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
