# Pre-Ship Pre-flight Checklist

Work through each item for the current change. Answer with the actual state, not "yes/no" — a one-line description of what you confirmed is more useful than a checkbox.

---

## Backup
Is there a recovery point before this change reaches production?
- Database backup taken (or confirmed recent)?
- Prior artifact or image tag retained and reachable?
- Rollback step documented in the deploy runbook?

## Ownership
Who owns this change in production right now?
- Is the deploying engineer the right person with access to prod?
- Is there a second person aware and reachable if something goes wrong?
- Is on-call coverage confirmed for the rollout window?

## Blast-radius
How far does this change reach if it fails?
- What percentage of users or traffic is affected on day 1?
- Which downstream services depend on what this change touches?
- Is the blast radius bounded (feature flag, staged rollout, circuit breaker)?

## Mechanism tested on a copy
Has the change been exercised in a non-production environment that matches prod?
- Did the migration or seed run against a copy of production data?
- Were environment variables, secrets, and feature flags in the test environment aligned with prod values?
- Did the smoke tests cover the exact path that will go live?

## Memory
Can you recover from a bad deploy without guesswork?
- Rollback command known and tested?
- Time to rollback estimated (is it under your acceptable window)?
- Post-rollback state confirmed: data safe, queues drainable, cache invalidatable?

---

*If any item cannot be answered, resolve it before shipping. A "we'll fix it if something breaks" posture is what makes incidents into outages.*
