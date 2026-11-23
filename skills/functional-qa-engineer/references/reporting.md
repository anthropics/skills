# Reporting

The reader is a developer who has 2 minutes and wants to know: what is broken, how bad, and where to look.

## Bug card

```
B-<nn> · <Severity: Critical/High/Medium/Low> · <Area> · <status if retested>
<Title: the wrong behaviour in one sentence, with the number that proves it>
Steps:    numbered, from a named entity (project/page) the dev can open
Expected: what should happen (cite the oracle or spec)
Actual:   what happens, measured; quote exact UI text and API codes
Where to reproduce: project/entity link · run/session id · job id · request + response · log excerpt
Evidence: screenshot(s), expected vs actual side by side when useful
Reference: same steps on the reference target/env (web, stage or prod) and its result, for any parity or target-specific bug
```

Rules learned from reviewer feedback (check `bug-card-complete`):
- **Every** card gets preconditions + numbered steps + expected + actual, not only the first few. Write for someone who wasn't there.
- Shared setups get **descriptive names** ("Setup 1: open the Toggles lab"), never shorthand like "S" or "L".
- In a published report, **embed** the screenshots under each card (publish the PNGs with the page and use `<img>` with a caption); a list of file names is not evidence.
- Before filing a target-specific bug, run the same steps on the reference target and put both results on the card (check `reference-parity-first`). If they match, it is shared behaviour or by design, not a parity bug.
- If the feature has PRs, cite the gating line from the diff when classifying a missing option (check `read-pr-gating`): a deliberate gate is a requirements gap, not a regression.
- On a shared account or single-device env, note any contention (another user's activity, slow release of a shared resource) on the card (check `shared-env-contention`).

Severity guide: Critical = blocks the feature's main job; High = wrong result or lost work/data on a common path; Medium = misleading state, workaround exists; Low = cosmetic/copy.

## Retest table

| Bug | Severity | Dev said | Retest | What the retest showed |
Use Fixed / Partly fixed / Not fixed / Intermittent (give the rate, e.g. 2/10) / Blocked (name the blocker and who unblocks it) / Not reproduced (trigger didn't occur) / Not retested. For "Partly", name the part that remains. If the fix is not deployed, say "fix in PR #N, not deployed". Record which build each result was verified on, so a later deploy shows which bugs still need a re-run.

## Verdict (top of report)

One bold sentence (ship / not ship and why), then 3–5 bullets: blockers, regressions, new bugs, what is not deployed. Keep earlier verdicts below, dated, so history is visible.

## Slack TL;DR (draft, never send without the user)

```
Retest <date>: <N> fixed, <N> partly, <N> not fixed, <N> new.
Blockers: B-xx <short>, B-yy <short>
Not deployed: PR #N (B-aa, B-bb)
New: B-cc <short> (High), …
Report: <link>
```

## Hygiene

- No credentials anywhere. Refer to accounts by role ("second user") in shared text.
- Credit bugs a person found manually ("found by <name>").
- Remove bugs that a dev showed are expected or that do not reproduce, and say why in your reply.
