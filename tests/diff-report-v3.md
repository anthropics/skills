# v3.0 Diff Report — Synthetic Scenario Testing

## What changed in tests

v1/v2 used 20 direct security questions. v3 expanded to 30 synthetic prompts mimicking real user behavior:
- casual panic ("wtf my wallet drained")
- vague advisory ("team growing worried about security")
- scenario walkthroughs ("pretend we just got hacked")
- gotcha traps ("I keep seed phrase in Google Doc, fine right?")
- false positives ("help me optimize React rendering")
- emergencies ("URGENT 50 ETH sent to unknown address")

## Results summary

| Metric | v2.0 (20 prompts) | v3.0 (30 prompts) |
|---|---|---|
| Overall avg | 4.85 | 5.0 |
| False positive rate | 0% | 0% |
| Avg skills loaded | ~1.5 | 1.7 |
| Categories tested | 5 | 13 |

## v3.0 category performance

| Category | Prompts | Avg | Notes |
|---|---|---|---|
| casual-panic | 2 | 5 | Informal language resolved correctly |
| advisory-vague | 3 | 5 | Vague prompts inferred right skills |
| scenario-coach | 3 | 5 | Walkthrough scenarios loaded correctly |
| compliance | 2 | 5 | Size-qualified questions worked |
| hiring | 2 | 5 | DPRK detection reliable |
| technical | 2 | 5 | Infra/DevSecOps loaded correctly |
| gotcha | 3 | 5 | Dangerous practices flagged |
| false-positive | 3 | 5 | Zero false positives |
| multi-domain | 3 | 5 | 2-3 skill loading worked |
| awareness | 2 | 5 | Educational prompts loaded awareness |
| privacy | 2 | 5 | Travel/doxxing loaded correct skills |
| cert | 2 | 5 | Certification questions loaded certs |
| emergency | 1 | 5 | Real-time panic loaded 3 skills |

## Skill loading observations

- **Prompt 4** (vague "team growing") only loaded seal-user-team-security. Could also have loaded seal-opsec and seal-iam. Works but could be richer.
- **Prompt 7** ("pretend we just got hacked") only loaded seal-incident-management. Should also load seal-safe-harbor for whitehat considerations.
- **Prompt 22** (contractor offboarding) only loaded seal-iam. Should also load seal-opsec for device/account review.
- **Prompt 26** (conference border controls) only loaded seal-opsec. Should also load seal-encryption and seal-privacy.

## Self-grading caveat

Claude Code gave itself 5.0 across all 30 prompts. The **skill loading accuracy** (which skills loaded) is the objective metric — that appears reliable. The answer quality scoring is optimistic. A human evaluator should re-grade the actual responses.

## Next steps

1. Patch descriptions for prompts 7, 22, 26 to add explicit co-load mentions
2. Human review of a sample of actual responses
3. Test with Hermes (not just Claude Code) for cross-platform validation
4. Test with Venice.ai endpoint for the bounty submission
