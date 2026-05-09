---
name: frontend-law-auditor
description: Human-centered frontend quality gate and theory-based audit skill. Use when reviewing or debugging web/mobile UI for cognitive friction, conversion drop-offs, confusing forms, weak feedback, poor interaction flow, or pre-release UX signoff. Audits interfaces against Fitts, Hick, Gestalt, Von Restorff, Jakob, Miller, Goal-Gradient, Zeigarnik, Tesler, Peak-End, Postel, Doherty, Serial Position, Occam, and Parkinson laws.
license: Complete terms in LICENSE.txt
---

# Frontend Law Auditor

Use this skill to detect whether a frontend actually follows human-centered design laws, not just visual trends.

## When to Apply

Apply this skill when the user asks to:
- review frontend usability or UX quality
- diagnose drop-offs in onboarding/signup/checkout flows
- build a launch gate for design quality
- evaluate whether UI follows psychology-based design principles
- produce a remediation plan with measurable acceptance criteria

Skip when the task is purely backend/infrastructure with no user interface impact.

## Mandatory Workflow

Always follow this sequence.

1. **Collect evidence**
- Screenshots or recordings for key flows (signup, checkout, search, settings).
- Interaction timings and loading states.
- Form validation behavior and error messaging.
- Navigation/action layout for first and last positions.

2. **Initialize a metrics template**
- Run:
```bash
python scripts/law_audit.py --init-template /tmp/frontend-evidence.json
```
- Fill measured values in the generated JSON file.

3. **Run audit**
- Run:
```bash
python scripts/law_audit.py --input /tmp/frontend-evidence.json --output /tmp/frontend-audit.md --json-out /tmp/frontend-audit.json
```
- For CI-style gating:
```bash
python scripts/law_audit.py --input /tmp/frontend-evidence.json --strict --fail-threshold 85
```

4. **Interpret results using two layers**
- **Layer A: Fast gate** (binary pass/fail checks).
- **Layer B: Deep law analysis** (cause-based diagnosis per principle).
- For each failed principle, open its mapped rule file under `rules/`.

5. **Produce fix backlog**
- Sort by severity and expected impact on completion/conversion.
- Provide concrete acceptance criteria per fix.

## Output Contract

For every audit, output in this shape:

1. **Fast Gate Failures**
- Only failed checks with direct evidence.

2. **Law Diagnosis**
- `Principle -> Observed friction -> Why it happens (theory) -> UI change`.

3. **Priority Fix Plan**
- P0/P1/P2 buckets with measurable thresholds (target size, feedback ms, choice count, etc.).

4. **Recheck Checklist**
- What must pass in the next audit run.

## Evidence Requirements

Minimum evidence for a valid audit:
- target size and reachability data for critical actions
- choice density and progressive disclosure status
- progress visibility for multi-step flows
- validation behavior and error specificity
- interaction acknowledgment timing (p95 ms)
- completion-state quality (end feedback)

If evidence is incomplete, explicitly list missing keys and mark affected laws as `unknown`.

## References

Load only what you need:
- `rules/_sections.md` for full rule index and priority groups
- `rules/<law>.md` for implementation-level diagnosis and fixes
- `references/metrics-schema.md` for metric definitions and thresholds
- `references/theory-playbook.md` for deep principle explanations and fixes
- `examples/evidence.sample.json` for input format

## Notes

- Use this skill as a detector and decision aid, not as a replacement for product judgment.
- If laws conflict, prioritize task completion and safety-critical clarity first.
