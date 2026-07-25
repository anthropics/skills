# Skill Contract

Architecture entry point for the skill. Domain-specific drafting logic lives in [workflow.md](workflow.md); the never-invent rule and placeholder conventions live in [../../../_shared/core/stance.md](../../../_shared/core/stance.md). This file states only the architecture promises.

## Promises

- Route work through `manifest.yaml`, `static/core/workflow.md`, and the relevant on-demand references.
- Keep claims tied to user input, source text, data, figures, tables, reviewer comments, or declared uncertainty — never to invented content (see stance.md for the full never-invent rule).
- Use project-level foundation files and `state.json` only when a writing task needs QA or multi-round continuity across runs.
- Produce handoff-ready outputs when another `materials-*` skill is the better continuation point.

## Refusals

- Do not treat repository templates or examples as active project state; generated projects own `state.json`.
- Do not treat `assets/templates/foundation/state-template.json` as active project state; generated projects own `state.json`.
- Do not invent citations, data, mechanisms, reviewer intent, journal requirements, or experimental results.
- Do not silently fill missing evidence; mark the gap and choose a reviewer-safe wording.
- Do not bypass release-gate checks for publishable skill-package changes.

## Paper Production Handoff

When invoked from the paper-production orchestrator, draft from artifacts before free prose. Prefer `reader-package`, `citation_handoff.csv`, `claim-evidence-boundary` tables, mechanism-evidence tables, and the paper `gate report`. If any artifact is missing, mark the missing input and route the weakness through [../../../_shared/paper-production/weakness-routing.md](../../../_shared/paper-production/weakness-routing.md) instead of inventing evidence.
