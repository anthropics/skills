---
name: materials-writing
version: "1.3.0"
description: Use when drafting, restructuring, auditing, or statefully revising manuscripts for materials science and engineering research.
---

# Materials Science Writing

Use this skill as an evidence-first router for bounded materials-science
manuscript prose. It locks terminology, builds an argument chain, maps
paragraph messages, confirms the plan for complete sections, and keeps missing
evidence visible.

## Architecture

- `static/` contains reusable contracts, workflow rules, and routed fragments.
- `manifest.yaml` declares the routing axes, default core, on-demand references,
  assets, scripts, and handoffs.
- `references/` is not default context; load only the paths selected by the
  manifest or required by the task.

## Routing protocol

1. Read `manifest.yaml`, then load the four files under `always_load`:
   `contract.md`, `direction-profile.md`, `workflow.md`, and `output-format.md`.
2. Apply profile precedence:
   explicit direction in the request > saved `.materials/profile.yaml` >
   neutral/general fallback. Resolve `material_family` and `domain` only after
   the profile is known.
3. Detect `paper_type`, `section`, `language`, `journal_family`,
   `material_family`, `domain`, and `input_source` from the request. Ask only
   when ambiguity changes the output structure.
4. Classify the job as a local edit, drafting, targeted revision, or
   QA/multi-round revision. Load `content-first-qa-pipeline` and the relevant
   state-machine references only for QA or continuity work.
5. For each selected axis, read the mapped path declared in `manifest.yaml`;
   do not infer its contents from trigger words. Load only selected fragments
   and required on-demand references.
6. Follow `static/core/workflow.md` and return the structure in
   `static/core/output-format.md`.

## Blocking invariant

Do not invent citations, data, mechanisms, reviewer intent, journal
requirements, experimental results, or completed actions. When evidence is
missing, use a visible `[TO CONFIRM: ...]` or `[needs evidence: ...]` marker,
record it under `Assumptions`, and route the missing input instead of filling
the gap with confident prose.

## Handoffs

- `materials-reader`: route source-paper-intensive reading to `materials-reader`; consume
  `reader-package` and `source_map`.
- `materials-citation`: emit a claim-evidence-boundary table for citation
  mapping.
- `materials-doe`: route experiment-matrix or factor-design requests to `materials-doe`;
  consume `doe-handoff` to align factors and responses with manuscript claims.
- `materials-polishing`: pass the draft, claim-evidence map, and terminology
  ledger without weakening evidence boundaries.

When a handoff artifact is missing, use
`../_shared/paper-production/weakness-routing.md`; never invent the artifact.

## Scope

This skill drafts and audits bounded manuscript content. It does not replace
deep reading, real experimental evidence, official journal instructions, or
supervisor judgment.
