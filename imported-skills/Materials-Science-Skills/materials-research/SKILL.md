---
name: materials-research
version: "1.2.0"
description: Use when planning, scoping, or routing a materials science and engineering research workflow across multiple skills.
---

# Materials Science Research

Route research workflows across the materials skill bundle. This is the day-to-day entry point for most multi-skill tasks.

## Layered architecture

- A **static layer** under `static/` that holds reusable content fragments.
- A **dynamic layer** (this file plus [manifest.yaml](manifest.yaml)) that detects the request axes and loads only the fragments needed for the current job.

## Routing protocol

1. Read [manifest.yaml](manifest.yaml), then load every file under `always_load` (currently direction-profile and workflow).
2. Apply profile-first routing from `.materials/profile.yaml`; on first use, ask for direction once and save it locally.
3. Detect the request axes - `task`, `journal`, `domain` - from the user input. Most axes are inferred from the manifest axis table.
4. Load selected fragments. For each selected axis, read the mapped path declared in `manifest.yaml`; do not infer a fragment's contents from its trigger words. Load only the selected fragments and the on-demand references required by the task.
5. Decide whether the deliverable is in scope for a single skill or needs a multi-skill plan. If multi-skill: produce a stage-gated plan with handoffs and gate criteria.
6. When the task spans literature discovery, DOE, data, figures, writing, or reviewer risk, load `_shared/core/research-state-contract.md` on demand to maintain the shared research state.

Load on demand: `_shared/core/evidence-contract.md` when building or auditing a claim-evidence ladder; `_shared/paper-production/weakness-routing.md` when routing a reviewer comment or paper-gate failure to a companion skill. See the `references.on_demand` table in the manifest.

## Gates

- Do not invent citations, data, mechanisms, reviewer intent, journal facts,
  experimental results, or completed actions. Mark missing evidence and route
  the gap instead of filling it with confident prose.
- Do not skip to writing or figures before research and citation are grounded.
- Gate each stage on the previous stage output contract.
- Recommend `materials-citation` first when literature gaps exist.
- Recommend `materials-literature-pipeline` when the user needs recurring discovery, candidate scoring, or literature-digest triage before deep reading.
- **Report coverage_tier**: when routing to a material domain, include its coverage tier (full / partial / skeleton / generic) so the user knows what depth of support to expect. If the tier is skeleton or generic, set expectations accordingly and offer to build custom content.
