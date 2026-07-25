# Model Tiering (#517)

Opt-in routing of ARS agents to different model tiers, exploiting intelligence asymmetry across pipeline tokens (Lance Martin, "Cost effective harnesses with Fable", 2026-07-10: an advisor-checkpoint configuration reached ~90% of frontier-solo quality at ~34% of token cost; delegation pays only when workers absorb enough tokens to offset the per-handoff coordination cost).

**This is entirely optional.** When `ARS_MODEL_TIERING` is absent, every agent runs on the session model (`model: inherit`) — byte-equivalent to pre-#517 behavior. Same opt-in philosophy as `terminal_policies`: absence of the switch means nothing changes.

## The switch

```bash
# Pick ONE direction, or leave unset (default: session model everywhere).
export ARS_MODEL_TIERING="economy"        # frontier session: execution agents step down one tier (floor: Opus-class)
export ARS_MODEL_TIERING="quality-boost"  # below-frontier session: judgment agents step UP to the frontier tier at the gates
```

Any other value is warned once (one line) and treated as absent — misconfiguration must never silently change models.

## Relative tiers, never hard-pinned ids

Tier positions are expressed relative to the session: "session model", "frontier tier of the session's model family", "one tier below the session model", "the Opus-class floor". Concrete model ids are NEVER pinned in this mechanism's FILES — a hard-pinned floor becomes a downgrade ceiling on the next model generation (the v3.7.0 `opus` command floor, retired in the 2026-06 Fable 5 harness pass, is the precedent).

### Resolving a tier at dispatch time

The no-hard-pinning rule is about what lives in the repo, not about the dispatch call — a subagent invocation ultimately needs a model value the runtime accepts (an alias such as `opus`/`sonnet`, or a concrete current-generation id). The dispatching session resolves the relative target at the moment of dispatch:

1. Determine the session's model family and current-generation lineup (from the runtime's own model information — never from a list stored in this repo).
2. Map the direction to a target: `economy` → the tier exactly one below the session model, bounded below at the Opus-class tier; `quality-boost` → the family's frontier tier.
3. Pass whatever identifier the runtime accepts for that target (alias preferred where supported; otherwise the current generation's concrete id). The concrete value exists only in that ephemeral call — it is never written into agent files, manifests, or this doc.
4. If the session cannot resolve the target (unknown lineup, runtime exposes no model choice): the direction is a no-op for that call — announce `[MODEL-TIERING: could not resolve target tier — ran on the session model]` once per run. Fail-open, never a guessed id.

## Direction 1 — `quality-boost` (for sessions below the frontier tier)

- **Who:** judgment-type agents (table below) **when dispatched at a checkpoint surface**: the Stage 2.5 / 4.5 integrity gates (`integrity_verification`, `compliance_agent`); the Stage 4→5 claim–ref alignment audit (`claim_ref_alignment_audit` — dispatched only when `ARS_CLAIM_AUDIT=1`, so this surface exists only on opted-in runs); and the final-review surfaces (Stage 3 full panel: `eic`, the three reviewers, `devils_advocate_reviewer`, `editorial_synthesizer`; Stage 3' re-review dispatches the narrow team — among its judgment-type roles that means `eic` + `editorial_synthesizer`; `field_analyst` is execution-type and unaffected here).
- **What:** dispatch those calls AT the frontier tier of the session's model family — a jump to the frontier, however many tiers away the session sits, not a single-increment step. Everything else stays on the session model.
- **Why there:** the measured value of a stronger model concentrates at mid-task re-ranking and verification, not upfront planning.
- **No-op condition:** a session already at the frontier tier has nothing to upgrade to — announce `[MODEL-TIERING: quality-boost is a no-op at the frontier tier]` once and proceed. quality-boost NEVER downgrades anything.

## Direction 2 — `economy` (for frontier-tier sessions)

- **Who:** execution-type agents (table below), at every dispatch.
- **What:** dispatch exactly ONE tier below the session model, **floor: the Opus-class tier, never Sonnet-class**. Judgment-type agents stay on the session model. This is a documented quality-for-cost trade: the ~90%/34% numbers above came from ML-tuning tasks, not scholarly writing, and academic-prose tolerance is untested — hence the conservative floor.
- **No-op condition:** a session already at or below the Opus-class floor has nowhere lower to go — announce `[MODEL-TIERING: economy is a no-op at or below the floor]` once and proceed. economy NEVER touches judgment-type agents.
- **Highest-risk downgrade:** `draft_writer` is the suite's highest-token and therefore highest-savings agent, and also its most quality-sensitive downgrade point (it writes the prose the whole pipeline exists to produce). The one-tier floor bounds the risk; if measured quality degrades, the remedy is reclassifying it to judgment-type in `scripts/model_tiering_manifest.json` + this table — one place, no agent-file edit.

## Where the decision is made

A different tier is physically selectable only where a role runs as a **separate subagent** (the built-in Agent tool's `model` parameter, or a plugin-exposed agent). Today many ARS roles execute **inline** in the main session as prompt templates (see `docs/PERFORMANCE.md` § "v3.7.0 Plugin agents and model routing") — inline execution has no per-role model choice. The mechanism therefore works like this:

- **Flag unset:** nothing changes — roles execute exactly as they do today (inline or subagent, session model). No role is spun out, no dispatch shape changes; byte-equivalent.
- **A direction applies to a role:** the session dispatches that role as a subagent pinned to the target tier — including roles that would otherwise have executed inline (the dispatch-as-subagent IS the mechanism for them).
- **Dispatching as a subagent is not possible in the runtime** (no Agent tool available, or the role's step is inseparable from the main conversation): the role runs inline on the session model and the direction is a no-op for that call — announce `[MODEL-TIERING: <role> ran inline on the session model — tiering not applicable]` once per run. Fail-open, never a silently wrong model claim.

Agent files are untouched — frontmatter stays `model: inherit`, and this mechanism never edits an agent file (the sha256-locked `bibliography_agent.md` included). The machine-readable classification lives in `scripts/model_tiering_manifest.json`; `scripts/check_model_tiering.py` fails CI when an agent file exists without a classification (drift guard), when a tier value is invalid, or when this table and the manifest disagree.

## Prompt-caching guidance (article item 4)

When a tiering direction is active, route repeated same-stage calls to the SAME worker so its cache accumulates — e.g. across the Stage 3 → 3' review loop, the re-dispatched roles (the narrow re-review team: `field_analyst`, `eic`, `editorial_synthesizer` — not the full panel) should reuse their Stage 3 workers rather than spawning fresh ones per round. The reuse rule is tier-independent: it covers `field_analyst` (execution-type, the affected role under `economy`) exactly as it covers the two judgment-type roles. A fresh worker per call re-pays the full context write and can erase the tiering savings entirely. With the flag unset this guidance imposes nothing: default behavior stays byte-equivalent, dispatch shapes included.

## Classification table (39 agents; frozen 2026-07-11, #517)

One tier per agent; membership changes require editing BOTH this table and `scripts/model_tiering_manifest.json` (the lint pins them together).

### Judgment-type (26) — session model; quality-boost upgrade candidates at checkpoint surfaces

| Skill | Agents |
|---|---|
| deep-research (10) | `socratic_mentor`, `research_question`, `research_architect`, `synthesis`, `devils_advocate`, `editor_in_chief`, `ethics_review`, `risk_of_bias`, `meta_analysis`, `source_verification` |
| academic-paper (6) | `socratic_mentor`, `argument_builder`, `structure_architect`, `peer_reviewer`, `revision_coach`, `literature_strategist` |
| academic-paper-reviewer (6) | `eic`, `methodology_reviewer`, `domain_reviewer`, `perspective_reviewer`, `devils_advocate_reviewer`, `editorial_synthesizer` (mechanical by v3.6.2 design but emits the final decision letter — judgment-type conservatively until data says otherwise) |
| academic-pipeline (3) | `pipeline_orchestrator`, `claim_ref_alignment_audit`, `integrity_verification` |
| shared (1) | `compliance` (holds tier-based block authority) |

### Execution-type (13) — economy-direction downgrade candidates (one tier, floor Opus-class)

| Skill | Agents |
|---|---|
| deep-research (4) | `bibliography` (citation existence is handled by the deterministic verification gate, so the lookup layer does not depend on this agent's tier), `timeline_extraction`, `report_compiler`, `monitoring` |
| academic-paper (6) | `intake`, `draft_writer` (highest-savings / most quality-sensitive — see Direction 2), `abstract_bilingual`, `citation_compliance`, `visualization`, `formatter` (STAMP-ONLY by design) |
| academic-paper-reviewer (1) | `field_analyst` |
| academic-pipeline (2) | `collaboration_depth` (advisory-only, never blocks), `state_tracker` |

## Interaction with cross-model verification

Orthogonal layers: `ARS_CROSS_MODEL` chooses an EXTERNAL verifier for specific checks (see `shared/cross_model_verification.md`); `ARS_MODEL_TIERING` chooses which Anthropic tier runs each ARS agent. They compose without coordination — e.g. an economy session still sends cross-model integrity samples if `ARS_CROSS_MODEL` is set, and the #518 blind disagreement checkpoints compare against the primary decision whatever tier produced it.
