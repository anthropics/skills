# Ecosystem Placement Decision

**Canonical source:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6` (the runtime tooling catalog and CP-side / CC-side split) and `§6.3` (the layer-fit boundary — governance Skills vs. workflow systems).

This reference is a Skill-internal application of the canonical placement framework. Gate 3 answers two questions: (1) Where does this Skill sit in the rootnode runtime tooling map — CP-side or CC-side, and what does it compose with? (2) Does this Skill fill a clear gap, or duplicate existing capability?

The Skill applies this reference at Gate 3 (after Gates 1 and 2 have passed) and at validation dimension 7 when scanning the produced Skill against ecosystem composition.

If the canonical KF section evolves (new Skills added to the catalog, layer-fit boundary refined, surface taxonomy updated), regenerate this reference. The cross-reference anchors above are the propagation hooks.

---

## Why Gate 3 exists

A Skill that passes Gates 1 and 2 (correct mechanism, warranted abstraction) can still be the wrong build if it duplicates existing capability or sits awkwardly in the surface taxonomy. Three failure modes Gate 3 prevents:

1. **Routing collisions.** Two Skills with overlapping descriptions compete for activation. Even with negative triggers, the user gets unpredictable behavior. Better to extend the existing Skill than ship a competitor.

2. **Surface mismatch.** A Skill built CP-side that should have been CC-side never reaches the deployment context where it would be useful (or vice versa). Surface choice is structural, not stylistic.

3. **Layer-fit miscategorization.** A Skill built as governance/runtime tooling that should have been a workflow system (or vice versa) sits at the wrong abstraction level. Per `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6.3`: rootnode runtime Skills are governance over thick workflow systems, not replacements for them. Get this wrong and the Skill either over-prescribes (fails to compose) or under-prescribes (fails to govern).

---

## CP-vs-CC decision tree

The first placement decision is surface: does this Skill belong on the chat side (CP — runs in Claude Project conversations) or the code side (CC — deploys to delivery project repositories)?

Walk this sequence:

1. **Is the work design-heavy / methodology-grounded / cross-project governance?** → CP-side. Examples: prompt design, project audit, methodology validation, cross-project context bridging.

2. **Is the work project-specific / deployment-local / filesystem-bound?** → CC-side. Examples: repo hygiene scans, file-pattern enforcement, build/test/deploy workflows, local execution in a specific codebase.

3. **Is the work both — design-heavy AND deploys to a specific repo?** → Bridge case. Build CP-side; specify CC handoff in the procedure. The Skill itself runs CP-side; its outputs may be artifacts the user takes to CC for execution.

4. **Is the work surface-agnostic — runs identically on either side?** → Default CP-side. CP is the more general environment; surface-agnostic Skills find more activation surface there.

The decision tree is not a hard rule — it's a default assignment. Override with reasoning if the specific Skill has structural reasons to sit on the other side.

---

## Current rootnode Skill inventory (snapshot)

The catalog as of v2 build. Update in `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6` when this snapshot drifts; this reference should be regenerated when the canonical updates.

### CP-side methodology Skills

| Skill | Surface | Composes with |
|---|---|---|
| `rootnode-prompt-compilation` | CP | block libraries, domain packs, prompt-validation |
| `rootnode-prompt-validation` | CP | prompt-compilation (downstream review) |
| `rootnode-project-audit` | CP | memory-optimization, anti-pattern-detection, behavioral-tuning, context-budget |
| `rootnode-anti-pattern-detection` | CP | project-audit (called by it) |
| `rootnode-behavioral-tuning` | CP | project-audit (called by it) |
| `rootnode-memory-optimization` | CP | project-audit (called by it) |
| `rootnode-context-budget` | CP | project-audit (called by it) |
| `rootnode-global-audit` | CP | full-stack-audit |
| `rootnode-full-stack-audit` | CP | project-audit + global-audit (orchestrates) |

### CP-side block library Skills

| Skill | Surface | Composes with |
|---|---|---|
| `rootnode-identity-blocks` | CP | block-selection, prompt-compilation |
| `rootnode-reasoning-blocks` | CP | block-selection, prompt-compilation |
| `rootnode-output-blocks` | CP | block-selection, prompt-compilation |
| `rootnode-block-selection` | CP | identity/reasoning/output-blocks (router) |

### CP-side domain pack Skills

| Skill | Surface | Composes with |
|---|---|---|
| `rootnode-domain-business-strategy` | CP | prompt-compilation |
| `rootnode-domain-software-engineering` | CP | prompt-compilation |
| `rootnode-domain-content-communications` | CP | prompt-compilation |
| `rootnode-domain-research-analysis` | CP | prompt-compilation |
| `rootnode-domain-agentic-context` | CP | prompt-compilation |

### CP-side build/utility Skills

| Skill | Surface | Composes with |
|---|---|---|
| `rootnode-skill-builder` | CP | builds all rootnode Skills (this Skill) |
| `rootnode-profile-builder` | CP | profile-shaped JSON config consumers |
| `rootnode-handoff-trigger-check` | CP | handoff readiness evaluation pre-CC |
| `rootnode-project-brief` | CP | cross-project context generation |
| `rootnode-session-handoff` | CP | session continuation artifacts |
| `drayline-ecosystem` | CP (context carrier) | Drayline-aware Skill activations |

### CC-side runtime Skills

| Skill | Surface | Composes with |
|---|---|---|
| `rootnode-cc-design` | CP+CC (CP for design, CC for REMEDIATE mode) | repo-hygiene (REMEDIATE consumes hygiene reports) |
| `rootnode-repo-hygiene` (planned, v1 in build) | CC | cc-design REMEDIATE mode |
| `rootnode-critic-gate` | CC | governance over CC workflow systems |
| `rootnode-mode-router` | CC | governance over CC workflow systems |

A Skill being designed enters this map at one of these slots — or identifies a clear gap. If the new Skill duplicates an existing slot, Gate 3 surfaces the duplication and recommends extending the existing Skill instead of shipping a competitor.

---

## Composition patterns

Three patterns describe how rootnode Skills compose:

**Pattern A — Orchestrator + specialists.** One Skill orchestrates; others are specialists it calls. Example: `rootnode-project-audit` orchestrates; `anti-pattern-detection`, `behavioral-tuning`, `memory-optimization`, `context-budget` are specialists it dispatches to. The orchestrator's description doesn't duplicate the specialists' triggers — it activates on the orchestration surface ("audit my project") and the specialists' activations cascade.

**Pattern B — Router + libraries.** One Skill routes between options; others provide the option content. Example: `rootnode-block-selection` routes; `identity-blocks`, `reasoning-blocks`, `output-blocks` are the libraries it routes to. The router's description handles "help me choose"; the libraries handle "give me the X approach."

**Pattern C — Producer + consumer.** One Skill produces an artifact; another consumes it. Example: `rootnode-repo-hygiene` produces a hygiene report; `rootnode-cc-design` REMEDIATE mode consumes it. Or: a Skill following the process-abstraction handoff brief format produces a brief; `rootnode-skill-builder` v2 consumes it (Gate 2 auto-pass).

When designing a new Skill, identify which composition pattern it fits — and which existing Skills it composes with under that pattern. The build summary surfaces the composition map.

---

## Layer-fit boundary

Per `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6.3`: rootnode runtime Skills are **governance over thick workflow systems**, not replacements for them.

The distinction matters because it determines what the Skill does and doesn't include:

- **A workflow system** is a thick procedural framework — n8n, an audit pipeline, a build/test/deploy chain. It defines the work end-to-end.
- **A governance Skill** is a thin layer that adds discipline, validation, or orchestration over a workflow system. It doesn't replicate the workflow; it shapes how the workflow runs.

Examples:

- `rootnode-critic-gate` is governance, not a workflow system. It adds critic-style review at gates within a CC workflow; it doesn't replace the workflow itself.
- `rootnode-mode-router` is governance, not a workflow system. It routes between modes within a CC workflow; it doesn't define the modes' contents.
- `rootnode-repo-hygiene` is governance + scan, not a workflow system. It applies the hygiene catalog as a scan over an existing repo; it doesn't define the repo's structure.

**Anti-example:** A Skill that tries to be "the complete CC build pipeline" is a workflow system masquerading as governance. It either fails to compose with actual workflow systems users have, or duplicates them and creates conflict.

When designing a new Skill, ask: am I building governance, or am I building a workflow system? If governance, the scope is thin and the Skill composes with existing thick systems. If workflow, the scope is thick and the Skill is probably better as a different mechanism (a project template, a CC repo scaffold, an MCP server) than as a Skill.

---

## Duplication detection signals

Watch for these signals that the new Skill duplicates existing capability:

- **Description vocabulary overlap.** The new Skill's description uses the same trigger phrases as an existing Skill. Even with negative triggers, this creates routing collisions. Recommend extending the existing Skill.
- **Composition map overlap.** The new Skill composes with the same set of Skills as an existing Skill, in the same way. The two are doing the same job from different angles. Pick one.
- **Output overlap.** The new Skill produces the same artifact shape as an existing Skill. The artifact is the work; whoever produces it owns the territory.
- **Trigger surface overlap.** The new Skill activates on the same conversation contexts as an existing Skill. If the user can't tell which Skill should fire, neither can Claude.

When duplication is detected, surface to the user with three options:

1. **Extend the existing Skill** to cover the new use case. Usually the right move — preserves ecosystem cleanliness.
2. **Ship the new Skill with sharp negative triggers** to prevent collision. Sometimes warranted when the use cases are genuinely distinct despite overlap; rarely the best move.
3. **Don't ship the new Skill.** The use case is already covered by the existing Skill; the new build is unnecessary.

---

## Placement note format

When Gate 3 passes (clear gap or accepted extension/duplication reasoning), v2 produces a placement note artifact: `{skill-name}_placement.md`. This artifact ships with the build output and surfaces in the build summary as a recommendation for the user to update `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`.

### Format

```markdown
# Placement Note: {skill-name}

**Surface:** CP | CC | CP+CC
**Composition pattern:** Orchestrator | Specialist | Router | Library | Producer | Consumer | Standalone
**Layer fit:** Governance | Workflow

---

## Composes with

[List of existing rootnode Skills this Skill composes with, and how]

## Fills which gap

[2-3 sentences describing the capability gap this Skill fills, and why
existing Skills don't already cover it]

## Suggested catalog entry for `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`

```
| `{skill-name}` | {surface} | {composes-with-summary} |
```

## Migration / extension considerations

[If this Skill replaces or extends an existing Skill, document what
changes for users. If standalone, mark "N/A".]
```

The user applies the catalog entry to `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6` as a separate edit. v2 doesn't auto-edit canonical KFs — methodology updates remain human-reviewed (per locked decision #5 in the design spec).

---

## What this reference does not do

This reference doesn't decide whether the work fits the Skill mechanism (Gate 1) or whether the abstraction is warranted (Gate 2). Gate 3 assumes both have passed.

This reference doesn't define the runtime tooling catalog itself — that's `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`. This reference applies the catalog to the placement decision.

This reference doesn't replace cross-Skill validation at the ecosystem level (e.g., periodic full-catalog audits for routing collisions across all rootnode Skills). It catches single-Skill placement issues at build time; ecosystem-wide health is a separate audit surface.
