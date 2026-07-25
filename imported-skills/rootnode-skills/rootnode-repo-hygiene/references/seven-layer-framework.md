# Seven-Layer Framework

The 7-layer decomposition model and the leak-check procedure for detecting placement violations across a CC environment.

**Canonical sources:**
- `root_CC_ENVIRONMENT_GUIDE.md §1` — the 7-layer model in detail with placement rules per layer
- `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.1 + §4.2` — placement discipline and decomposition by mechanism

This file applies the canonical content to leak-check execution. It does not duplicate the canonical layer definitions; it cites them and applies the model to detection.

---

## The 7 layers

The mechanisms that compose a CC environment, each with a distinct role. Misplaced content is the dominant CC failure mode — the decomposition framework is the diagnostic.

| # | Layer | Right placement | Common misplacement |
|---|---|---|---|
| 1 | Stable always-relevant facts | CLAUDE.md | Buried in Skills, missing entirely, scattered in chat handoffs |
| 2 | File-pattern-specific conventions | `.claude/rules/` with `paths:` frontmatter | Crammed into CLAUDE.md (bloat) |
| 3 | Reusable multi-step procedures | Skills (`.claude/skills/`) | In CLAUDE.md (bloat) or in legacy slash-command files |
| 4 | Focused specialists with isolated context | Subagents (`.claude/agents/`) | In main conversation prompts |
| 5 | Lifecycle guarantees | Hooks (in `.claude/settings.json`) | In CLAUDE.md as "remember to..." (unreliable) |
| 6 | External data and APIs | MCP servers | Pasted into context manually each session |
| 7 | Trust and permission boundaries | `settings.json` + permission modes | Asked to Claude as a prompt instruction |

Layer-by-layer detail lives in `root_CC_ENVIRONMENT_GUIDE.md §1`. The summary above is sufficient for leak-check execution; consult the canonical when a placement decision needs full context.

---

## Why the model is the master diagnostic

When a CC deployment exhibits behavioral problems — Claude forgets a rule, a guarantee fails to hold, a procedure runs inconsistently — the proximate symptom usually points at one specific instruction or rule. The structural cause is almost always upstream of that: the content was placed in a layer that doesn't enforce the guarantee the author wanted.

CLAUDE.md text is preference. Only hooks enforce. `.claude/rules/` content only loads when its `paths:` pattern matches. Skills only activate when their description triggers. Subagents only run when explicitly delegated to. Each layer has a contract; misplaced content silently violates the contract.

The leak-check walks the layers and asks: for each piece of content, is it in the layer whose contract supports it? When the answer is no, the finding is a "leak" — content that belongs in another layer.

---

## Leak-check procedure

Run as a cross-category analytical pass after the 14-category sweep completes. The pass operates on the same evidence the categories produced, but applies the structural lens.

**Step 1 — Inventory standing context.** Read CLAUDE.md fully. Read all `.claude/rules/*.md` files. Read all SKILL.md files in `.claude/skills/`. Read subagent definitions in `.claude/agents/`. Read hook configurations in `.claude/settings*.json`. Read MCP server declarations.

**Step 2 — For each piece of content, ask the placement question.** Walk the inventory. For each instruction, rule, procedure, or guarantee, ask:
- "What is this trying to do?"
- "Which layer's contract supports that?"
- "Is the content in that layer?"

When the content is NOT in the layer whose contract supports it, surface a leak finding.

**Step 3 — Apply the layer-pair tests.** Six common leak shapes to test explicitly:

1. **CLAUDE.md → `.claude/rules/`.** Any conditional content in CLAUDE.md ("when editing X files...", "in the Y directory...") is a leak. The conditional makes it not-always-relevant; `.claude/rules/` with `paths:` is the right home.

2. **CLAUDE.md → Skills.** Any multi-step procedure in CLAUDE.md (more than 3 sequential steps, especially when the steps reference each other) is a leak. Skills are the procedure layer.

3. **CLAUDE.md → hooks.** Any "remember to...", "always do X", or "before/after Y" instruction that describes a lifecycle guarantee is a leak. CLAUDE.md preference does not enforce. Hooks do.

4. **CLAUDE.md → MCP.** Any externally-sourced reference data pasted in (API documentation excerpts, third-party tool schemas) is a leak. MCP is the integration layer.

5. **Skills → hooks.** A Skill that describes a guarantee its caller must remember to invoke is a leak. The guarantee belongs in a hook that fires automatically.

6. **`.claude/rules/` → Skills.** A `.claude/rules/` file that contains a multi-step procedure rather than file-pattern conventions is a leak. The procedural content belongs in a Skill.

**Step 4 — Surface findings in the report.** Each leak gets an `L-{n}` finding with the format below. Findings appear in their own "7-Layer Leak Findings" section near the end of the report.

---

## Leak finding format

```
L-{n}  [layer: <1-7>]
  Current placement: <CLAUDE.md | rules | Skills | subagents | hooks | MCP | settings>
  Recommended placement: <target layer>
  Evidence: <quoted content with location>
  Recommended extraction: <one-sentence procedure for moving the content>
```

The `layer:` tag references the target layer (where the content belongs), not the source layer.

**Example:**

```
L-1  [layer: 5]
  Current placement: CLAUDE.md (line 47)
  Recommended placement: hooks
  Evidence: "Remember to run npm test after every edit; if tests fail, fix before continuing."
  Recommended extraction: Add a Stop hook in .claude/settings.json that runs `npm test` and surfaces failures before session close.
```

---

## Routing rules

7-layer leak findings are recommendation-only at Phase 2. They route to `rootnode-cc-design` REMEDIATE mode rather than executing directly via the Skill's Phase 2 batch system.

**Why recommendation-only.** Leaks are structural changes — file moves, mechanism migrations, refactors. Each leak's fix requires anti-pattern-aware fix-recipe derivation and 7-layer placement validation, which is the value REMEDIATE provides. Direct Phase 2 execution would treat the leak as a single edit when it's an environment change.

**When the active profile has `remediate_routing: true` (default).** Phase 1 includes the leak findings in the "Routing recommendations" section alongside Cat 11–14 findings. The recommendation language names REMEDIATE handoff explicitly.

**When the active profile has `remediate_routing: false`.** Leak findings remain in the report under their own section but no automated downstream pathway is named. The user is responsible for acting on them manually.

**Phase 2 behavior on `[APPROVED]` markers in leak findings.** Phase 2 surfaces a notice naming the marked leaks and recommends REMEDIATE handoff. The marker is preserved in the report (it documents user intent) but does not flow into a Phase 2 execution batch.

---

## Profile gating

The 7-layer leak check runs only when the active profile has `include_seven_layer_leak_check: true`.

- `default` profile — leak check enabled.
- `quick-scan` profile — leak check disabled (fast triage scope).
- `deep-audit` profile — leak check enabled.

Custom profiles can enable or disable per the use case.

---

## Common leak patterns observed in production

These patterns surface frequently in CC deployments that have evolved past their initial configuration:

- **CLAUDE.md absorbing rules** as the project added file types or directories. Each addition was small in isolation; over time, CLAUDE.md becomes the everything-document. Targets `.claude/rules/`.

- **Verification-as-preference** ("remember to run tests") in CLAUDE.md when test infrastructure already exists. Targets a Stop hook.

- **Procedural drift into CLAUDE.md** when a multi-step workflow was discovered during a session and added to CLAUDE.md "for next time" rather than extracted to a Skill.

- **MCP-shaped content pasted manually** when the author didn't realize MCP could fetch the same data on demand.

- **Subagent scope mixing into main** when high-token subtasks were never delegated and accumulated as inline patterns.

The `cc-best-practices.md` reference cross-walks each of the 12 convergence patterns to its target layer; consulting that file alongside this one provides the full layer-fit picture.

---

*End of seven-layer framework. Layer detail in `root_CC_ENVIRONMENT_GUIDE.md §1`. Placement discipline in `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.1 + §4.2`.*
