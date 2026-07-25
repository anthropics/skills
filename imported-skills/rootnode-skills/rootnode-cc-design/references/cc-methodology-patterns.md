# CC Methodology Patterns

> **Canonical sources:** `root_CC_ENVIRONMENT_GUIDE.md` (7-layer architecture, agent topology, scope authorization, halt-and-escalate). This reference is a Skill-internal application of those canonicals, framing each pattern in cc-design's Skill-build/use context. Because the Skill runs CP-side at design Projects and CC-side at delivery repositories where root.node KFs are not present at runtime, the reference is self-contained for operational execution but cites the canonical as source of truth, so canonical evolution regenerates this file.

Project-agnostic distillation of the methodology patterns this Skill applies. Drawn from accumulated experience designing Claude Code deployments and triangulated against Anthropic primary documentation. Each pattern includes a structural description, the failure mode it prevents, and a tagged exemplar from a working project where one is available.

This reference is the methodology grounding for DESIGN, EVOLVE, REMEDIATE, and TEMPLATE modes. Read it before producing any deployment plan, remediation plan, or audit verdict.

---

## Table of contents

1. The agent-warranted test
2. The authority matrix pattern
3. The scope-authorization framework
4. The 4-agent verification topology (S/B/C/X)
5. The change_log discipline
6. The test backstop discipline
7. Additive evolution with narrow detection
8. Halt-and-escalate trigger design
9. Files as primary context surface
10. The design brief workflow
11. Tagging discipline (generalizable vs. project-specific)

---

## 1. The agent-warranted test

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §3.1` (verification topology pattern + agent-warranted test).

Before recommending an agent topology, ask: does the work require multiple distinct cognitive perspectives running in parallel, or sequential decomposition with handoffs? If the work is a single-loop iteration (read, edit, verify, repeat), a single Claude Code session is the right architecture — adding sub-agents introduces coordination overhead without proportional benefit.

Subagents are a context-isolation primitive, not a multiplier. Anthropic's primary documentation states this directly: "flooding Claude with options makes automatic delegation less reliable." Practitioner consensus (rosmur/claudecode-best-practices, obra/superpowers, alexop.dev) reinforces the point: most teams settle on a handful of well-scoped agents rather than a sprawling roster. Default to the built-ins (Explore, Plan, general-purpose) and add custom subagents only when the warrant is clear.

**Signals that warrant a multi-agent topology:**
- Verification requires perspectives that conflict by design (structural correctness vs. visual quality vs. content fidelity)
- The work decomposes into independent units that parallelize, AND an implementation plan exists, AND tasks are mostly independent (the obra/superpowers threshold)
- A class of decisions requires independent re-derivation (Critic agent reviewing a change author's diagnosis)
- Research-heavy side tasks would flood main context with file contents not referenced again
- A task needs a fresh perspective uninfluenced by the implementation conversation

**Signals that don't warrant multi-agent:**
- "Coverage" — using more agents because more is better. This is anti-pattern.
- Tasks that scale sequentially (each step depends on the previous; parallel agents will block)
- Same-file edits — two subagents editing the same file in parallel is a recipe for conflict
- Single-perspective verification (one thorough audit beats four shallow audits)
- Small tasks where delegation overhead exceeds the benefit
- Work that requires agents to coordinate with each other directly (use agent teams instead — different mechanism)

**Apply this test in DESIGN mode** before recommending any agent topology. **Apply when reviewing topologies during EVOLVE or REMEDIATE work** — if a project has 5+ custom subagents, walk each against the warrant signals (the §4.5 subagent overuse fix recipe).

---

## 2. The authority matrix pattern

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §2.1` (R2 authority matrix as a required CLAUDE.md section).

Every Claude Code deployment has *some* content where the agent's authority must be bounded. The authority matrix defines those bounds explicitly. The structural pattern is three tiers:

| Tier | Authority |
|---|---|
| 1 — Source-only | Verbatim from canonical source. Zero authority to modify. If the source isn't available, content is omitted — never fabricated, never paraphrased. |
| 2 — Mirror-exact | Claude's authority, but must mirror canonical source exactly without rewording. Structural wrappers (section headers from source titles, anchor text). |
| 3 — Free design | Claude's free-range authority. UI chrome, transitional language, generated explanations. |

**The pattern is generalizable; the tier definitions are project-specific.** Examples beyond the original case (production CC deployment 2026-05-04):
- Production database schemas (mirror-only — exact match required)
- Customer-facing copy under brand approval (source-only or escalate)
- Generated code that must match an approved API contract (mirror-exact)
- Compliance text required by regulation (source-only)
- Auto-generated documentation indexed against committed source (mirror-exact)

**In every CLAUDE.md (R2 in the cc-environment-design-patterns reference):** identify the tiers for the specific project. The three-tier shape generalizes; the specific tier definitions are project-specific. Without an authority matrix, agents either over-edit (causing drift) or freeze on every content decision.

**Working example — production CC deployment 2026-05-04:** Tier 1 = verbatim source content (Q text, A text, prose, table cells from source documents). Tier 2 = section H2s from source titles, TOC anchor text, figcaptions from source cells. Tier 3 = toolbar labels, button text, keyboard shortcut overlay, generated intros. This was the load-bearing rule of the entire system; every engine fix in the documented evolution arc was checked against it. **[generalizable structure, project-specific content]**

---

## 3. The scope-authorization framework

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §4` (scope authorization).

Explicit in-scope and out-of-scope lists for autonomous iteration, with halt-and-escalate triggers when the agent approaches the boundary. Without this, the failure modes are:
- Over-editing — agent makes changes outside the intended scope, causing regressions
- Freezing on every decision — agent stops to confirm trivial choices, losing the leverage of autonomous iteration
- Silent boundary violation — agent edits something it shouldn't, doesn't surface, ships broken work

**Specify scope at three levels in every CLAUDE.md:**

**In-scope (autonomous, no confirmation needed):** Changes the agent can make without surfacing. Examples: bug fixes within an established subsystem, additive engine improvements with narrow detection, test additions, formatting/style fixes within agreed conventions.

**In-scope with notification (autonomous, but log the change prominently):** Changes the agent can make but must surface in the change log. Examples: cross-cutting refactors, new agent role additions, scope expansion proposals.

**Out-of-scope (halt and escalate):** Changes the agent must not make without explicit human authorization. Examples: authority matrix tier-1 boundary modification, schema contract changes between layers, deletion of test cases, `--force` operations, modifications to invariant infrastructure.

**See also:** The pre-execution version of this gate (deciding whether work is ready to hand off to autonomous execution at all) is implemented in the `rootnode-handoff-trigger-check` Skill if available. The per-change version (evaluating proposed changes during execution) is implemented in the `rootnode-critic-gate` Skill if available. Recommend either Skill only when the deployment has a specific need for that gate function.

---

## 4. The 4-agent verification topology (S/B/C/X)

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §3.1` (verification topology pattern; S/B/C/X is the canonical reference shape).

When verification requires conflicting perspectives, a four-agent topology — Structural Auditor, Behavioral Auditor, Content Fidelity Auditor, Cross-Verifier — catches different bug classes and reconciles findings. The Cross-Verifier role is structurally invariant across deployments. The other three are domain-substituted. **[generalizable]**

| Agent role | What it catches | Domain substitutions |
|---|---|---|
| Structural Auditor | Code structure / API contract / schema validity / HTML text-level assertions | Source code linting, schema validation, generated-output structure |
| Behavioral Auditor | Runtime behavior / integration tests / E2E flows / browser interaction | E2E test runner, integration suite, smoke tests |
| Content Fidelity Auditor | Data integrity / business logic correctness / spec compliance / verbatim source check | Domain-specific correctness assertions (e.g., medical fact verification, financial reconciliation, legal text match) |
| Cross-Verifier | Reconciles the above three; investigates conflicts | Reconciles the above three; role is invariant |

**Working example — production CC deployment 2026-05-04:** This topology shipped 27/27 ship items without a halt violation. The Cross-Verifier was the role that caught issues no single agent would have flagged — when the Structural Auditor said "PASS" but the Content Fidelity Auditor said "FAIL," the Cross-Verifier investigated the discrepancy and surfaced the root cause.

**When NOT to use:** If only one perspective is needed (e.g., a CLI tool with unit tests as the single verification surface), one thorough auditor beats four shallow ones. Apply the agent-warranted test (§1) before recommending S/B/C/X.

**Forward-looking expansion (recommend with caution):** Some deployments may benefit from adding Orchestrator + Critic + Scribe agents on top of S/B/C/X for goal decomposition, per-change governance, and institutional memory updates. This is a hypothesis, not a validated pattern. Recommend only when (a) multiple production runs per session require goal decomposition, (b) changes have high blast radius and per-change governance is needed, or (c) institutional memory updates are recurring overhead. Otherwise, the expansion is over-engineering. **[forward-looking proposal]**

---

## 5. The change_log discipline

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §5.1` (change_log discipline).

Every fix, every change, every notable decision gets an entry in `change_log.md`. The change_log is the durable institutional memory — every new agent reads it cold and inherits the full debugging arc. Agents that don't read the change_log re-diagnose solved problems and waste cycles.

**Format per entry:**
- WI / change identifier (e.g., `WI42` or `2026-05-04-fix-table-merge`)
- Subsystem affected
- Diagnosis (1-2 sentences: symptom + root cause)
- Fix (what code/config changed; narrow detection criteria)
- Verification (concrete metrics: before X, after Y)
- Regression sweep result (how many existing builds re-verified clean)

**Anti-pattern:** vague entries like "improved table parsing" without metrics. The change_log loses its diagnostic value when entries don't include the before/after.

**In every CLAUDE.md pre-flight checklist (R5):** "Read change_log tail before any change to a subsystem with prior fixes." This enforces the discipline at the agent-behavior level.

**Working example — production CC deployment 2026-05-04:** The change_log captured every WI fix in the documented evolution arc. New audit agents read it cold and inherited the full debugging arc — no re-diagnosing.

---

## 6. The test backstop discipline

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §5.2` (test backstop).

A pytest (or equivalent) suite that runs in <5 seconds and covers the high-risk patterns from the change_log. The test backstop catches accidental regressions before they ship — the most common Claude Code failure mode in extended sessions is the agent fixing one thing and breaking another silently.

**Pre-flight rule:** every agent runs the test backstop before any change, and re-runs it after. If the test count drops or any test fails after a change, the change is rejected and the agent re-derives.

**Working example — production CC deployment 2026-05-04:** 49 cases, 0.24s runtime, covering each WI plus invariants. The discipline caught regressions at multiple points during the documented evolution arc. **[generalizable]**

**For projects without unit-testable cores:** the backstop pattern still applies but the implementation differs. Examples: integration tests that exercise an end-to-end flow in <30s; a smoke-test script that verifies the build/deploy pipeline is healthy; a curated regression-fixture set with expected outputs. The point is a fast, automated check that runs before/after any agent change.

---

## 7. Additive evolution with narrow detection

**Canonical source:** `root_CC_ENVIRONMENT_GUIDE.md §5.3` (additive evolution with narrow detection).

Engine improvements are additive — they add a new code path gated by narrow detection criteria, rather than modifying an existing path. This produces monotonic improvement: every old artifact rebuilds byte-identical because the fixes only fire on the specific shape they target.

**The discipline:** when proposing a fix, design the detection criterion before designing the fix. The criterion should be specific enough that the fix only fires on the failure shape and never on the existing-passing cases. If the detection is broad, the fix has to be perfect; if the detection is narrow, the fix only has to handle the target case.

**Working example — production CC deployment 2026-05-04:** The documented evolution arc is monotonic improvement. Every engine fix landed alongside a regression sweep proving it didn't break the others. **[generalizable]**

**See also:** The detection-narrowness check is one of the four checks performed by the `rootnode-critic-gate` Skill if available. When a deployment uses critic-gate to govern autonomous engine evolution, this discipline is automatically applied per-change.

---

## 8. Halt-and-escalate trigger design

**Canonical source:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.7` (halt-and-escalate as a first-class discipline) + `root_CC_ENVIRONMENT_GUIDE.md §2.1` (R4 halt triggers in CLAUDE.md required sections).

Triggers are conditions, not preferences. Each trigger is a single concrete condition the agent can recognize unambiguously.

- Bad: "halt if something seems risky."
- Good: "halt if the change would modify any line containing the string `# AUTHORITY:` in a CLAUDE.md-flagged file."

Triggers must be verifiable from the agent's vantage point — conditions the agent cannot detect cannot be enforced.

**For guarantees that absolutely cannot be missed, back the trigger with a hook.** CLAUDE.md text alone is preference, not enforcement. See `cc-skills-and-hooks-composition.md` for the hooks-vs-prompts decision tree and the verification "iron law" pattern.

**Halt-trigger categories every CLAUDE.md should specify (R4):**
- Authority matrix tier-1 boundary approach
- Schema contract change between layers (e.g., extractor output ↔ generator input)
- Test count drops or test failure after a change
- Regression detected in a previously-passing build
- Ambiguity that cannot be resolved from CLAUDE.md alone
- Any operation requiring `--force` or equivalent destructive flag

**Working example — production CC deployment 2026-05-04:** Halt triggers were specified explicitly in CLAUDE.md §19.2 and the agent surfaced 0 halt violations across the 27/27 ship. Every fix's verification step proved the triggers held.

---

## 9. Files as primary context surface

**Canonical source:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.6` (files as primary context surface — surface-invariant principle) + `root_CC_ENVIRONMENT_GUIDE.md §5.5` (CC-side application).

Project decisions live in version-controlled files, not in chat history. The community phrase is "files as universal context": CLAUDE.md, PLANNING.md, SPEC.md, INITIAL.md, PRPs, AGENTS.md, change_log.md are the durable context layer. Chat is for transient ideation. **[generalizable]**

**The discipline:**
- Every decision worth carrying forward gets captured in a file before the chat window closes
- Plans and specs are markdown artifacts the agent reads, not paragraphs the agent infers from past conversation
- Compaction safety: project-root CLAUDE.md re-injects after `/compact`; nested files reload on demand. Conversation-only instructions are lost. If it matters, write it down.

**Anti-pattern named identically across multiple practitioner sources:** "transcript dump" — pasting chat history into Claude Code as a prompt. Always restructure into a spec file first. See `cc-anti-patterns.md` §4.1.

---

## 10. The design brief workflow

**Canonical source:** Skill-internal application of the methodology framework. The brief is a cc-design operational artifact, not a canonical KF concept.

The design brief is the grounding artifact for any non-trivial design work in this Skill. Without it, output drifts toward generic patterns. With it, every recommendation is grounded in the project's actual surface.

**Brief format:** Markdown with YAML front-matter. Lives at `{project_code}_design_brief.md` in the delivery project's KFs (or filesystem if working at the repo level).

```yaml
---
project_name: <name>
current_state: <greenfield | in-progress | shipped | maintenance>
tech_surface: [<tech1>, <tech2>, <tech3>]
governance_state:
  claude_md: <none | exists | needs-update>
  skills: <count>
  scope_rules: <none | partial | mature>
runtime_tooling:
  handoff_gate: <none | configured | active>
  critic_gate: <none | configured | active>
  mode_router: <none | configured | active>
authority_constraints: <free-text summary or "see brief body">
verification_surface: <free-text summary or "see brief body">
last_updated: YYYY-MM-DD
---

# Brief body

## Mission
<1-paragraph: what the project produces, who it's for, what "shipped" means>

## Authority constraints
<what the agent must NOT modify; tier 1 / tier 2 / tier 3 if applicable>

## Verification surface
<how is correctness checked: tests, manual review, LLM judge, etc.>

## Current state details
<more detail than the front-matter enum permits>

## Known friction or open questions
<things to surface in EVOLVE mode>
```

**The 5-question interview** (used to author a brief on first invocation):

1. **Mission.** "In one paragraph: what does this project produce, who is it for, and what does 'shipped' mean for it?"
2. **Current state.** "Where is the project now? Greenfield (no code), in-progress (under active development), shipped (in production with maintenance work), or maintenance (mostly stable, occasional fixes)?"
3. **Tech surface.** "What's the primary tech stack? Languages, frameworks, key dependencies, infrastructure platforms."
4. **Authority constraints.** "What MUST the agent never modify autonomously? Examples: production database schemas, regulated content, customer-facing copy, irreversible operations. Apply the 3-tier authority matrix pattern."
5. **Verification surface.** "How is correctness checked? Unit tests, integration tests, manual review, LLM judge, smoke scripts, runtime monitoring? Be specific — 'tests' is too vague."

**Brief refresh trigger:** if `last_updated` is > 90 days old, or if the front-matter enum values are wrong (e.g., brief says `current_state: greenfield` but the project has shipped), surface the staleness and offer to refresh.

**When to skip the brief:** small focused asks (one CLAUDE.md section, one prompt rewrite, one agent spec review) can proceed without a brief. The brief grounds multi-faceted design work, not single-shot questions. Use judgment.

---

## 11. Tagging discipline (generalizable vs. project-specific)

**Canonical source:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.4` (source authority hierarchy) + `§4.5` (generalizable-vs-specific tagging discipline).

Patterns drawn from working examples are tagged in every output as one of:

- **[generalizable]** — pattern works across CC work generally. Examples: 4-agent S/B/C/X verification topology, scope-authorization framework, change_log discipline, additive evolution with narrow detection, halt-and-escalate triggers, the agent-warranted test, files-as-context discipline, MCP minimalism.
- **[project-specific]** — pattern was specific to one project's domain. Default to "may be project-specific until proven otherwise." Generalization claims need a basis: name the structural feature that makes the pattern transfer beyond the original specifics.
- **[generalizable structure, project-specific content]** — the structural pattern transfers, the content does not. Examples: the Authority Matrix shape (3 tiers) transfers; the specific tier definitions are project-specific.
- **[forward-looking proposal]** — described in source material but not actually implemented or validated. Examples: Pattern-Miner agent, Outside-the-Box agent, Drift Sentinel agent (proposed in source material). Recommend only with explicit caution.

**Apply tags inline in DESIGN, EVOLVE, REMEDIATE, and TEMPLATE mode outputs.** When citing a pattern, name the basis for the tag in one line. Without the tag, recommendations imply more confidence than the source material warrants.

---

## End of methodology patterns reference
