# Decomposition Framework

**Canonical source:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.1` (placement discipline) and `root_CC_ENVIRONMENT_GUIDE.md §1` (the 7-layer model in detail).

This reference is a Skill-internal application of those canonicals. It does not duplicate the 7-layer model — it applies the placement test specifically to **Skill-build inputs**: when a user asks "build me a Skill that...," this reference answers "does this work belong in a Skill at all?"

If the canonical KFs evolve (new mechanism added, placement criteria refined), this reference should be regenerated against the new canonical. The cross-reference anchor above is the propagation hook.

---

## Why Gate 1 exists

Misplaced content is the dominant failure mode in CC deployments. A Skill that should have been a hook produces unreliable enforcement (prompts are preferences, hooks are guarantees). A Skill that should have been a subagent pollutes the parent context. A Skill that should have been CLAUDE.md content costs retrieval tokens to surface information that should always be loaded. A Skill that should have been a `.claude/rules/` file fails to fire on the file-pattern cues that the rules system handles natively.

Building a Skill when a different mechanism is correct is worse than not building anything: the user thinks the work is solved, the wrong mechanism silently underperforms, and the failure mode is hard to diagnose because the Skill *exists* and *looks reasonable*.

Gate 1 prevents this by asking the placement question first, before any build work begins.

---

## The 7-layer mechanism map (Skill-build view)

For full mechanism semantics, read `root_CC_ENVIRONMENT_GUIDE.md §1`. The summary below is the build-time decision lens — what to look for in the user's request that signals a non-Skill mechanism.

| Mechanism | Build-time signal that the work belongs here (NOT a Skill) |
|---|---|
| **CLAUDE.md** | Always-relevant standing context. Project mission, authority matrix, halt triggers, scope boundaries. Information that must be loaded at session start, not retrieved on demand. |
| **`.claude/rules/`** | Path-scoped or file-pattern-scoped rules. "When working on `*.tsx` files, always..." or "In the `migrations/` directory, never...". The rules system handles glob matching natively. |
| **Skills** (.claude/skills/) | Multi-step procedures, methodology, decision rubrics, reusable build/review/audit pipelines. Triggered by intent ("build me X," "audit Y," "convert Z"), not by file pattern. |
| **Subagents** | Focused specialist tasks with isolated context. The parent agent dispatches to a subagent when (a) the task is large and self-contained, (b) the parent's context shouldn't be polluted by intermediate state, (c) parallelism across multiple specialists is valuable. |
| **Hooks** | Lifecycle guarantees. PreToolUse / PostToolUse / Stop / UserPromptSubmit hooks enforce things deterministically. If the user's request is "always do X before Y" or "never let Z happen without W," the work belongs in a hook, not in Skill prose. |
| **MCP** | External data and APIs. Connecting to Slack, Drive, Airtable, GitHub, custom services. Tool definitions and authentication, not procedural instructions. |
| **Settings** | Trust and permission boundaries. `permissions`, `defaultMode`, environment variables, model selection. Configuration, not behavior. |

A Skill is the right mechanism when: the work is a **multi-step procedure or methodology**, triggered by **user intent expressed in language**, that produces **a coherent deliverable or analysis**, and that can be **reused across contexts** (different projects, different users, different inputs).

If any of those four criteria fails, suspect a mismatch and walk the redirect logic below.

---

## Redirect language by mechanism

When a Skill-build request fits a different mechanism, redirect with brief explanation. Use the patterns below as starting prompts — adapt to the user's specific input.

### Belongs in CLAUDE.md, not a Skill

Signal: user wants information or rules that must be in scope at all times — project mission, scope authorization, authority decisions, halt triggers, the standing decision context.

Pivot: "This work fits CLAUDE.md, not a Skill. CLAUDE.md is always-loaded; Skills load on demand. If this content needs to be in scope every session — without waiting for a trigger phrase — it belongs in CLAUDE.md's R1–R5 sections. See `root_CC_ENVIRONMENT_GUIDE.md §2` for CLAUDE.md design discipline. Want help drafting the relevant CLAUDE.md section instead?"

### Belongs in `.claude/rules/`, not a Skill

Signal: user describes work tied to file patterns or directory paths — "always do X for `*.py` files," "in the `tests/` directory, do Y," "before touching `migrations/`, check Z."

Pivot: "This work fits `.claude/rules/`, not a Skill. The rules system fires on file-pattern matches natively — Skills fire on intent expressed in language. A Skill that scans for file patterns duplicates infrastructure the rules layer provides cleanly. See `root_CC_ENVIRONMENT_GUIDE.md §3` for path-scoped rule patterns. Want help drafting the rule file instead?"

### Belongs in a hook, not a Skill

Signal: user wants enforcement — "always run X before Y completes," "never let Z happen without W passing first," "guarantee that A occurs after B."

Pivot: "This work fits the hook mechanism, not a Skill. Hooks provide deterministic enforcement (PreToolUse / PostToolUse / Stop / UserPromptSubmit). Skill instructions are preferences the model can override under conflicting pressure — hooks are guarantees. The Enforcement-as-preference anti-pattern (`root_AGENT_ANTI_PATTERNS.md §4.4`) describes this exact failure mode. See `root_CC_ENVIRONMENT_GUIDE.md §6` for hook design. Want help drafting the hook config instead?"

### Belongs in a subagent, not a Skill

Signal: user wants a focused specialist whose intermediate work shouldn't pollute the parent context — large research tasks, multi-step audits with verbose intermediate state, parallel investigations across multiple targets.

Pivot: "This work fits a subagent, not a Skill. Subagents run in isolated context — useful when (a) the task is self-contained, (b) intermediate state shouldn't pollute the parent, (c) you want to dispatch multiple in parallel. A Skill runs in the calling context and adds its instructions to the parent's working memory. See `root_CC_ENVIRONMENT_GUIDE.md §4` for the agent-warranted test (when a subagent is genuinely warranted vs. when a built-in tool suffices). Want help defining the subagent instead?"

### Belongs in MCP, not a Skill

Signal: user wants integration with an external service — Slack, Drive, GitHub API, custom database, third-party tooling.

Pivot: "This work fits MCP, not a Skill. MCP is the integration mechanism for external services — tool definitions and authentication, not procedural prose. A Skill that wraps API calls in instructions duplicates what MCP handles natively (and more reliably, with proper credential handling). See `root_CC_ENVIRONMENT_GUIDE.md §7` for MCP minimalism principles. Want help scoping the MCP server instead?"

### Belongs in settings, not a Skill

Signal: user wants permission boundaries, trust configuration, model selection, environment variables — not behavior, but configuration.

Pivot: "This work fits settings, not a Skill. Settings configure the environment (permissions, default mode, model, env vars). Skills add procedures and methodology. If the request is 'always allow X' or 'never auto-execute Y,' that's a `permissions` configuration. See `root_CC_ENVIRONMENT_GUIDE.md §1.7`. Want help drafting the settings change instead?"

---

## Hybrid placements (legitimate Skill use with companion mechanism)

Some requests genuinely warrant a Skill **plus** a different mechanism. Don't redirect away from the Skill in these cases — flag the companion as a build-summary recommendation.

**Skill + hook companion.** The Skill provides the procedure ("how to validate a release"); a hook enforces the trigger ("always run release validation before tagging"). Build the Skill; recommend the user also add a hook config so enforcement isn't preference-only.

**Skill + CLAUDE.md companion.** The Skill provides the methodology ("how to write an ADR"); CLAUDE.md establishes the project's ADR location and authority ("ADRs live in `docs/adr/`; Aaron approves before merge"). Build the Skill; recommend the CLAUDE.md addition so the Skill knows where to write.

**Skill + `.claude/rules/` companion.** The Skill provides multi-step methodology ("comprehensive Python refactor"); a rule file provides the lightweight always-on context ("when in `*.py`, prefer pathlib over os.path"). Build the Skill; recommend the rule file for the always-on slice.

In hybrid cases, build the Skill, but surface the companion mechanism in the build summary so the user can decide whether to add it.

---

## Decision flow

When parsing a Skill-build request, walk this sequence:

1. **Is the work always-relevant context?** → CLAUDE.md. Redirect.
2. **Is the work tied to file patterns?** → `.claude/rules/`. Redirect.
3. **Does the user need enforcement (deterministic guarantee)?** → Hook. Redirect.
4. **Is the work a focused specialist task that shouldn't pollute parent context?** → Subagent. Redirect.
5. **Is the work an external service integration?** → MCP. Redirect.
6. **Is the work permission/trust configuration?** → Settings. Redirect.
7. **Is the work multi-step procedure / methodology / decision rubric, triggered by user intent in language?** → Skill. Pass Gate 1, proceed to Gate 2.

The first six checks are short-circuiting: if any fires, redirect and halt the build. Only when none fires does the work pass to Gate 2 (warrant check).

---

## Edge cases

**The user explicitly says "I want this as a Skill."** User preference is input, not authorization. If the work fits a different mechanism, redirect with explanation — and respect the user's right to override after hearing the redirect. Some users have valid reasons (portability across environments, version control conventions, distribution model) for choosing a Skill even when another mechanism would be technically cleaner. Surface the mismatch; let the user decide.

**The work fits multiple mechanisms.** Pick the most specific one. Hooks are more specific than Skills (deterministic enforcement vs. on-demand procedure). Rules are more specific than Skills (file-pattern matching vs. intent matching). CLAUDE.md is more specific than Skills (always-loaded vs. on-demand). Specificity wins because it carries fewer failure modes.

**The work is a methodology that *includes* enforcement.** Build the Skill for the methodology; recommend the hook for the enforcement slice. See "Skill + hook companion" above.

**The user describes the work in terms that match Skill-build language but the underlying need is different.** Listen for the underlying need. "I want a Skill that always runs before deploys" — the keyword "always" signals enforcement; redirect to hook. "I want a Skill that watches for X" — the keyword "watches" signals lifecycle; redirect to hook. "I want a Skill that knows about our project structure" — signals always-loaded context; redirect to CLAUDE.md.

---

## What this reference does not do

This reference does not teach the 7-layer model itself — that's `root_CC_ENVIRONMENT_GUIDE.md §1`. It applies the model to Skill-build decisions. If you need to understand any mechanism in depth, read the canonical source.

This reference does not handle Gate 2 (warrant) or Gate 3 (ecosystem fit). Those are separate gates with separate references (`warrant-check-criteria.md`, `ecosystem-placement-decision.md`). Gate 1 only answers "Skill or different mechanism?" — not "if Skill, is it warranted?" or "if Skill, where does it sit in the ecosystem?"
