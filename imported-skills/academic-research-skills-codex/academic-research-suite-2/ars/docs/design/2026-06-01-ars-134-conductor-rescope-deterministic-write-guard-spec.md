# ARS #134 — Rescope: Active Conductor → Scoped-Write Guard MVP (deterministic for structured tools, all-Bash-deny for fenced agents)

**Issue:** #134 (v3.10 Active Conductor Architecture)
**Date:** 2026-06-01
**Type:** Architecture design spec (design-phase only — no implementation in this round)
**Decision authority:** owner-confirmed rescope (2026-06-01)
**Prerequisite shipped:** v3.9.2 (#133 hot-fix) — Routing Discipline, Phase Boundary blocks, advisory verifier, all live on main.

> **Implementation outcome (Slice 1 shipped).** The Bash policy in this spec was written as
> "best-effort literal-target linting" (catch obvious `>`/`cp`/`mv`/`tee`), with the §3.2
> Step-4 / §7 candidate of denying mutation-capable Bash for Bucket A agents left open to
> decide at implementation. Implementation converged on that candidate, taken to its sound
> conclusion: **all Bash is denied wholesale for a Bucket A agent** (use the Grep/Glob tools
> to search, Write/Edit/MultiEdit to write). Reason: neither a denylist of "mutation-capable"
> Bash nor an allowlist of "read-only" Bash can be decided reliably from a command string
> (interpreters, `--pre`/`--pager`/`--compress-program`-style exec hooks, and command-
> injecting env vars make both "writes a file" and "is read-only" unstable across
> commands/flags/env/versions). All-deny is the only Bash policy that reaches zero fail-open
> by construction without a sandbox. Where the prose below says "best-effort literal-target
> Bash", read "all-Bash-deny for Bucket A" — the structured-tool determinism (the load-bearing
> claim) is unchanged. The honest cost is a clean false-deny of ad-hoc read-only Bash, which
> the fenced agents do not need.

## 0. TL;DR

#134 as originally written proposes a 35-55h "active conductor / dispatched-executor" architecture: a persistent intent-aware controller, structured task envelopes, structured return contracts, and a retrofit of 23-34 agent prompts. **This spec rescopes it** to its load-bearing core: a **structured-tool scoped-write guard** — a `PreToolUse` hook that blocks out-of-scope file writes by the structured editing tools (Write / Edit / MultiEdit) per subagent, backed by a machine-readable scope manifest, with **best-effort linting of obvious Bash write redirections**.

**Coverage claim — stated precisely (no over-promise).** The guard is *deterministic* for the structured editing tools (Write / Edit / MultiEdit): a write outside the agent's declared scope is blocked regardless of the agent's prompt. It is *best-effort only* for Bash — it can catch plain redirection / `cp` / `mv` / `tee`, but is **blind to writes made inside invoked programs** (`python script.py`, `sed -i`, `node -e`, `perl -pi`, build scripts) and to advanced shell constructs (heredocs, process substitution, variable-indirected paths). This is NOT "deterministic enforcement of all writes" — calling it that would be the same false-enforcement illusion v3.9.2 avoided by not fencing multi-phase agents with placebo prose (§3.3). The honest value is: it makes the common, accidental scope-inflation write path (a helpful agent calling Write into a downstream phase dir — the #133 shape) deterministically impossible, and surfaces obvious Bash attempts.

The rest of the conductor vision (full task envelopes, return contracts, persistent conductor session, intake classifier) is preserved as **forward-scope**, gated on the MVP proving real coverage and on new incidents pointing beyond what the MVP covers.

## 1. Why rescope (the framing challenge)

The original issue treats #133 as "a missing-envelope problem." First-party review (corroborated by an independent adversarial design review) finds otherwise:

1. **v3.9.2 already closed the reported #133 failure at the prompt level.** Routing Discipline (`.claude/CLAUDE.md`) clarifies on ambiguous cross-phase input instead of silently dispatching; 23 Bucket A single-phase agents carry `## Phase Boundary` blocks naming the #133 pattern as forbidden; `check_pipeline_integrity.py` flags the pattern post-hoc. The entry-routing failure (L1) and the prompt-discipline half of L2 are mitigated and CI-linted (`check_v3_9_2_phase_boundary.py`: 23 fenced, 16 exempt).

2. **A task envelope that is only a YAML block in a subagent prompt is still honor-system.** An agent can ignore a structured envelope exactly as easily as it can ignore prose. The structured-envelope layer, by itself, buys a tidier prompt format that *feels* more rigorous — not enforcement.

3. **The one capability the prompt layer genuinely cannot provide is deterministic enforcement — for the structured editing tools.** A `PreToolUse` hook blocks a `Write`/`Edit`/`MultiEdit` outside an agent's declared scope regardless of what the agent's prompt says or "decides." This is the only part of the conductor vision that is enforcement rather than prose — and even it is bounded by the Bash blind spot (§3.3): the hook is deterministic for structured-tool writes, best-effort for literal-target Bash, and blind to invoked-program side-effects.

Therefore the smallest increment that captures most of the real residual risk is: **a default-on `PreToolUse` write-scope guard for the 23 Bucket A agents, backed by a minimal machine-readable scope manifest.** Full envelopes and return contracts only become enforcement if and when the hook consumes them — and even then they are not justified until the hook proves coverage and incidents demand more.

This rescope also honors the standing repo discipline against unrequested abstraction / configurability for single-use needs: we build the one mechanism that is enforcement, and defer the abstraction layer until a second consumer (or a real incident) demands it.

## 2. What stays prompt-level (unchanged)

- **Activation model: default-on GUARD, not default-on CONDUCTOR.** The v3.9.2 clarification gate stays always-on for ambiguous input (the #133 victim was unaware — opt-in would miss them). The write-scope hook is also default-on whenever ARS plugin context is active, and **silent unless it blocks something**. We do NOT auto-activate a persistent "conductor" session for any ARS-ish context — that risks the sycophantic-over-asking failure and surprises users. `/ars-*` commands and existing routing continue to choose workflows; the guard only prevents forbidden writes once an agent is running.
- `[direct-mode]` escape hatch bypasses **clarification only**, never the safety guard (issue Q1 resolution).
- The 16 Bucket B/C/D agents stay prompt-exempt (v3.9.2 honest-framing decision preserved — see §4).

## 3. Slice 1 — Bucket A scoped-write guard (this is the MVP)

### 3.1 Scope manifest

A new machine-readable manifest mapping each Bucket A agent to its permitted write scope. Single source of truth, derived from the canonical `docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md` classification table (do NOT re-derive — that table is authoritative; the manifest references it).

**Authoritative agent universe (first-party counted 2026-06-01).** The classification table has **39 rows = 23 Bucket A + 4 B + 8 C + 4 D** (16 B/C/D exempt). (The table's own title says "38-Agent" because `socratic_mentor_agent` appears as two rows — one in deep-research, one in academic-paper — same `name`, distinct prompt bodies; 39 rows over 38 unique frontmatter names. The manifest keys on the 23 Bucket A `name` values, none of which is the duplicated socratic_mentor, so the duplication does not affect Slice 1.) The 23 Bucket A names: `abstract_bilingual_agent`, `bibliography_agent`, `citation_compliance_agent`, `devils_advocate_reviewer_agent`, `domain_reviewer_agent`, `draft_writer_agent`, `editor_in_chief_agent`, `editorial_synthesizer_agent`, `eic_agent`, `ethics_review_agent`, `formatter_agent`, `literature_strategist_agent`, `meta_analysis_agent`, `methodology_reviewer_agent`, `peer_reviewer_agent`, `perspective_reviewer_agent`, `research_architect_agent`, `research_question_agent`, `risk_of_bias_agent`, `source_verification_agent`, `structure_architect_agent`, `synthesis_agent`, `timeline_extraction_agent`.

Proposed shape (`scripts/ars_phase_scope_manifest.json` or `.yaml` — format decided at implementation, JSON for hook-read simplicity):

```json
{
  "version": 1,
  "source": "docs/design/2026-05-18-ars-v3.9.2-agent-phase-classification.md",
  "agents": {
    "bibliography_agent":   { "bucket": "A", "phase": 2, "allowed_write_globs": ["phase2_*/**", "**/annotated_bib*.md", "**/literature.{yaml,json}", "**/references.bib"] },
    "synthesis_agent":      { "bucket": "A", "phase": 3, "allowed_write_globs": ["phase3_*/**", "**/synthesis*.md"] }
    /* … 23 Bucket A entries total … */
  }
}
```

**Design difficulty — skill-relative phase numbering (must be handled, not assumed away).** The classification table's "Phase N" is *skill-relative*, not global: deep-research Phase 2 = investigation, but academic-paper-reviewer "Phase 1 (reviewer skill)" is the whole reviewer skill, which sits at academic-pipeline Phase 5. A naive `phase{N}_*/` glob is therefore not globally meaningful. The manifest's `allowed_write_globs` must be the **authoritative scope expression** (path patterns the agent may write), with `phase` retained only as a human-readable label cross-referencing the classification table — the hook keys on globs, not on a phase integer. This avoids the false precision of a global phase number.

### 3.2 PreToolUse hook

A new `PreToolUse` hook (added to `hooks/hooks.json`, which today carries only a SessionStart announce). First-party verified against official Claude Code hook docs (2026-06-01):

- **Payload fields available inside a subagent:** `session_id`, `transcript_path`, `cwd`, `permission_mode`, `hook_event_name`, `effort`, `tool_name`, `tool_input`, plus the subagent-conditional `agent_id` and `agent_type`. `agent_type` equals the agent's frontmatter `name` (not filename) — this is the canonical subagent identity binding. **`tool_use_id` is NOT documented as a payload field** (the #134 issue comment listed it — drop it; do not rely on it).
- **Deny mechanism:** exit 0 with stdout JSON:
  ```json
  { "hookSpecificOutput": {
      "hookEventName": "PreToolUse",
      "permissionDecision": "deny",
      "permissionDecisionReason": "ARS scope guard: <agent_type> may not write <path> (outside allowed_write_globs)" } }
  ```
  (`permissionDecision` ∈ `{deny, allow, ask, defer}`; exit code 2 + stderr is the coarse alternative.)
- **Logic (strict order — normalization is the FIRST operation, before any deny-list or glob match):**

  **Step 1 — Extract + normalize the write target(s) FIRST.** For `Write` / `Edit` / `MultiEdit`, the target is the single top-level `tool_input.file_path` (first-party verified against official docs 2026-06-01: all three tools take exactly one `file_path`; `MultiEdit`'s `edits[]` array holds multiple edits to that ONE file — it does NOT carry multiple distinct file paths. Caveat: `MultiEdit`'s `tool_input` is not enumerated in the official hooks input table — schema taken from the tool definition; pin a fixture and re-verify if CC changes it). For `Bash`, extract literal write targets from `tool_input.command` (best-effort, §3.3). For each extracted target: resolve to an absolute path relative to `cwd`, resolve symlinks (resolving parent dirs without requiring the leaf to exist, since the write may create it), require it falls under the workspace root via `commonpath(target, workspace_root)`, then convert to a **workspace-root-relative canonical path**. ALL later steps match against this normalized form — never the raw `file_path` (a raw `phase2_*/../hooks/hooks.json` must already be canonicalized so it cannot slip past the deny-list or a glob). **The path-traversal escape (a target resolving OUTSIDE the workspace root) is denied for a Bucket A agent only — it is a Bucket A phase-dir fence, not a global one (#302).** The main session and Bucket B/C/D agents are unconstrained by Slice 1 (§3.3), so an escaping target from them (e.g. a write into a sibling git worktree — a mainstream layout) falls through to the Step-3 `allow`; fencing it would contradict Step 3's own "unconstrained by Slice 1" rule. Infra self-protection (Step 2) is NOT consulted on an escaped path: every protected glob is workspace-relative, so an outside-workspace target can never be an infra target (a symlink resolving back INTO the workspace is not an escape, so Step 2 still runs for it).

  **Step 2 — Infrastructure self-protection (unconditional, on the NORMALIZED path; overrides any later allow).** Deny any write whose normalized target is part of the enforcement surface — regardless of `agent_type`. Protected set: `hooks/hooks.json`, the hook script and any helper modules it imports, the scope manifest, the agent definition / frontmatter files (the source of the `agent_type == name` binding — renaming an agent out of the manifest would fail the guard open), `.claude/CLAUDE.md`, and (Slice 2) the provenance ledger. **Coverage caveat (must stay honest, consistent with §3.3):** this deny is deterministic for `Write`/`Edit`/`MultiEdit`. For a Bucket A agent the Bash write path is closed by the SHIPPED all-Bash-deny policy (Step 4), so infrastructure self-protection holds against Bash too for fenced agents. (For the unconstrained main session / Bucket B/C/D agents, Bash is not gated — Step 2 only governs the structured-tool path there; those actors are trusted by Slice 1 scope.) Do NOT claim Step 2 blocks "any write from any tool" by any actor.

  **Step 3 — Agent gating.** If payload has `agent_type` AND it is a Bucket A manifest entry → enforce its `allowed_write_globs` (globs are workspace-root-anchored, matched against the Step 1 normalized relative path — NOT against an absolute path, which would never match, and NOT against `cwd`-relative, which would let a write under any matching-named subfolder slip through). If `agent_type` is absent or not a Bucket A key → `allow` (main session / B/C/D unconstrained by Slice 1), BUT if ARS plugin context is detectable and a write tool fired with NO `agent_type`, emit a **fail-loud advisory log line** (do not silently no-op a possibly-regressed payload — see §3.4 cross-check lint).

  **Step 4 — Tool-specific check.** `Write` / `Edit` / `MultiEdit` → single `file_path` already normalized in Step 1; deny if outside the agent's globs. `Bash` → **SHIPPED: deny ALL Bash for a Bucket A agent** (the §7 candidate, taken to its sound conclusion — see the Implementation-outcome note at the top). The hook does not parse Bash at all: a Bucket A agent's Bash is denied wholesale with a message routing search to the Grep/Glob tools and writes to Write/Edit/MultiEdit; non-Bucket-A Bash passes through. This also makes Step 2 self-protection robust against Bash (no invoked-program write path remains for a fenced agent). *(The original design here was "best-effort literal-target Bash linting"; implementation found neither a denylist nor an allowlist of Bash is sound — §3.3.)*

### 3.3 The Bash bypass gap — honest disclosure (NOT silently capped)

A write-scope guard that only inspects `tool_input.file_path` catches Write/Edit/MultiEdit deterministically, but a subagent can write via Bash. PreToolUse *does* fire for Bash with the full command in `tool_input.command`, yet the command string only exposes a parseable write target for *direct shell file operations*. The uncatchable surface is larger than just exotic shell syntax and must be stated in full:

1. **Invoked-program side-effects (the largest gap).** `python script.py`, `python -c "open('x','w')..."`, `node -e`, `sed -i`, `perl -pi -e`, `awk` with redirect, a `Makefile`/build script, `git checkout`/`git restore`, `rsync`, `install`, `tar -x`, `touch`, `mkdir`, `rm` — the hook sees only the launch command, never the file I/O the launched program performs. No amount of command-string parsing reaches inside an invoked process.
2. **Advanced shell constructs.** Heredocs, process substitution, subshell writes, variable-indirected paths (`> "$OUT"`).
3. **Catchable subset only:** plain `>` / `>>` redirection, `tee`, `cp`, `mv` with literal path arguments.

Per no-silent-caps discipline, this gap is stated explicitly here, in the hook's own deny output, and in the protocol doc — NOT silently capped. The analysis above is exactly *why* the SHIPPED policy is to **deny ALL Bash for a Bucket A agent** rather than attempt to parse it: the uncatchable surface (invoked-program side-effects, advanced shell constructs, and — found during implementation — "read-only" tools that execute subprocesses via `--pre`/`--pager`/`--compress-program` or command-injecting env vars) means neither "this Bash writes" nor "this Bash is read-only" can be decided from a command string. Option (a) from the original draft — "deny/ask mutation-capable Bash" — was therefore taken all the way to deny-all (the only form that reaches zero fail-open by construction; a sandbox, option (b), remains out of scope). The honest coverage claim is now: **"deterministic for the structured editing tools; all Bash denied for Bucket A agents (use Grep/Glob + structured tools); no Bash write path remains for a fenced agent."** **A guard that pretends to be watertight when it is porous would be a false-enforcement illusion — exactly the failure mode v3.9.2 avoided by NOT fencing multi-phase agents with placebo prose. The MVP's real, honest win is making the #133 shape — a helpful agent calling the Write tool into a downstream phase dir — deterministically impossible, plus closing the Bash write path for fenced agents entirely.**

### 3.4 Tests + lint

- TDD: a test harness that synthesizes PreToolUse payloads per `agent_type` and asserts allow/deny decisions: in-scope structured-tool write allowed; out-of-scope `Write` denied; out-of-scope `MultiEdit` denied (single `file_path`, multiple edits to that one file — assert the path check uses the top-level `file_path`, not a non-existent per-edit path array); out-of-scope Bash redirection denied where catchable; Bash invoked-program write NOT claimed-blocked (test asserts the honest non-coverage, so the limitation can't silently regress into a false coverage claim); **Step 2 infrastructure write denied for every `agent_type`** (including a manifest agent with a deliberately broad glob); **traversal-bypass denied** (a `Write` with `file_path` like `phase2_x/../hooks/hooks.json` is canonicalized in Step 1 and then caught by Step 2 — proves normalization precedes self-protection); absent `agent_type` allowed (main session); non-Bucket-A `agent_type` allowed; **main-session / non-Bucket-A escape allowed** (a `Write` resolving OUTSIDE the workspace — e.g. a sibling worktree — is allowed for the main session and Bucket B/C/D, while the SAME escape from a Bucket A agent stays denied — proves the escape deny is a Bucket A fence, not global, #302); absolute-vs-relative path normalization (a `Write` with an absolute `file_path` under the workspace resolves and matches its relative glob).
- **Three-way name cross-check lint (fail-open guard, addresses the silent-no-op risk).** Assert the SAME 23 names appear in (a) the classification table Bucket A rows, (b) the scope manifest keys, and (c) the actual agent definition frontmatter `name` fields on disk. A mismatch (renamed agent, manifest typo, table drift) would make the hook silently fail open for that agent — the lint catches it before that can happen. Mirrors `check_v3_9_2_phase_boundary.py`'s 23/16 split.
- Mutation tests confirm each invariant is load-bearing (trivial accept-all replacement must FAIL).
- Wire into `spec-consistency.yml` + the pytest manifest.

### 3.5 Slice 1 explicitly does NOT include

No task envelope schema, no return contract schema, no conductor protocol doc beyond a narrow note, no agent-prompt retrofit (the 23 Phase Boundary blocks already exist as the human-readable mirror; Slice 1 adds the machine-readable enforcement layer beside them), no persistent conductor session, no intake classifier. Each is a later slice (§5) or forward-scope (§6).

## 4. Retrofit scope (issue Q4 resolution)

- **Slice 1 covers the 23 Bucket A single-phase agents only.** Their write scope is static and well-defined per the classification table.
- **The 16 Bucket B/C/D agents stay exempt.** The v3.9.2 author deliberately did not fence them on honest-framing grounds (placebo prose on a multi-phase agent fakes enforcement). A *static union* of a multi-phase agent's scopes is weak (it would permit writes to any phase the agent ever touches, defeating the point). Real enforcement for the 4 Bucket B agents (`report_compiler` 4/6, `devils_advocate` 1/3/5, `argument_builder` 3/Plan, `visualization` 4/7) needs **per-invocation scope grants** — a later slice, and only if the hook can read a current-task-scope record. Bucket C/D (phase-orthogonal / meta: `socratic_mentor`, `monitoring`, `revision_coach`, `intake`, `field_analyst`, `compliance`, orchestrators) are legitimately cross-phase and should NOT be forced into phase envelopes; grant them explicit special scope only where a concrete need arises.

## 5. Slice roadmap (each independently shippable and independently valuable; owner can stop after any slice)

1. **Slice 1 — Bucket A scoped-write guard (THE MVP).** Scope manifest + PreToolUse hook (Step 2 self-protection + structured-tool deterministic + best-effort Bash) + hook config + tests + three-way name cross-check lint. No prompt retrofit, no return contract, no conductor doc beyond a narrow protocol note. *Stops here cleanly with net safety value.* Independently shippable: depends only on v3.9.2 (already on main).
2. **Slice 2 — Write provenance log (annotated overlay, NOT a ground-truth replacement).** When the hook allows a write, append `{agent_type, tool, path, timestamp, decision}` to a local ARS provenance ledger. The ledger is an *authorship annotation* over the file system — it is NOT tamper-resistant by construction (a Bash invoked-program write, or the unconstrained main session / exempt agents, can write files the ledger never sees), so it MUST NOT replace `check_pipeline_integrity.py`'s file-system/git ground-truth scan; it layers "who wrote it" on top of the existing "what exists" check. The ledger file itself is under Step 2 self-protection (append-through-hook only). Partially closes issue-comment deferred item #3 (provenance annotation; full author-provenance verification stays bounded by the Bash blind spot).
3. **Slice 3 — Bucket B per-invocation scope grants.** Only for `report_compiler`, `devils_advocate`, `argument_builder`, `visualization`. Requires a current-task-scope record the hook reads — this is the *minimal* form of a "task envelope": just enough machine-readable scope for the hook, not a full contract. **NOT independently shippable on its own:** it has a hidden trust dependency — *who writes the grant, when it expires, and how an agent is prevented from editing its own grant*. The grant producer must be the dispatching layer (not the dispatched agent), and the grant store must be under Step 2 self-protection. This slice is effectively a minimal conductor/envelope and should only be built once that authenticated-grant-producer + protected-grant-store trust boundary is designed (its own design round).
4. **Slice 4 — Return report schema (optional).** Useful for conductor UX and handoff summaries; not core safety. Builds only if Slice 3's task-scope record wants a matching acceptance record.
5. **Slice 5 — Structured intake classifier.** Given materials with no passport hash, classify which phase to resume and dispatch accordingly (issue-comment deferred item #4). Build only if ambiguous no-passport resumes prove a recurring problem *after* v3.9.2's clarification gate — i.e. incident-driven, not speculative.

## 6. Forward-scope (preserved from the issue, deliberately NOT built now)

- **Full task envelope + return contract substrate** (issue's central proposal): becomes enforcement only when the hook consumes it (Slice 3 is the minimal honest version). Full free-form envelope/return-contract is gold-plating until then.
- **Persistent conductor session holding cross-turn state** (issue's "active conductor"): the v3.9.2 clarification gate + the hook cover the safety case without a persistent controller. Revisit only if intent-tracking across turns becomes a felt need.
- **Cross-CLI degradation (issue Q5):** the hook is Claude-Code-specific (other CLI runtimes have no equivalent PreToolUse hook). On those runtimes the layer degrades to the existing prompt-level Phase Boundary blocks. Document the asymmetry; do not build a cross-CLI enforcement substitute speculatively.
- **#272 instruction/data boundary:** the issue flags the envelope layer as a possible home for "retrieved external content is data, not instruction." The write-scope hook does NOT address this — it is a write-path guard, not a read/trust-boundary guard. **Slice 1 (and this rescope of #134 generally) must NOT close #272 or claim any mitigation of it.** The instruction/data boundary remains a separate, still-open safety track; rescoping #134 down to a write guard must not let it be silently buried just because #134 once contemplated an envelope layer. Revisit #272's home only when a concrete envelope substrate exists (Slice 3+), and even then as an explicit separate design.
- **v3.7+ gate interaction (issue Q6):** claim audit / triangulation / compliance gates remain orthogonal to the write-scope guard; the guard is a file-write-path constraint and does not fold them in. No change to those gates.

## 7. Open items for implementation rounds (not this design round)

- Manifest format (JSON vs YAML) and exact glob vocabulary per Bucket A agent — resolve against the classification table at Slice 1 implementation, with its own independent cross-model review.
- Exact Bash-command write-target parser scope (which constructs to attempt) and how loudly to surface the best-effort caveat in the deny reason.
- Whether `hooks/hooks.json` PreToolUse entry needs an `if` matcher to limit firing to ARS agent contexts (perf) vs firing on every tool call and short-circuiting on absent `agent_type`.

## 8. Ship gate for the MVP (Slice 1, when implemented)

Quality cleanup pass → independent cross-model review (0 P0/P1) → boundary + secret scan → PR. The `#134` issue is updated to reflect the rescope (this spec becomes its design anchor); Slice 1 closes the MVP, later slices tracked as follow-ups or left as forward-scope.

## 9. Definition of done — DESIGN ROUND (this round)

- [x] First-party review of v3.9.2 base (routing gate, Phase Boundary blocks, verifier, classification table) — done.
- [x] Adversarial framing challenge run; rescope decision owner-confirmed.
- [x] PreToolUse hook capability (payload `agent_type`, deny schema, Bash gap) first-party verified against official docs.
- [x] This spec written: rescope rationale, Slice 1 design, 5-slice roadmap, forward-scope, honest Bash-gap disclosure.
- [x] Independent cross-model design review reaches 0 P0/P1 — 3-round trajectory (R1: rescope direction confirmed sound by both reviewers, 5 P1 + 4 P2 on Slice-1 mechanism precision; R2: ordering regression caught + 4 more P1; R3: both reviewers CONVERGED, 0 P0/P1).
- [ ] Spec doc shipped (PR) as the #134 design anchor; implementation slices follow in separate PRs.
