---
name: sadp
description: Structured AI Development Protocol — a governance harness for indefinite-horizon AI co-development. Provides atomic generational handoff, a 77-rule discipline layer with LOCK/UNLOCK/SUSPEND, append-only MEM ledger + per-edit forensics, pre-bump release gate, evaluator subagent, doc-audit instruments, and architectural fitness functions. Single-operator + single-AI use case. Apache 2.0.
version: 1.91
homepage: https://github.com/brownanan/acervator/tree/main/sadp
license: Apache-2.0
---

# SADP — Structured AI Development Protocol

A governance harness for indefinite-horizon AI co-development. This skill packages the SADP machinery so any Claude-compatible agent harness (Claude Code, Codex CLI, Cursor, Gemini CLI, etc.) can install and use it.

## When to use this skill

Use SADP when:

- You're co-developing software with an AI partner across **multiple sessions** (the same project, the same AI, weeks or months of collaboration).
- The project has **release discipline** — version banners, CHANGELOGs, a release artifact.
- Mistakes can ship — version bumps, CHANGELOG entries, banner-bearing files that need to stay consistent.
- You want **structural prevention** of common failure modes (self-grading bias, banner-bumped-with-failing-suite, bugs recurring at different sites, sessions ending blind) rather than disciplinary avoidance.

Don't use SADP for:

- One-off scripts.
- Multi-agent orchestration (use claude-flow / AutoGen instead; SADP can sit underneath each agent).
- Projects with horizons measured in days rather than weeks.

## What this skill provides

### 1. Atomic generational handoff

A per-session HOP file with a forward-looking `## NEXT SESSION` header. Any cold-start session reads it first. Cold-read budget ≤ 2-3% of context window.

Tool: `python tools/hop_open.py`
- `--next-only` — just the NEXT SESSION block
- `--last N` — NEXT SESSION + most recent N session blocks (default 2)
- `--check` — validate the schema

### 2. 77-rule discipline layer (R1–R77)

Rules organized into nine functional groups: A (Memory & LTM), B (File Safety), C (Change Protection), D (Battery & Engine), E (Documentation), F (Cost & Audit), G (Reliability & Find-It-Fix-It), H (Governance Authority), I (AI Discipline).

LOCK/UNLOCK/SUSPEND semantics on every rule:
- **LOCK** — rule cannot be modified without operator override
- **UNLOCK** — rule open for revision
- **SUSPEND** — rule temporarily inactive (recorded in forensic log)

Reference: `sadp/RULE_REGISTRY.json` for the canonical list; `sadp/SPEC-CORE.md` for full rule text.

### 3. Administrative control surface

**Pre-bump release-readiness gate** with 5 contracts:
- R1: `src/__init__.py.__version__` == `main.py:current_version`
- R2: Latest CHANGELOG.md entry mentions current banner version
- R3: Latest sadp/CHANGELOG.md entry mentions current banner version
- R4: pytest exits 0 AND test count matches CHANGELOG declaration
- R5: EPISODIC_MEMORY.json has a MEM entry with `version == banner`

Tool: `python tools/check_release_readiness.py`

**PreToolUse hook** that mechanically denies banner-bump Write/Edit ops without a fresh green sidecar log: `.claude/hooks/verify_release_gate.py`

**Stop hook** that captures uncommitted work to non-destructive forensic log at session end: `.claude/hooks/session_stop_backstop.py`

### 4. Append-only forensic ledgers

- `sadp/EPISODIC_MEMORY.json` — longitudinal MEM ledger; one entry per significant project event.
- `sadp/EDIT_LOG.jsonl` — per-edit record with authority (which rule) + purpose (one-line reason).
- `DEVELOPMENT_CHRONICLE.md` — append-only narrative.

Tool: `python tools/mem_search.py "<query>"` — BM25 search over the MEM ledger so cold-read doesn't require reading the whole 389-entry file.

### 5. Evaluator subagent

`agents/evaluator.md` defines an evaluator persona invoked as a Task subagent with no Write/Edit tools from a fresh context. Used to verify MEM-bearing changes without self-grading bias. Returns `PASS` or `NEEDS_WORK` with specific findings. Optionally drafts a §V-style invariant candidate when the reviewed MEM is `type=incident severity≥P1` (bugs → invariants promotion).

### 6. Doc drift detection

- `tools/doc_audit.py` — 3 drift signals (TRAILING_VERSION, SPARSE_COVERAGE, TABLE_TRUNCATION) across documentation
- `tools/doc_gap_audit.py` — 8 gap categories (TRAILING_VERSION, TABLE_TRUNCATION, SUBSYSTEM_MISSING, MEM_GAP, RULE_GAP, ADR_GAP, CHAPTER_BOLTED_ON, STALE_REFERENCE) for manual-content drift

### 7. Architectural fitness functions

`tests/test_architectural_fitness.py` — 9 rules over the dependency graph, run by pytest. Catches structural defects (e.g., direct construction outside a factory, declared-but-unwired interfaces).

### 8. QA-status unified dashboard

`python tools/qa_status.py` — single command answers "is QA healthy?" with one line. 11 instruments green simultaneously means the project is in known-good state.

### 9. Doc generators

- `tools/build_agents_md.py` — regenerates `AGENTS.md` at repo root on every cascade so external AI tools see a current view of SADP machinery.

## How to use

### First-time setup in a fresh project

```bash
python tools/sadp_init.py
```

Scaffolds:
- `sadp/` — config, rule registry, MEM ledger, EDIT_LOG, CHANGELOG, SPEC-CORE, FIXED_SECTION_SCHEMAS
- `.sadp/` — sidecar logs, session history
- `.claude/hooks/` — PreToolUse + Stop hooks
- `.claude/settings.json` — hook registration
- `HOP.md` — starter HOP with NEXT SESSION schema
- `AGENTS.md` — auto-generated pointer

### Daily flow

1. Cold start a session: `python tools/hop_open.py` — orient on NEXT SESSION
2. Do work — let the AI partner implement under your direction
3. Before bumping versions: `python tools/check_release_readiness.py` — confirm `[OK] Release-ready`
4. Cascade: bump banners → CHANGELOG entries → MEM entry → EDIT_LOG entries → chronicle → AGENTS.md regen → final gate → zip

### Cascade discipline

Every ship follows: src banner → main banner → CHANGELOG entry → sadp/CHANGELOG entry → MEM-N → EDIT_LOG entries → chronicle entry → AGENTS.md regen → gate → zip. The cascade discipline IS the value.

## Configuration

`sadp/config.json` lets you point SADP at your project's specific files:

```json
{
  "project_name": "yourproject",
  "version_file": "src/__init__.py",
  "version_attr": "__version__",
  "main_file": "main.py",
  "main_attr": "current_version",
  "hop_file": "HOP.md",
  "changelog": "CHANGELOG.md",
  "sadp_changelog": "sadp/CHANGELOG.md",
  "episodic_memory": "sadp/EPISODIC_MEMORY.json",
  "edit_log": "sadp/EDIT_LOG.jsonl",
  "chronicle": "DEVELOPMENT_CHRONICLE.md"
}
```

Default values match the Acervator project's conventions. Override in `sadp/config.json` for your project.

## Examples

See `WHY_SADP.md` at the repository root for:
- Comparison matrix against Anthropic's `cwc-long-running-agents`, AGENTS.md, Cavekit/Cavemem, and the harness-engineering literature
- What SADP costs you (cascade-discipline friction is real)
- What SADP is NOT (not multi-agent orchestration, not CI/CD)

Verified comparison evidence: `docs/audits/2026-06-01_sadp_augmentation_research.md` (5 search angles, 24 sources, 25/25 claims verified).

## License

Apache 2.0 with patent grant. See `LICENSE` and `NOTICE`. SADP itself is fully open source. Patent-flagged trading inventions referenced in the same repository (Acervator's application layer) are NOT inside the grant — see `NOTICE` for the boundary.

## Provenance

Built end-to-end from operating experience by Anthony L. Brown (Ekthelius the Accumulator - Contact: brownanan@gmail.com) across 27 sessions and 389 MEM entries of single-operator + single-Claude collaboration on the Acervator trading platform. The methodology emerged from real friction; the structural patterns absorbed from community-developed harnesses (Anthropic `cwc-long-running-agents`, AGENTS.md, Cavekit/Cavemem) are credited in `NOTICE`.

## Guidelines

- **Don't bypass the gate.** When the PreToolUse hook denies a Write, the answer is to run `python tools/check_release_readiness.py` and get `[OK]` — not to disable the hook.
- **Don't skip the MEM entry.** R49 MDEL: every ship lands a MEM entry. The MEM ledger is the longitudinal record; skipping entries breaks searchability and forensic grounding.
- **Don't full-read the MEM ledger.** Use `tools/mem_search.py` — cold-reading 389 entries costs context unnecessarily.
- **Don't full-read the HOP.** Use `tools/hop_open.py` — the NEXT SESSION block + last 2 session blocks is the orientation budget.
- **Don't dilute LOCK/UNLOCK/SUSPEND.** The temporal control surface is what makes SADP's rule layer distinct from a flat AGENTS.md. Use it.
- **Credit absorbed patterns.** SADP took patterns from `anthropics/cwc-long-running-agents`, AGENTS.md, and Cavekit/Cavemem. Credit them in any derivative work.

## PR body (ready to paste — copy from below the line break)

# PR draft — Submit SADP to anthropics/skills

**Target repository:** [anthropics/skills](https://github.com/anthropics/skills)
**Branch suggestion:** `add-sadp-harness`
**Anchor file:** `sadp/SKILL.md` from this repo (already in the canonical SADP layout per the Anthropic Agent Skills spec)
**Status (as of v3.20.54):** draft — operator-driven submission when ready

---

## Pre-submission checklist

Before opening the PR, confirm:

- [ ] Anthropic published the `anthropics/skills` repo (public). If not yet open, this PR is queued until then.
- [ ] `sadp-harness 1.91` is already published on PyPI (per `tools/publish_sadp_to_pypi.py`). The skill should reference an install path that adopters can actually use.
- [ ] `sadp/SKILL.md` reflects the v1.91 wheel contents and current rule count (60 core).
- [ ] You have a GitHub fork of `anthropics/skills` ready to push the branch to.
- [ ] `gh auth status` shows you authenticated under the GitHub identity you want this PR opened under.

---

## PR title

```
Add SADP-harness — structured AI development protocol with 60-rule core + project-overlay extension
```

(70 chars; well under the customary 72-char cap.)

---

## PR body (ready to paste — copy from below the line break)

---

### Summary

This PR adds **SADP (Structured AI Development Protocol)** to the `anthropics/skills` registry. SADP is a governance harness for indefinite-horizon AI co-development — designed around the long-conversation context constraints, generational session handoff, and forensic-observability needs that surface during multi-month single-operator + single-Claude collaborations.

Distribution: `pip install sadp-harness` ([PyPI](https://pypi.org/project/sadp-harness/)).
Source repository: [github.com/brownanan/acervator](https://github.com/brownanan/acervator) (full provenance + the project this methodology emerged from).
License: Apache 2.0 with patent grant.

### What's the skill?

The `sadp/SKILL.md` document (added in this PR) provides Claude with structured guidance on running the SADP workflow against an adopting project:

1. **Read the HOP file in full** at session start (atomic generational handoff)
2. **Reference SPEC-CORE.md** for the 60 core rules + project's IMPL overlay for domain rules
3. **Emit `# sadp: R...` annotations** on critical-path functions
4. **Append MEM ledger entries** at session close with rules-implicated linkage
5. **Run the pre-cascade gate** before shipping (`sadp check`)
6. **Honor the LOCK/UNLOCK/SUSPEND** state semantics on rules

The full discipline is captured in `sadp/SPEC-CORE.md` (~170 KB, 60 rules with citations to Tufte, Cleveland-McGill, Knaflic, Helland, Nygard, McCabe, Martin, Hunt & Thomas, WCAG, Nielsen, IEEE 29148, etc.).

### Why submit this skill?

- **Real operating provenance.** Built across 27 sessions and 399 MEM entries of single-operator + single-Claude development on a non-trivial codebase. Each rule cites a real failure that motivated it.
- **Compatible with existing Anthropic primitives.** Borrows structural patterns from `cwc-long-running-agents`, AGENTS.md, the Agent Skills spec, Cavekit/Cavemem (credited inline). The SKILL.md follows the Agent Skills format exactly.
- **Drop-in installable.** `pip install sadp-harness` → `sadp scaffold --target .` → operational in any Python project. No code changes required to host project; SADP is read-from-config.
- **No vendor lock.** SPEC-CORE is provider-agnostic; `sadp/impl/{claude,openai,local}.md` document per-provider enforcement mechanisms. Claude is the reference implementation; other providers welcomed.

### What ships in the wheel

24 files, ~580 KB:
- `sadp/SKILL.md` (the Agent Skills entry point)
- `sadp/SPEC-CORE.md` (60 core rules; ~170 KB)
- `sadp/RULE_REGISTRY.json` (60 rules, all `tier: "core"`; project-overlay rules don't ship)
- `sadp/_tools/` (8 bundled subcommand implementations: `sadp check`, `sadp scaffold`, `sadp hop`, `sadp mem-search`, `sadp doc-audit`, `sadp qa-status`, `sadp build-agents-md`, `sadp doc-gap-audit`)
- `sadp/{__init__,__main__,cli,config}.py` + scaffold templates

### What does NOT ship

The wheel excludes the host project's domain-specific overlay (in our case: trading-engine rules, GUI rules, Acervator simulator-state-machine invariants). Adopters declare their own overlay rules in `sadp/impl/IMPL-<PROJECT>.md`; the wheel-publish tooling filters by `tier` field.

### Try it

```bash
pip install sadp-harness
mkdir my-project && cd my-project
sadp scaffold --target . --project-name myproject
sadp hop --check     # → [OK] HOP schema valid
sadp check           # release-readiness gate
sadp --help          # full subcommand list
```

### What this PR adds to `anthropics/skills`

Following the registry convention:

```
skills/
  sadp/
    SKILL.md       # copied from sadp/SKILL.md in source repo
    README.md      # short pointer back to PyPI + source repo
```

The SKILL.md is self-contained and follows the Anthropic Agent Skills format. The README provides install + first-use guidance. No other files needed.

### Open questions for the maintainers

1. Should SKILL.md include the full 60-rule spec inline, or just the entry-point procedure with a link to `pip install sadp-harness` for the rules themselves? (Current approach: entry-point procedure inline; full spec in the wheel.)
2. Is there a convention for skills with their own PyPI distribution vs. inline-shipped? SADP is the former.
3. Should I add usage examples to SKILL.md showing 2-3 Acervator-side incidents that the discipline caught? (E.g., the Nuclear/Inferno cascade for R47, the Ichimoku silent-failure for R28.)

I'm flexible on all three — happy to revise per maintainer preference.

### Reproducibility

- Source: github.com/brownanan/acervator @ tag v3.20.54
- Wheel: PyPI `sadp-harness == 1.91`
- Built locally with `python -m build`; verified via `tools/publish_sadp_to_pypi.py --verify-only`

---

## Manual submission steps (when ready)

```bash
# 1. Fork anthropics/skills on github.com if not already done

# 2. Clone your fork
gh repo clone <your-username>/skills
cd skills

# 3. Sync with upstream
git remote add upstream https://github.com/anthropics/skills.git
git fetch upstream
git checkout main && git merge upstream/main

# 4. Create the branch
git checkout -b add-sadp-harness

# 5. Add the skill files
mkdir -p skills/sadp
cp <ACERVATOR_REPO>/sadp/SKILL.md skills/sadp/SKILL.md

# Create skills/sadp/README.md with a short pointer (see template below)
cat > skills/sadp/README.md << 'EOF'
# SADP — Structured AI Development Protocol

A governance harness for indefinite-horizon AI co-development.

- **Install:** `pip install sadp-harness`
- **Source + docs:** github.com/brownanan/acervator
- **License:** Apache 2.0 with patent grant

See `SKILL.md` in this directory for the Claude-facing skill definition.
EOF

# 6. Commit + push
git add skills/sadp/
git commit -m "Add SADP-harness skill (sadp-harness 1.91 on PyPI)"
git push -u origin add-sadp-harness

# 7. Open the PR — body content above
gh pr create \
    --repo anthropics/skills \
    --title "Add SADP-harness — structured AI development protocol with 60-rule core + project-overlay extension" \
    --body-file docs/anthropics_skills_pr_draft.md  # or paste manually
```

After opening, monitor the PR for maintainer review. Be prepared to:
- Trim SKILL.md if maintainers prefer compact skills
- Revise install instructions if the registry has a preferred pattern
- Provide additional usage examples on request

---

## Operator decisions to confirm before opening the PR

1. **Repo extraction first?** Some maintainers prefer skills point at standalone repos rather than subdirectories of larger ones. If `anthropics/skills` maintainers ask for this, the response is "v3.20.55+ work — happy to extract `sadp/` to a standalone github.com/brownanan/sadp-harness repo and update the SKILL.md pointer." (Currently the lineage is acervator/sadp/...)
2. **PyPI publish first?** Yes — the PR is most credible when the install command actually works. Run `tools/publish_sadp_to_pypi.py --full` before opening.
3. **GitHub identity.** Confirm `gh auth status` shows the identity you want this PR opened under. Anthony L. Brown (brownanan) is the default per the source repo provenance.

