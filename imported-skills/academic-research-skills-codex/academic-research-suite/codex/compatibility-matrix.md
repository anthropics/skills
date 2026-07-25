# ARS Codex Compatibility Matrix

Audit date: 2026-07-13

## Provenance

| Surface | Evidence |
|---|---|
| Codex package repo | `academic-research-skills-codex` current working tree before release commit |
| Upstream Claude Code repo | Tracked in `skills/academic-research-suite/manifest.json` |
| Upstream suite version | `v3.16.0` |
| Codex package version | `0.1.18` |
| License | CC BY-NC 4.0 in upstream and Codex package |
| Upstream sync status | Vendored `ars/` content synced to ARS release `v3.16.0` (`73c898c`); Codex adapter profile retained |
| Codex-only adapter location | `skills/academic-research-suite/codex/` |

## Matrix

| Capability | Default Codex Status | Optional Full-Runtime Profile | Parity Level | Implementation Location | Verification Method | Remaining Risk |
|---|---|---|---|---|---|---|
| Install / update | One Codex skill path, not a Claude plugin | No change; install remains the root skill path | partial | `README.md`, `manifest.json` | `/skills`; `single-root-skill` gate | No native Claude marketplace lifecycle in Codex |
| `ars-*` aliases | Root router emulates Claude command intent | Deterministic planner emits the same alias route metadata | near | `SKILL.md`, `codex/full-runtime-manifest.json`, `codex/scripts/ars_codex_full_runtime.py` | adapter pytest; manifest gate | Slash-prefixed input can still be intercepted by a client |
| Vague paper-topic routing | Root router sends vague paper topics to Socratic scoping | Planner preserves the same override | near | `SKILL.md`, `codex/scripts/ars_codex_full_runtime.py` | adapter pytest; upstream router tests | Natural-language routing is still heuristic outside smoke cases |
| Agent prompts | `agents/*.md` are read inline as role/phase prompts | `codex/agents/*.md` provides opt-in agent-team templates pointing back to source prompts | near | `ars/*/agents/*.md`, `codex/agents/*.md` | manifest gate; reviewer fixture gate | Actual subagent availability depends on the active Codex runtime |
| Reviewer independence | Inline mode must preserve independent reviewer sections before synthesis | Agent-team planner orders independent reviewer sections before editorial synthesis | near | `codex/agents/paper-reviewer-panel.md`, `codex/tests/fixtures/reviewer_full_independent_sections.md` | reviewer fixture gate; adapter pytest | Inline runs rely on faithfully preserving section boundaries |
| Hooks | Upstream Claude hooks are metadata only | Disabled-by-default read-only Codex hook pack | partial | `codex/hooks/hooks.json`, `codex/scripts/ars_codex_hook.py` | `hook-safety` gate | Hook installation format can differ by Codex client |
| Model routing | Claude `opus` / `sonnet` hints are metadata | Planner reports model hints without forcing model changes | partial | `codex/full-runtime-manifest.json`, `codex/scripts/ars_codex_full_runtime.py` | adapter pytest; plan inspection | Not equivalent to Claude Code model pinning |
| ARS model tiering | Unset preserves the active Codex model | Planner surfaces `economy` / `quality-boost` as advisory metadata; classification is applied only when per-dispatch model selection exists | partial | `ars/shared/model_tiering.md`, `ars/scripts/model_tiering_manifest.json`, `codex/scripts/ars_codex_full_runtime.py` | upstream tiering lint; adapter pytest | Codex runtimes may not expose relative-tier or per-dispatch model control |
| Material Passport | Prompt/procedure plus vendored validators | Full-runtime manifest exposes passport reset as a quality gate | near | `ars/scripts/check_passport_reset_contract.py`, `codex/full-runtime-manifest.json` | upstream validator; adapter gate | Runtime context isolation is procedural, not a hard sandbox |
| Citation / claim / temporal integrity | Vendored validators can be run when needed | Planner surfaces relevant gates in the route plan | partial | `ars/scripts/*claim*`, `ars/scripts/temporal_integrity_audit.py`, `codex/full-runtime-manifest.json` | upstream validators; adapter tests | External metadata/API checks require configuration |
| Cross-model verification | Disabled by default; explicit provider configuration and user consent required | Same behavior; unavailable verifier must be reported rather than invented | partial | `README.md`, `SKILL.md`, `ars/shared/cross_model_verification.md`, `codex/full-runtime-manifest.json` | manual inspection | External-provider availability depends on user-supplied API credentials |
| Upstream lock provenance | `manifest.json` pins upstream commits | Quality gate checks the package manifest has a full upstream SHA and required included paths | near | `manifest.json`, `codex/scripts/ars_codex_quality_gates.py` | `upstream-lock` gate | Future upstream syncs still require deliberate manifest updates |

## Exact Degradations Relative To Claude Code

- Codex does not register native Claude slash commands; `ars-*` aliases are
  parsed by the root skill and optional full-runtime planner.
- Codex full-runtime agent-team mode is opt-in and planner/template based.
  Inline execution remains the default.
- Claude Code plugin marketplace install/update is not reproduced.
- Claude Code `SessionStart` and future `SubagentStop` hooks are not installed
  automatically. The Codex hook pack is manual and read-only.
- `opus` / `sonnet` command frontmatter is preserved as metadata; the active
  Codex model is used unless the user/runtime provides an explicit override.
- `ARS_MODEL_TIERING` preserves the upstream agent classification, but cannot
  force economy or quality-boost routing without a runtime model override.
- External cross-model verification is never simulated silently.
