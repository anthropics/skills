# #448 — Scope infra self-protection to the plugin root, not the user's project

**Status:** spec for the fix branch `fix/448-infra-protection-plugin-root`
**Affects:** `scripts/ars_write_scope_guard.py` (the #134 write-scope guard), its tests.
**Eval impact:** none (no scoring / generation / gold-set change).

## Problem

Issue #448 (two independent external reporters: `philpav`, `herman925`): after installing
the ARS plugin, Claude can no longer edit the user's own project-root `CLAUDE.md`.

### Root cause (first-party verified — codex ran the decision function)

`scripts/ars_write_scope_guard.py` is a PreToolUse hook. Step 2 of `evaluate_decision`
denies any write whose normalized path matches `INFRA_PROTECTED_GLOBS` **unconditionally**
— before agent gating, so it applies even to the trusted main session:

```python
if _infra_protected(rel):       # rel is relative to workspace_root
    return DENY
```

`workspace_root = os.environ.get("CLAUDE_PROJECT_DIR") or payload.cwd or os.getcwd()`.

Under a plugin install, `CLAUDE_PROJECT_DIR` is the **user's project**, not the ARS plugin
directory (`CLAUDE_PLUGIN_ROOT`). `INFRA_PROTECTED_GLOBS` carries `"CLAUDE.md"` and
`".claude/CLAUDE.md"` to protect ARS's *own* repo CLAUDE.md (which describes the guard
binding) from being edited by an agent. But matched against the *user's* project root, the
user's own `CLAUDE.md` matches and is denied — even from the main session. That is the bug.

### Scope is wider than `CLAUDE.md`

`CLAUDE.md` is merely the first entry users hit. The real defect is a **root-boundary
error**: Step 2 matches *plugin* infra filenames against *user-project* paths. Other infra
entries that can plausibly also exist in a user repo — `hooks/hooks.json`, `hooks/*.sh`,
`.claude-plugin/plugin.json`, and especially `shared/agents/*.md` — would be misfired the
same way. The fix must address the boundary, not just `CLAUDE.md`.

## Design (Fix C — dual root)

The two enforcement surfaces have **different anchors**, and conflating them is the bug:

- **Bucket-A phase-scope** (Step 4) fences the 23 single-phase agents to *their own
  phaseN_ dir inside the user's project*. Anchor: `workspace_root` (= `CLAUDE_PROJECT_DIR`).
  **Unchanged.**
- **Infra self-protection** (Step 2) protects *the ARS plugin's own enforcement files* from
  tampering. Those files live under the plugin install dir. Anchor: **`plugin_root`**.

### Changes

1. `evaluate_decision(payload, manifest, workspace_root, plugin_root)` gains a `plugin_root`
   parameter (pure function, fully testable). `plugin_root` may be `None` (callers that
   cannot determine it — see #4) → infra protection still runs against `workspace_root` as
   the conservative fallback (preserves the pre-fix protective behavior when the plugin and
   project root coincide, e.g. ARS developing ARS).

2. Step 2 becomes plugin-root-scoped. Resolve the write target's real absolute path once.
   It is an infra target **iff** it resolves inside `plugin_root` AND its plugin-root-relative
   path matches `INFRA_PROTECTED_GLOBS`. A target outside `plugin_root` (the normal case for
   a user project where plugin_root ≠ workspace_root) is never an infra target.

3. When `plugin_root == workspace_root` (ARS repo developing itself, or fallback), behavior
   is **byte-equivalent to pre-fix**: every infra glob still matches at the workspace root,
   so the guard still protects its own files during ARS development. The fix only *narrows*
   the false-positive on a *separate* user project — it does not loosen self-protection on
   the home turf.

4. `main()` computes `plugin_root` from `os.environ.get("CLAUDE_PLUGIN_ROOT")`, else
   `Path(__file__).resolve().parents[1]` (scripts/ → repo root; `.claude-plugin/plugin.json`
   lives there, confirming it is the plugin root). This is robust for both install tracks
   (plugin via `CLAUDE_PLUGIN_ROOT`; git-clone+symlink via the file location).

### Why not Fix A (remove CLAUDE.md from infra, deny only for Bucket A)

A only patches `CLAUDE.md`; the same root-boundary defect remains for `hooks/*.sh`,
`shared/agents/*.md`, etc. in a user project. It treats the symptom. (codex concurred.)

### Why not Fix B (fingerprint the ARS repo by a sibling file)

Brittle: false positives in vendored/copied projects, false negatives if the layout moves,
undefined in monorepos / nested ARS checkouts, and extra filesystem work on the hot path.
It also treats a symptom rather than the boundary. (codex concurred.)

## Threat-model check (does Fix C reopen the guard-disable path?)

The infra protection exists so a Bucket A agent cannot edit ARS's own enforcement files to
neuter the guard. Under Fix C those files are still protected because they resolve inside
`plugin_root`. A Bucket A agent in a user project:

- Cannot write outside its `phaseN_` dir (Step 4, unchanged) — so it cannot reach a
  user-project-root `CLAUDE.md` anyway.
- Cannot run Bash at all (wholesale deny, unchanged).
- Cannot reach the plugin's own files unless they happen to sit inside a phase dir (they do
  not).

So Fix C does not reopen any real attack path. The only behavior it *changes* is: the **main
session** (and Bucket B/C/D) in a **user project** may now edit that project's own
`CLAUDE.md` / `hooks/*.sh` / `shared/agents/*.md` — which they always should have been able
to, and which they could already do via Bash regardless.

## Test plan (red → green)

New cases in `scripts/test_ars_write_scope_guard.py`, all with `plugin_root != workspace_root`:

1. **RED before fix:** main session writes `<workspace>/CLAUDE.md` with
   `plugin_root=<elsewhere>` → must be ALLOW (pre-fix: DENY).
2. main session writes `<workspace>/.claude/CLAUDE.md` → ALLOW.
3. main session writes `<workspace>/shared/agents/foo.md` → ALLOW (user project collision).
4. main session writes `<workspace>/hooks/hooks.json` → ALLOW (user project).
5. **Self-protection preserved:** any actor writes `<plugin_root>/CLAUDE.md` (target inside
   plugin root) → DENY. (Set `workspace_root == plugin_root` to model ARS-on-ARS, OR pass a
   target that resolves into plugin_root.)
6. **Self-protection preserved:** write `<plugin_root>/scripts/ars_write_scope_guard.py` → DENY.
7. **Fallback:** `plugin_root=None` with target `<workspace>/CLAUDE.md` → DENY (conservative,
   == pre-fix).
8. **Bucket A unchanged:** bucket-A agent writing its own `phase2_x/notes.md` → ALLOW;
   writing `phase3_x/notes.md` → DENY (phase-scope intact).

All existing tests must still pass (the manifest-driven phase-scope behavior is untouched).
