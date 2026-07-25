#!/usr/bin/env python3
"""ARS write-scope guard — PreToolUse hook (#134 Slice 1, the MVP).

Spec: docs/design/2026-06-01-ars-134-conductor-rescope-deterministic-write-guard-spec.md

Blocks out-of-scope file writes by the 23 Bucket A single-phase subagents, backed by
the machine-readable scope manifest at scripts/ars_phase_scope_manifest.json.

COVERAGE CLAIM — stated precisely, NOT over-promised (spec §3.3 / §7):
  * DETERMINISTIC for the structured editing tools (Write / Edit / MultiEdit): a write
    outside the agent's declared scope is denied regardless of the agent's prompt. This is
    the load-bearing win.
  * Bash for Bucket A agents: DENIED WHOLESALE. A single-phase agent may not run any Bash;
    it uses the Grep/Glob tools to search and Write/Edit/MultiEdit to write. Six review
    rounds established WHY nothing finer is sound: neither "this Bash writes a file" (a
    denylist — `python -c`/`sh -c`/`make`/custom scripts all write, unenumerable) nor "this
    Bash is read-only" (an allowlist — `rg --pre`/`git grep -O`/`sort --compress-program`/
    `GIT_EXTERNAL_DIFF=…` all execute subprocesses, and "read-only" varies by flag, env, and
    binary version) can be decided reliably from a command string without a sandbox. All-deny
    is the only Bash policy that reaches ZERO fail-open by construction. The cost is a clean
    false-deny of ad-hoc read-only Bash, which the agent does not need (it has Grep/Glob).
  This is NOT "deterministic enforcement of all writes" — it is deterministic for the
  structured tools plus a clean wholesale Bash deny for fenced agents. The honest win is
  making the #133 shape (a helpful agent calling a write tool into a downstream phase dir)
  deterministically impossible, and closing the direct-shell-write path for Bucket A entirely.

The testable core is `evaluate_decision(payload, manifest, workspace_root)` — a pure
function. `main()` only wires stdin -> evaluate_decision -> stdout JSON.

PAYLOAD CONTRACT (first-party verified against official Claude Code hook docs 2026-06-01):
  Available: session_id, transcript_path, cwd, permission_mode, hook_event_name, effort,
  tool_name, tool_input, plus subagent-conditional agent_id / agent_type. `agent_type`
  equals the subagent's frontmatter `name` (e.g. "bibliography_agent"). `tool_use_id` is
  NOT a payload field — do not rely on it.

TOOL_INPUT SHAPES: Write / Edit / MultiEdit each carry a SINGLE top-level `file_path`.
  Write: {file_path, content}; Edit: {file_path, old_string, new_string};
  MultiEdit: {file_path, edits:[{old_string,new_string},...]} — edits[] is multiple
  edits to that ONE file, NOT multiple distinct paths. Bash: {command}.
  (Official hooks input table does not enumerate MultiEdit; the single-top-level-file_path
  shape is taken from the tool definition. The path-extraction below reads ONLY the
  top-level file_path and FAILS LOUD if a structured write tool ever lacks one — so a
  schema drift cannot silently fail the guard open.)
"""

import fnmatch
import json
import os
import sys
from pathlib import Path

MANIFEST_FILENAME = "ars_phase_scope_manifest.json"

# Structured editing tools: deterministic, single top-level file_path. The 23 Bucket A
# agents emit markdown / yaml / bib / txt into their phase dir via these three tools;
# NotebookEdit is deliberately out of Slice 1 scope (no Bucket A agent writes notebooks,
# and its hook input shape is unverified — adding it would be speculative coverage).
STRUCTURED_WRITE_TOOLS = {"Write", "Edit", "MultiEdit"}

# Tools the guard inspects at all. Everything else -> allow (out of scope).
INSPECTED_TOOLS = STRUCTURED_WRITE_TOOLS | {"Bash"}

# Step 2 infrastructure self-protection — normalized workspace-relative path patterns
# that NO agent (and not even the unconstrained main session) may write. These are the
# enforcement surface: tampering with them would fail the guard open.
INFRA_PROTECTED_GLOBS = [
    "hooks/hooks.json",
    "hooks/*.sh",
    ".claude-plugin/plugin.json",  # declares the hook routing — disabling it neuters the guard
    # The hook script, its manifest, and the cross-check lint, protected by filename both
    # in any SUBDIR (`**/name`) AND at the workspace root (bare `name`). A deny-list
    # widening only protects MORE paths, so it is safe — unlike a per-agent allow-glob
    # widening, which would loosen scope. Covering both forms ensures a future directory
    # move can't fail the guard open (spec §3.2: "the hook script and any helper modules
    # it imports"). (`**/name` matches subdirs only, not root — see _matches_any — so the
    # bare entries are load-bearing for a root-level copy, not redundant.)
    "**/ars_write_scope_guard.py",
    "ars_write_scope_guard.py",
    "**/ars_phase_scope_manifest.json",
    "ars_phase_scope_manifest.json",
    "**/check_v3_10_134_write_scope.py",  # the three-way name cross-check lint
    "check_v3_10_134_write_scope.py",
    # Agent definition files: the agent_type==name binding lives in their frontmatter;
    # renaming an agent out of the manifest would fail the guard open. Covers the per-skill
    # source dirs, the shared dir, AND the top-level plugin-shipped `agents/` dir (the
    # #413-materialized byte-identical copies — these carry the same name binding and were
    # previously unprotected; closed in #448 when the plugin-root anchoring re-established
    # which files count as plugin infra).
    "deep-research/agents/*.md",
    "academic-paper/agents/*.md",
    "academic-paper-reviewer/agents/*.md",
    "academic-pipeline/agents/*.md",
    "shared/agents/*.md",
    "agents/*.md",
    # CLAUDE.md / .claude/CLAUDE.md are DELIBERATELY NOT protected (#459). They were
    # added to guard ARS's own repo CLAUDE.md, but two generic doc filenames collide
    # with the user's own project under the clone+symlink install layout: there
    # CLAUDE_PLUGIN_ROOT is unset, the plugin_root fallback resolves to the cloned repo
    # root, and a user working IN that repo has plugin_root == workspace_root — so their
    # own CLAUDE.md sits at plugin_root and the infra glob re-denied it (the #448 bug
    # resurfacing on a layout the #449 plugin-root anchoring can't distinguish, because
    # home-turf and clone-as-user are the SAME runtime condition). Unlike every entry
    # above, CLAUDE.md is NOT load-bearing: it documents the guard binding, it is not the
    # binding — editing it cannot fail the guard open. So protecting it bought soft-policy
    # comfort at the cost of a hard false-deny for real users. The right home for "don't let
    # an agent rewrite ARS's own instruction doc" is review / CI, not the write-scope guard,
    # which must protect ENFORCEMENT files only. See #459 (and #448/#449 for the history).
]


def _normalize_target(raw_path, cwd, workspace_root):
    """Step 1 — resolve to a workspace-root-relative canonical path.

    Returns (rel_path, escaped_workspace). rel_path is None when the target escapes
    the workspace root (path traversal); escaped_workspace is True then.

    Resolves symlinks on the existing parent chain WITHOUT requiring the leaf to exist
    (the write may create it), so a `phase2_x/../hooks/hooks.json` raw path is
    canonicalized to `hooks/hooks.json` BEFORE any deny-list / glob match runs.
    """
    if not os.path.isabs(raw_path):
        raw_path = os.path.join(cwd, raw_path)
    # CRITICAL: do NOT os.path.abspath() first — abspath collapses `..` LEXICALLY, which
    # would resolve `symlinked_dir/../x` to a sibling of symlinked_dir's *name* before the
    # symlink is followed, blinding the guard to the real target (caught in review). Instead
    # os.path.realpath() resolves symlinks AND `..` together in true filesystem order. It
    # tolerates a not-yet-created leaf (resolving the existing prefix and appending the
    # rest), so a brand-new file path still canonicalizes correctly.
    normalized = os.path.realpath(raw_path)

    real_ws = os.path.realpath(workspace_root)
    try:
        common = os.path.commonpath([normalized, real_ws])
    except ValueError:
        # Different drives / mixed abs-rel — treat as escape.
        return None, True
    if common != real_ws:
        return None, True
    rel = os.path.relpath(normalized, real_ws)
    # `commonpath(...) == real_ws` already proves the path did not escape; do NOT also
    # reject `rel.startswith("..")` — that would false-deny a legitimate root-level file
    # literally named `..foo` (caught in review). Only the workspace root itself (rel == ".")
    # is not a writable target.
    if rel == ".":
        return None, True
    return rel, False


def _match_segments(path_segs, pat_segs):
    """Path-segment-aware glob match. A `*` / `?` / `[...]` matches only WITHIN one
    segment (never across `/`); the literal segment `**` matches ONE OR MORE whole
    segments (a descendant — NOT zero, so `dir/**` covers files UNDER dir, not the bare
    dir node itself). This gives `dir/**` and `**/name` their intended PATH semantics —
    unlike bare fnmatch, whose `*` spans `/` and would let a root-level `phase2_x.md` match
    `phase2_*` (the false-open regression caught at review).

    ITERATIVE (NFA-style) matcher over (path_index, pattern_index) states — NOT recursive.
    A `**` previously recursed once per consumed segment, blowing Python's recursion limit
    (~1000) on a deep path and crashing the hook (caught in review). The worklist keeps a
    visited set so it is O(len(path) * len(pattern)) and cannot stack-overflow at any depth.
    """
    n, m = len(path_segs), len(pat_segs)
    # State = (i, j): path_segs[i:] still to match against pat_segs[j:].
    stack = [(0, 0)]
    seen = set()
    while stack:
        i, j = stack.pop()
        if (i, j) in seen:
            continue
        seen.add((i, j))
        if j == m:
            if i == n:
                return True
            continue  # pattern exhausted but path remains -> this branch fails
        head = pat_segs[j]
        if head == "**":
            # `**` consumes ONE OR MORE segments. So it requires >=1 remaining path segment,
            # then may consume just that one (advance both) or keep consuming (advance path
            # only). A trailing `**` (j == m-1) therefore needs >=1 remaining segment — so
            # `dir/**` matches a descendant, never the bare `dir` node; a leading `**/name`
            # matches name in any subdir but NOT at root (the bare INFRA pattern covers root).
            if i < n:
                stack.append((i + 1, j + 1))  # `**` ate exactly this segment
                stack.append((i + 1, j))      # `**` keeps eating
            continue
        # A literal segment pattern: needs a path segment that fnmatches it.
        if i < n and fnmatch.fnmatch(path_segs[i], head):
            stack.append((i + 1, j + 1))
    return False


def _matches_any(rel_path, globs):
    """Workspace-root-anchored glob match against the normalized relative path.

    Path-segment-aware (a `*` never crosses `/`). Conventions:
      * `dir/**`  — anything strictly UNDER `dir` (>=1 segment below). The bare `dir`
                    node is intentionally NOT matched: every real Bucket A write is to a
                    FILE inside its phase dir, and matching the bare single-segment path
                    would let a root file `phase2_x.md` masquerade as the `phase2_*` dir
                    (the false-open caught at review).
      * `**/name` — `name` in any subdirectory. For a file that may ALSO live at the
                    workspace root, the INFRA list carries both `**/name` and the bare
                    `name` (a deny-list, so widening is safe — see INFRA_PROTECTED_GLOBS).
    """
    # Glob patterns are authored with `/`; segment-split the path on the same separator.
    # On Windows, rel_path (from os.path.relpath) uses `\`, so normalize `\` -> `/` THERE.
    # On POSIX this MUST stay a no-op: `\` is a LEGAL filename character, so an
    # unconditional replace would rewrite a root-level file literally named
    # `phase2_x\notes.md` (one segment) into `phase2_x/notes.md` (two segments) and let it
    # masquerade as the `phase2_*` dir — a fence-escape false-allow (#330 PR #450 caught by
    # cross-model review). Gate on os.sep so the rewrite only fires where `\` is a separator.
    if os.sep == "\\":
        rel_path = rel_path.replace("\\", "/")
    segs = [s for s in rel_path.split("/") if s not in ("", ".")]
    for g in globs:
        pat = [s for s in g.split("/") if s != ""]
        if _match_segments(segs, pat):
            return True
    return False


def _infra_protected_target(raw_path, cwd, plugin_root):
    """Step 2 — is the write target one of the ARS plugin's OWN enforcement files?

    #448 root-cause fix: infra self-protection must be anchored to the PLUGIN root, not
    the user's PROJECT root. The two enforcement surfaces have different anchors:
      * Bucket A phase-scope (Step 4) fences agents to their phaseN_ dir inside the USER'S
        project — anchored on workspace_root (= CLAUDE_PROJECT_DIR).
      * Infra self-protection (here) protects the ARS plugin's own files from tampering —
        those live under the plugin install dir, so it MUST be anchored on plugin_root.
    Conflating them was the bug: matching the plugin's infra filenames (`CLAUDE.md`,
    `hooks/*.sh`, `shared/agents/*.md`, ...) against a user PROJECT path denied the user's
    own same-named files — even from the trusted main session.

    A target is an infra target IFF it resolves INSIDE plugin_root AND its plugin-root-
    relative path matches INFRA_PROTECTED_GLOBS. A target outside plugin_root (the normal
    case in a user project where plugin_root != workspace_root) is never an infra target.

    A None plugin_root here returns False ("no infra root known -> not infra-protected").
    evaluate_decision never calls in with None — it substitutes workspace_root first — so
    this is a pure defensive guard, not a path any real caller exercises.
    """
    if not plugin_root:
        return False
    # Resolve the target the SAME way _normalize_target does (realpath, tolerant of a
    # not-yet-created leaf), but anchored on plugin_root instead of workspace_root.
    rp = raw_path
    if not os.path.isabs(rp):
        rp = os.path.join(cwd, rp)
    normalized = os.path.realpath(rp)
    real_plugin = os.path.realpath(plugin_root)
    try:
        common = os.path.commonpath([normalized, real_plugin])
    except ValueError:
        return False  # different drives -> cannot be inside plugin root
    if common != real_plugin:
        return False  # target resolves OUTSIDE the plugin root -> not an infra file
    rel = os.path.relpath(normalized, real_plugin)
    if rel == ".":
        return False  # the plugin root dir itself is not an enumerated infra FILE
    return _matches_any(rel, INFRA_PROTECTED_GLOBS)


def _allow_unconstrained(agent_type):
    """The decision for an actor that Slice 1 does not fence (main session / Bucket B/C/D).

    Single source for both the escaped-path allow (#302) and the Step-3 allow, so the two
    can't drift. A write tool firing with NO agent_type still surfaces a fail-loud advisory
    (spec §3.4) — do not silently no-op a possibly-regressed payload.
    """
    result = {"decision": "allow", "reason": ""}
    if not agent_type:
        result["absent_agent_type_advisory"] = True
    return result


def _extract_structured_target(tool_input):
    """Single top-level file_path for Write/Edit/MultiEdit.

    Returns the file_path string, or None if absent (schema drift -> fail loud upstream).
    """
    if not isinstance(tool_input, dict):
        return None
    fp = tool_input.get("file_path")
    return fp if isinstance(fp, str) and fp else None


def evaluate_decision(payload, manifest, workspace_root, plugin_root=None):
    """Pure decision function implementing the spec §3.2 logic (Bash policy per §7, shipped).

    Returns a dict: {"decision": "allow"|"deny", "reason": str, ...advisory flags}.

    Two enforcement paths:
      * Structured tools (Write/Edit/MultiEdit) — deterministic write-scope: extract the
        single top-level file_path, run infra self-protection FIRST (anchored on plugin_root,
        #448), then normalize against workspace_root for the escape check, then Bucket A glob.
      * Bash — DENY ALL for a Bucket A agent (spec §3.2 Step-4 hardening: neither a denylist
        of "mutation-capable" Bash nor an allowlist of "read-only" Bash is sound, because
        neither property is stable across commands/flags/env/versions; only all-deny reaches
        zero fail-open by construction). The agent uses the Grep/Glob tools for search and the
        structured tools for writes. Non-Bucket-A Bash passes through.

    plugin_root (#448): the ARS plugin install dir, used to anchor infra self-protection
    (Step 2). main() ALWAYS supplies a concrete root (CLAUDE_PLUGIN_ROOT or the resolved
    repo root), so the None default exists only for the ARS-on-ARS unit tests and for any
    caller that genuinely cannot determine a plugin root.

    When None, infra protection falls back to workspace_root. This is correct ONLY when the
    plugin and the workspace are the same tree (ARS developing ARS): it then reproduces the
    pre-#448 behavior byte-for-byte. It is NOT a safe default under a real plugin install
    (plugin_root != workspace_root) — there it would both re-deny the user's own CLAUDE.md
    and FAIL to protect plugin infra (those files are mere workspace escapes). So a real
    runtime caller MUST pass plugin_root; do not rely on this fallback off the home turf.
    """
    if not plugin_root:
        plugin_root = workspace_root
    # The pure core defends itself too — not only main() — so a non-dict payload (`[]`,
    # null, a string) passed straight to evaluate_decision can't crash on `.get` (review).
    if not isinstance(payload, dict):
        return {"decision": "allow", "reason": ""}
    tool_name = payload.get("tool_name", "")
    tool_input = payload.get("tool_input")
    if not isinstance(tool_input, dict):  # [] / null / str -> treat as empty (no crash)
        tool_input = {}
    cwd = payload.get("cwd") or workspace_root
    agent_type = payload.get("agent_type")
    agents = (manifest or {}).get("agents", {})
    is_bucket_a = bool(agent_type) and agent_type in agents

    # Tools we don't inspect (Read, Grep, WebFetch, ...) -> allow.
    if tool_name not in INSPECTED_TOOLS:
        return {"decision": "allow", "reason": ""}

    # --- Bash path: DENY ALL Bash for a Bucket A agent. Non-Bucket-A Bash passes through. ---
    if tool_name == "Bash":
        if is_bucket_a:
            return {
                "decision": "deny",
                "reason": (f"ARS scope guard: {agent_type} (a single-phase agent) may not use "
                           "Bash. Use the Grep/Glob tools to search and the Write/Edit/MultiEdit "
                           "tools to make file changes — those are scope-enforced deterministically. "
                           "Bash is denied wholesale because neither 'writes a file' nor 'is "
                           "read-only' is a property that can be decided reliably from a command "
                           "string (a tool can spawn a subprocess or be steered by an env var); "
                           "all-deny is the only policy that cannot fail open (spec §3.2/§3.3/§7)."),
                "bash_denied": True,
            }
        # Non-Bucket-A (main session / Bucket B/C/D) Bash -> pass through unconstrained.
        return {"decision": "allow", "reason": ""}

    # --- Structured tools: Step 1 extract + normalize the single top-level file_path. ---
    raw = _extract_structured_target(tool_input)
    if raw is None:
        # Schema drift: a structured write tool with no top-level file_path. Do NOT
        # silently allow — fail loud (deny + advisory) so the guard cannot fail open.
        return {
            "decision": "deny",
            "reason": (f"ARS scope guard: {tool_name} payload carried no top-level "
                       "file_path (unexpected schema) — denying to avoid silent "
                       "fail-open. Re-verify the tool_input shape."),
            "schema_drift_advisory": True,
        }
    # --- Step 2: infrastructure self-protection (anchored on plugin_root). RUNS FIRST,
    #     BEFORE the user-workspace escape check. ---
    # #448: anchored on the PLUGIN root, not the user's PROJECT root. Two reasons it must
    # precede the escape check:
    #   (a) Under a plugin install, the plugin's own files live OUTSIDE the user workspace,
    #       so they are "escaped" relative to workspace_root — the escape branch would let a
    #       main-session write to them through. Checking infra first keeps them protected
    #       wherever they physically sit.
    #   (b) A target inside the USER's project that merely shares a filename with an ARS infra
    #       file (the user's own CLAUDE.md / hooks/*.sh / shared/agents/*.md) resolves OUTSIDE
    #       plugin_root, so _infra_protected_target returns False and it is left to Step 3/4 —
    #       which is exactly the #448 fix.
    # _infra_protected_target resolves the target on its own (realpath, anchored on
    # plugin_root) so it is correct regardless of the workspace-relative `escaped` flag.
    if _infra_protected_target(raw, cwd, plugin_root):
        return {
            "decision": "deny",
            "reason": (f"ARS scope guard: {raw} is part of the ARS plugin's enforcement "
                       "infrastructure and may not be written by any agent."),
        }

    rel, escaped = _normalize_target(raw, cwd, workspace_root)
    if escaped:
        # The escape / path-traversal deny is a BUCKET A FENCE, not a global one (#302).
        # Slice 1's stated scope (§3.3) is confining the 23 Bucket A single-phase agents to
        # their phase dir; the main session and Bucket B/C/D agents are unconstrained. A
        # main-session write to a sibling git worktree (a mainstream layout) resolves outside
        # the workspace root and MUST be allowed — fencing it here contradicted the Step-3
        # "unconstrained by Slice 1" gate below. So: only a Bucket A agent is denied for an
        # escape; a non-Bucket-A actor falls through to the Step-3 allow.
        #   Infra self-protection already ran above (anchored on plugin_root), so an escaped
        # target that is an ARS plugin file was already denied; what remains here is a genuine
        # non-infra escape (e.g. a sibling worktree), correctly allowed for non-Bucket-A.
        if is_bucket_a:
            return {
                "decision": "deny",
                "reason": (f"ARS scope guard: {agent_type} write target {raw!r} escapes the "
                           "workspace root (path traversal) — denied."),
            }
        return _allow_unconstrained(agent_type)

    # --- Step 3: agent gating. ---
    if not is_bucket_a:
        # Main session or a Bucket B/C/D agent: unconstrained by Slice 1.
        return _allow_unconstrained(agent_type)

    # --- Step 4: Bucket A glob check (path already normalized in Step 1). ---
    allowed = agents[agent_type].get("allowed_write_globs", [])
    if not _matches_any(rel, allowed):
        return {
            "decision": "deny",
            "reason": (f"ARS scope guard: {agent_type} may not write {rel} "
                       f"(outside allowed_write_globs {allowed})."),
        }
    return {"decision": "allow", "reason": ""}


def render_hook_output(decision):
    """Render the PreToolUse stdout JSON.

    DENY -> explicit `permissionDecision: "deny"` (spec §3.2 first-party-verified schema).
    Non-deny -> PASS-THROUGH: emit NO permissionDecision, so the call falls back to the
    normal permission flow. Emitting `"allow"` here would be an explicit GRANT that skips
    every other permission rule (review finding) — a guard that only ADDS denials must never
    silently widen what the rest of the permission system would otherwise have asked about.
    """
    if decision.get("decision") == "deny":
        return json.dumps({
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "deny",
                "permissionDecisionReason": decision.get("reason", ""),
            }
        })
    # Pass-through: a bare hookSpecificOutput with no permissionDecision key.
    return json.dumps({"hookSpecificOutput": {"hookEventName": "PreToolUse"}})


def _load_manifest():
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, MANIFEST_FILENAME)
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def main():
    try:
        payload = json.load(sys.stdin)
    except (json.JSONDecodeError, ValueError):
        # Malformed payload: do not block (avoid wedging the session); pass through.
        print(render_hook_output({"decision": "allow", "reason": ""}))
        return 0

    # Valid JSON of the wrong SHAPE ([], null, a string) must not wedge the session either
    # — only a JSON object carries a tool call (review finding: payload.get would crash).
    if not isinstance(payload, dict):
        print(render_hook_output({"decision": "allow", "reason": ""}))
        return 0

    # Hot-path early-exit: PreToolUse fires on EVERY tool call (Read, Grep, WebFetch...),
    # not just writes. Bail before touching the manifest on disk for the common non-write
    # case — the matcher in hooks.json already narrows to write tools, but defend here too.
    if payload.get("tool_name", "") not in INSPECTED_TOOLS:
        print(render_hook_output({"decision": "allow", "reason": ""}))
        return 0

    # Workspace root: prefer CLAUDE_PROJECT_DIR, else the payload cwd. This anchors the
    # Bucket A phase-scope check (Step 4) to the USER'S project.
    workspace_root = os.environ.get("CLAUDE_PROJECT_DIR") or payload.get("cwd") or os.getcwd()

    # Plugin root (#448): anchors infra self-protection (Step 2) to the ARS plugin's OWN
    # files, NOT the user's project. CLAUDE_PLUGIN_ROOT is set on a plugin install; the
    # git-clone+symlink track has no such env var, so fall back to this script's repo root
    # (scripts/ -> repo root, where .claude-plugin/plugin.json lives). Use resolve() (NOT
    # abspath) so a symlinked script / scripts dir — the norm for the ~/.claude/skills
    # symlink install track — resolves to the REAL plugin tree, not the symlink's location
    # (abspath would not follow the symlink and compute the wrong root).
    plugin_root = os.environ.get("CLAUDE_PLUGIN_ROOT") or str(
        Path(__file__).resolve().parents[1])

    try:
        manifest = _load_manifest()
    except (OSError, json.JSONDecodeError):
        # Manifest unreadable: fail loud to stderr (advisory) but do not wedge writes.
        sys.stderr.write("[ARS write-scope guard] manifest unreadable; passing through.\n")
        print(render_hook_output({"decision": "allow", "reason": ""}))
        return 0

    decision = evaluate_decision(payload, manifest, workspace_root, plugin_root)

    # Surface fail-loud advisories to stderr (visible to the user/transcript), never silent.
    if decision.get("absent_agent_type_advisory"):
        sys.stderr.write("[ARS write-scope guard] write tool fired with no agent_type; "
                         "allowed (main session) but surfaced per no-silent-no-op rule.\n")
    if decision.get("schema_drift_advisory"):
        sys.stderr.write("[ARS write-scope guard] structured write tool lacked a top-level "
                         "file_path; denied to avoid silent fail-open.\n")

    print(render_hook_output(decision))
    return 0


if __name__ == "__main__":
    sys.exit(main())
