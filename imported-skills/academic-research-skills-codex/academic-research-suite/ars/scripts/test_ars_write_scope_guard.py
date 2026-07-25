"""TDD test suite for the ARS write-scope guard PreToolUse hook (#134 Slice 1).

Spec: docs/design/2026-06-01-ars-134-conductor-rescope-deterministic-write-guard-spec.md (§3.4).

The hook's testable core is `evaluate_decision(payload, manifest, workspace_root,
plugin_root=None)`, a pure function returning a decision dict {"decision": ..., "reason": ...}.
`main()` only wires stdin -> evaluate_decision -> stdout JSON (now also covered by
MainPluginRootComputationTest, which exercises the CLAUDE_PLUGIN_ROOT plumbing #448 added).

Decision semantics under test (spec §3.2 logic, amended by #448 dual-root anchoring):
  Step 2: infrastructure self-protection — RUNS FIRST, anchored on plugin_root (NOT the
          workspace): a target is infra IFF it resolves inside the ARS plugin install dir
          AND its plugin-relative path matches INFRA_PROTECTED_GLOBS. A user-project file
          that merely shares a filename (their own CLAUDE.md, hooks/*.sh, ...) is NOT infra.
  Step 1: normalize the write target against workspace_root (absolute + symlink resolve +
          workspace commonpath + escape detection -> workspace-root-relative canonical).
  Step 3: agent gating (Bucket A agent_type -> enforce allowed_write_globs;
          absent/non-Bucket-A -> allow, but fail-loud-log absent agent_type write).
  Step 4: tool-specific (Write/Edit/MultiEdit single top-level file_path;
          Bash deny-all for a Bucket A agent, pass-through for non-Bucket-A — neither a
          denylist nor an allowlist of Bash is sound, so all-deny is the only zero-fail-open
          policy).

Tests build a REAL workspace dir tree under tmp so normalization runs against the
real filesystem (no os.path mocking).
"""

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # scripts/ -> repo root

import ars_write_scope_guard as guard  # noqa: E402


# A minimal in-test manifest mirroring the real shape (keys = frontmatter name).
TEST_MANIFEST = {
    "version": 1,
    "agents": {
        "bibliography_agent": {
            "bucket": "A",
            "skill": "deep-research",
            "phase": "2",
            "allowed_write_globs": ["phase2_*/**"],
        },
        "synthesis_agent": {
            "bucket": "A",
            "skill": "deep-research",
            "phase": "3",
            "allowed_write_globs": ["phase3_*/**"],
        },
        "formatter_agent": {
            "bucket": "A",
            "skill": "academic-paper",
            "phase": "7",
            "allowed_write_globs": ["phase7_*/**"],
        },
        # Deliberately-broad glob agent: still must lose to Step 2 self-protection.
        "broad_test_agent": {
            "bucket": "A",
            "skill": "test",
            "phase": "X",
            "allowed_write_globs": ["**"],
        },
    },
}


def payload(tool_name, tool_input, cwd, agent_type=None, agent_id=None):
    p = {
        "session_id": "test",
        "cwd": cwd,
        "hook_event_name": "PreToolUse",
        "tool_name": tool_name,
        "tool_input": tool_input,
    }
    if agent_type is not None:
        p["agent_type"] = agent_type
    if agent_id is not None:
        p["agent_id"] = agent_id
    return p


def symlink_or_skip(testcase, target, link_name):
    """os.symlink, but skip the test on a Windows host without symlink privilege
    (WinError 1314) instead of failing — the symlink-resolution tests are about realpath
    behavior, not about whether the CI host granted SeCreateSymbolicLinkPrivilege."""
    try:
        os.symlink(target, link_name)
    except (OSError, NotImplementedError) as exc:
        if getattr(exc, "winerror", None) == 1314:
            testcase.skipTest("Windows symlink privilege is not available")
        raise


class WriteScopeGuardTest(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.ws = os.path.realpath(self._tmp.name)  # workspace root
        # Build real phase dirs so normalization resolves real parents.
        for d in ("phase2_investigation", "phase3_analysis", "phase7_format", "hooks", "scripts"):
            os.makedirs(os.path.join(self.ws, d), exist_ok=True)

    def tearDown(self):
        self._tmp.cleanup()

    def decide(self, p):
        return guard.evaluate_decision(p, TEST_MANIFEST, self.ws)

    # --- Step 4 / Step 3: structured-tool in-scope vs out-of-scope ---

    def test_in_scope_write_allowed(self):
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase2_investigation/annotated_bib.md"), "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")

    def test_out_of_scope_write_denied(self):
        # bibliography_agent (phase 2) writing into phase3 dir = the #133 shape.
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase3_analysis/synthesis.md"), "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        d = self.decide(p)
        self.assertEqual(d["decision"], "deny")
        self.assertIn("bibliography_agent", d["reason"])

    def test_in_scope_edit_allowed(self):
        p = payload("Edit",
                    {"file_path": os.path.join(self.ws, "phase3_analysis/synthesis.md"),
                     "old_string": "a", "new_string": "b"},
                    cwd=self.ws, agent_type="synthesis_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")

    def test_out_of_scope_multiedit_denied_via_top_level_file_path(self):
        # MultiEdit carries a SINGLE top-level file_path + edits[]; the path check
        # must use that top-level file_path, not a non-existent per-edit path array.
        p = payload("MultiEdit",
                    {"file_path": os.path.join(self.ws, "phase2_investigation/bib.md"),
                     "edits": [{"old_string": "a", "new_string": "b"},
                               {"old_string": "c", "new_string": "d"}]},
                    cwd=self.ws, agent_type="synthesis_agent")  # phase3 agent, writing phase2
        d = self.decide(p)
        self.assertEqual(d["decision"], "deny")

    def test_in_scope_multiedit_allowed(self):
        p = payload("MultiEdit",
                    {"file_path": os.path.join(self.ws, "phase3_analysis/synthesis.md"),
                     "edits": [{"old_string": "a", "new_string": "b"}]},
                    cwd=self.ws, agent_type="synthesis_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")

    # --- Bash policy: DENY ALL Bash for a Bucket A agent; non-Bucket-A Bash passes
    #     through unconstrained. ---

    def test_bash_denied_wholesale_for_bucket_a(self):
        # EVERY Bash command is denied for a Bucket A agent regardless of content — the only
        # policy that reaches zero fail-open by construction (neither "writes a file" nor "is
        # read-only" is decidable from a command string). One representative per class here
        # (+ the deny flag); the exhaustive historical-bypass list lives in
        # BashBypassRegressionTest.test_all_historical_bash_bypasses_denied.
        for cmd in ("rm x",                       # plainly writing
                    "python make_synthesis.py",   # interpreter (no denylist could enumerate)
                    "grep foo f",                 # looks read-only — still denied
                    "rg --pre 'sh -c touch' x f"):  # "read-only" tool that executes a subprocess
            p = payload("Bash", {"command": cmd}, cwd=self.ws, agent_type="bibliography_agent")
            d = self.decide(p)
            self.assertEqual(d["decision"], "deny", f"{cmd!r} should deny (all-Bash-deny)")
            self.assertTrue(d.get("bash_denied"), f"{cmd!r} should set bash_denied")

    def test_bash_deny_reason_routes_to_structured_and_search_tools(self):
        # The deny reason must tell the agent what to use instead (Grep/Glob + structured).
        p = payload("Bash", {"command": "grep foo f"}, cwd=self.ws, agent_type="bibliography_agent")
        reason = self.decide(p)["reason"].lower()
        self.assertIn("grep", reason)
        self.assertIn("write/edit", reason.replace(" ", ""))

    def test_bash_allowed_for_non_bucket_a(self):
        # A non-Bucket-A agent / main session is unconstrained — ANY Bash passes (the guard
        # only fences the 23 single-phase agents). Covers a named non-bucket-A agent and the
        # absent-agent_type main session.
        p = payload("Bash", {"command": "cp a b"}, cwd=self.ws, agent_type="report_compiler_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")
        p2 = payload("Bash", {"command": "rm x"}, cwd=self.ws)  # no agent_type (main session)
        self.assertEqual(self.decide(p2)["decision"], "allow")

    # --- Step 2: infrastructure self-protection (anchored on plugin_root; these tests use
    #     the 3-arg fallback where plugin_root collapses to workspace_root, so the plugin's
    #     own infra files sit at the workspace root and are denied for EVERY actor. The
    #     plugin_root != workspace_root cases live in PluginRootInfraScopeTest.) ---

    def test_infra_hooks_json_denied_for_every_agent(self):
        for at in ("bibliography_agent", "synthesis_agent", "formatter_agent", "broad_test_agent"):
            p = payload("Write",
                        {"file_path": os.path.join(self.ws, "hooks/hooks.json"), "content": "x"},
                        cwd=self.ws, agent_type=at)
            d = self.decide(p)
            self.assertEqual(d["decision"], "deny", f"{at} must not write hooks/hooks.json")
            self.assertIn("infrastructure", d["reason"].lower())

    def test_infra_manifest_denied_even_with_broad_glob(self):
        # broad_test_agent has glob ["**"] which would otherwise permit everything;
        # Step 2 self-protection overrides any later allow.
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "scripts/ars_phase_scope_manifest.json"), "content": "x"},
                    cwd=self.ws, agent_type="broad_test_agent")
        self.assertEqual(self.decide(p)["decision"], "deny")

    def test_infra_hook_script_denied(self):
        # The hook script itself (lives in scripts/) is part of the enforcement surface.
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "scripts/ars_write_scope_guard.py"), "content": "x"},
                    cwd=self.ws, agent_type="broad_test_agent")
        self.assertEqual(self.decide(p)["decision"], "deny")

    def test_infra_agent_frontmatter_denied(self):
        # Agent definition files carry the agent_type==name binding; writing them would
        # let an agent rename itself out of the manifest and fail the guard open.
        os.makedirs(os.path.join(self.ws, "deep-research/agents"), exist_ok=True)
        p = payload("Edit",
                    {"file_path": os.path.join(self.ws, "deep-research/agents/bibliography_agent.md"),
                     "old_string": "a", "new_string": "b"},
                    cwd=self.ws, agent_type="broad_test_agent")
        self.assertEqual(self.decide(p)["decision"], "deny")

    # --- Step 1 ordering: normalization precedes self-protection (traversal bypass) ---

    def test_traversal_bypass_to_infra_denied(self):
        # A Write whose raw file_path uses ../ to escape a phase dir back into hooks/.
        # Normalization (Step 1) must canonicalize it to hooks/hooks.json BEFORE Step 2,
        # so self-protection catches it. Proves normalize-first ordering.
        raw = os.path.join(self.ws, "phase2_investigation/../hooks/hooks.json")
        p = payload("Write", {"file_path": raw, "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        d = self.decide(p)
        self.assertEqual(d["decision"], "deny")
        self.assertIn("infrastructure", d["reason"].lower())

    def test_traversal_escaping_workspace_denied(self):
        # ../ escaping the workspace root entirely must be denied FOR A BUCKET A AGENT
        # (commonpath guard). Bucket A stays fenced to its workspace regardless of actor.
        raw = os.path.join(self.ws, "phase2_investigation/../../outside.md")
        p = payload("Write", {"file_path": raw, "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        self.assertEqual(self.decide(p)["decision"], "deny")

    def test_main_session_escape_allowed(self):
        # #302: a MAIN-SESSION write whose target resolves outside the workspace root
        # (e.g. a sibling git worktree) is ALLOWED — the main session is unconstrained by
        # Slice 1 (§3.3). The escape deny is a Bucket A fence, not a main-session fence.
        raw = os.path.join(self.ws, "../sibling-worktree/file.md")
        p = payload("Write", {"file_path": raw, "content": "x"}, cwd=self.ws)  # no agent_type
        d = self.decide(p)
        self.assertEqual(d["decision"], "allow")
        # Still fail-loud about the absent agent_type (not a silent no-op).
        self.assertTrue(d.get("absent_agent_type_advisory"),
                        "absent agent_type escape write must still surface the advisory")

    def test_non_bucket_a_agent_escape_allowed(self):
        # A Bucket B/C/D agent (agent_type present but not a manifest key) is also
        # unconstrained by Slice 1 — an escaping write is allowed, no advisory (it HAS a type).
        raw = os.path.join(self.ws, "../sibling-worktree/file.md")
        p = payload("Write", {"file_path": raw, "content": "x"},
                    cwd=self.ws, agent_type="report_compiler_agent")  # Bucket B, not in manifest
        d = self.decide(p)
        self.assertEqual(d["decision"], "allow")
        self.assertFalse(d.get("absent_agent_type_advisory"))

    # --- Step 3: agent gating edge cases ---

    def test_absent_agent_type_allowed(self):
        # Main session (no agent_type) is unconstrained by Slice 1.
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase7_format/anything.md"), "content": "x"},
                    cwd=self.ws)  # no agent_type
        d = self.decide(p)
        self.assertEqual(d["decision"], "allow")
        # but it must fail-loud-log the absent-agent_type write (not silent no-op)
        self.assertTrue(d.get("absent_agent_type_advisory"),
                        "absent agent_type write must surface a fail-loud advisory, not silently no-op")

    def test_absent_agent_type_still_denied_for_infra(self):
        # Even the main session may not clobber the PLUGIN's own infra. Here the 3-arg
        # fallback puts plugin_root == workspace_root, so hooks/hooks.json IS a plugin infra
        # file and is denied regardless of actor (the #448 carve-out only spares a SEPARATE
        # user project's same-named file — see PluginRootInfraScopeTest).
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "hooks/hooks.json"), "content": "x"},
                    cwd=self.ws)  # no agent_type
        self.assertEqual(self.decide(p)["decision"], "deny")

    def test_non_bucket_a_agent_type_allowed(self):
        # An agent_type not in the manifest (e.g. a Bucket B/C/D agent) is unconstrained.
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase7_format/report.md"), "content": "x"},
                    cwd=self.ws, agent_type="report_compiler_agent")  # Bucket B, not in manifest
        self.assertEqual(self.decide(p)["decision"], "allow")

    # --- Step 1: absolute vs relative normalization ---

    def test_absolute_path_under_workspace_matches_relative_glob(self):
        # A Write with an ABSOLUTE file_path under the workspace must resolve and match
        # its relative glob (glob is workspace-root-anchored, not absolute, not cwd-rel).
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase7_format/paper.md"), "content": "x"},
                    cwd=self.ws, agent_type="formatter_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")

    def test_relative_path_resolved_against_cwd(self):
        # A relative file_path resolves against cwd (= workspace here) then matches glob.
        p = payload("Write",
                    {"file_path": "phase7_format/paper.md", "content": "x"},
                    cwd=self.ws, agent_type="formatter_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")


class GlobMatchBoundaryTest(unittest.TestCase):
    """Negative + positive glob-match cases (feedback: widening a matcher needs
    explicit 'should-be-rejected' cases — unit pass at one layer can still mismatch)."""

    POSITIVE = [
        ("phase2_investigation/notes.txt", ["phase2_*/**"]),
        ("phase2_investigation/sub/deep.txt", ["phase2_*/**"]),   # deep descendant
        ("phase7_format/paper.md", ["phase7_*/**"]),
        ("scripts/ars_write_scope_guard.py", ["**/ars_write_scope_guard.py"]),  # subdir
        ("a/b/c/ars_write_scope_guard.py", ["**/ars_write_scope_guard.py"]),    # deep subdir
        ("ars_write_scope_guard.py", ["ars_write_scope_guard.py"]),             # root via bare
        ("deep-research/agents/bibliography_agent.md", ["deep-research/agents/*.md"]),
    ]
    NEGATIVE = [
        ("phase3_analysis/x.md", ["phase2_*/**"]),                # wrong phase number
        ("phase2x/notes.txt", ["phase2_*/**"]),                   # no underscore -> NOT phase2_
        ("other/phase2_investigation/x.md", ["phase2_*/**"]),     # nested, not workspace-root
        # FALSE-OPEN regression (caught in review): a ROOT-LEVEL file whose name fnmatches the
        # phase-dir glob must NOT match — `dir/**` covers descendants only, not a bare file.
        ("phase2_x.md", ["phase2_*/**"]),
        ("phase1_malicious.py", ["phase1_*/**"]),
        ("phase2_investigation", ["phase2_*/**"]),                # bare dir node: not a write target
        # `**/name` matches subdirs only, NOT root (root coverage is the bare entry).
        ("ars_write_scope_guard.py", ["**/ars_write_scope_guard.py"]),
    ]

    def test_positive_matches(self):
        for rel, globs in self.POSITIVE:
            self.assertTrue(guard._matches_any(rel, globs), f"{rel} should match {globs}")

    def test_negative_non_matches(self):
        for rel, globs in self.NEGATIVE:
            self.assertFalse(guard._matches_any(rel, globs), f"{rel} should NOT match {globs}")

    @unittest.skipIf(os.sep == "\\", "POSIX-only: `\\` is a path separator on Windows")
    def test_posix_literal_backslash_in_filename_not_split_into_segments(self):
        # On POSIX, `\` is a LEGAL filename character, NOT a separator. A root-level file
        # literally named `phase2_x\notes.md` is ONE segment and must NOT be rewritten into
        # two segments and matched against `phase2_*/**` — that would be a fence-escape
        # false-allow. (#330 PR #450's unconditional `replace("\\","/")` had this bug; the
        # rewrite is now gated on os.sep == "\\". This test pins the POSIX no-op.)
        self.assertFalse(
            guard._matches_any("phase2_x\\notes.md", ["phase2_*/**"]),
            "a literal backslash in a POSIX filename must not be treated as a path separator")


class DenyJSONShapeTest(unittest.TestCase):
    """The deny output JSON shape (spec §3.2 first-party-verified)."""

    def test_render_deny_decision_json(self):
        out = guard.render_hook_output({"decision": "deny", "reason": "ARS scope guard: nope"})
        obj = json.loads(out)
        hso = obj["hookSpecificOutput"]
        self.assertEqual(hso["hookEventName"], "PreToolUse")
        self.assertEqual(hso["permissionDecision"], "deny")
        self.assertEqual(hso["permissionDecisionReason"], "ARS scope guard: nope")

    def test_render_allow_is_passthrough_not_grant(self):
        # Non-deny must be PASS-THROUGH (no permissionDecision key), NOT an explicit
        # "allow" grant — an "allow" would skip every other permission rule (review
        # finding). Assert the key is absent entirely.
        out = guard.render_hook_output({"decision": "allow", "reason": ""})
        hso = json.loads(out)["hookSpecificOutput"]
        self.assertEqual(hso["hookEventName"], "PreToolUse")
        self.assertNotIn("permissionDecision", hso)


class NormalizationRegressionTest(unittest.TestCase):
    """Regression tests for normalization / glob-boundary findings — each must stay fixed."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.ws = os.path.realpath(self._tmp.name)
        for d in ("phase2_investigation", "phase3_analysis", "hooks", "scripts", ".claude-plugin"):
            os.makedirs(os.path.join(self.ws, d), exist_ok=True)

    def tearDown(self):
        self._tmp.cleanup()

    def decide(self, p):
        return guard.evaluate_decision(p, TEST_MANIFEST, self.ws)

    def test_bash_bypass_shapes_that_broke_the_old_parser_still_deny(self):
        # The shapes that defeated the old literal-target parser (quote-blind redirection,
        # quoted `;` in cp, no-whitespace redirection, `cp -t DEST` flag order) are now ALL
        # denied trivially by the all-Bash-deny policy — no parsing required. These stay as
        # regression cases so a future re-introduction of literal parsing can't reopen them.
        shapes = [
            'echo x > "' + os.path.join(self.ws, "hooks/hooks.json") + '"',  # quoted target
            "echo x>" + os.path.join(self.ws, "phase3_analysis/leak.md"),    # no whitespace
            'cp "a;b" ' + os.path.join(self.ws, "phase3_analysis/leak.md"),  # quoted ; in cp
            "cp -t " + os.path.join(self.ws, "phase3_analysis") + " src.md",  # -t flag order
        ]
        for cmd in shapes:
            p = payload("Bash", {"command": cmd}, cwd=self.ws, agent_type="bibliography_agent")
            self.assertEqual(self.decide(p)["decision"], "deny", f"{cmd!r} should deny")

    def test_root_level_phase_named_file_denied(self):
        # FALSE-OPEN P0: a phase2 agent writing a ROOT file named `phase2_x.md` must be
        # denied — it is not inside the phase dir (dir/** = descendants only).
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase2_x.md"), "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        self.assertEqual(self.decide(p)["decision"], "deny")

    def test_plugin_json_infra_protected(self):
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, ".claude-plugin/plugin.json"), "content": "x"},
                    cwd=self.ws, agent_type="broad_test_agent")
        d = self.decide(p)
        self.assertEqual(d["decision"], "deny")
        self.assertIn("infrastructure", d["reason"].lower())

    def test_symlink_traversal_to_infra_denied(self):
        # A symlinked dir + `../` must resolve through the symlink (realpath), not be
        # lexically collapsed by abspath. Build: ws/link -> ws/phase2_investigation, then
        # write link/../hooks/hooks.json. realpath resolves link first => ws/hooks/hooks.json.
        symlink_or_skip(self, os.path.join(self.ws, "phase2_investigation"),
                        os.path.join(self.ws, "link"))
        raw = os.path.join(self.ws, "link/../hooks/hooks.json")
        p = payload("Write", {"file_path": raw, "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        d = self.decide(p)
        self.assertEqual(d["decision"], "deny")
        self.assertIn("infrastructure", d["reason"].lower())

    def test_symlink_escaping_workspace_denied(self):
        # A symlink pointing OUTSIDE the workspace must be detected as an escape, not
        # approved on its lexical in-workspace name.
        outside = tempfile.mkdtemp()
        try:
            symlink_or_skip(self, outside, os.path.join(self.ws, "exit"))
            raw = os.path.join(self.ws, "exit/leak.md")
            p = payload("Write", {"file_path": raw, "content": "x"},
                        cwd=self.ws, agent_type="bibliography_agent")
            self.assertEqual(self.decide(p)["decision"], "deny")
        finally:
            import shutil
            shutil.rmtree(outside, ignore_errors=True)


class BashBypassRegressionTest(unittest.TestCase):
    """Regression pins for the historical Bash fail-open shapes + the deep-path crash.

    Review surfaced a long list of Bash bypasses (quoted redirection, statement split,
    `&>`/`<>`, transparent wrappers `command rm`, shell structure `(rm x)`/`$(rm x)`,
    `sudo -u bob rm`, `>(rm)`, backtick `` `rm` ``, and "read-only" tools that execute
    subprocesses like `rg --pre`). The final policy denies ALL Bash for a Bucket A agent, so
    every one of these denies trivially. These cases stay pinned: if anyone ever re-introduces
    a denylist/allowlist/parse approach, they must still deny. (The recursive-matcher crash is
    a separate fix pinned at the end.)
    """

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.ws = os.path.realpath(self._tmp.name)
        for d in ("phase2_investigation", "phase3_analysis", "phase7_format", "hooks", "scripts"):
            os.makedirs(os.path.join(self.ws, d), exist_ok=True)

    def tearDown(self):
        self._tmp.cleanup()

    def decide(self, p):
        return guard.evaluate_decision(p, TEST_MANIFEST, self.ws)

    def _bash(self, cmd):
        return self.decide(payload("Bash", {"command": cmd}, cwd=self.ws,
                                   agent_type="bibliography_agent"))

    def test_all_historical_bash_bypasses_denied(self):
        # Every shape that defeated an earlier denylist OR allowlist attempt. Under the final
        # all-Bash-deny policy they all deny trivially — no parsing, no allowlist membership,
        # no flag guard. (Labels name the bypass class so the coverage intent survives.)
        shapes = [
            "echo hi &> phase3_analysis/leak.md",      # combined redirect
            "cat <> phase3_analysis/leak.md",          # read-write open
            "command rm hooks/hooks.json",             # transparent wrapper
            "sudo -u bob rm x",                        # wrapper + flag
            "(rm x)", "{ rm x; }",                     # grouping
            "if true; then rm x; fi",                  # conditional
            "echo $(rm hooks/hooks.json)",             # command substitution
            "echo >(rm hooks/hooks.json)",             # process substitution
            "echo `rm x`",                             # backtick substitution
            "echo x>f", 'cp "a;b" /elsewhere',         # quote/no-whitespace parser bypasses
            # commands that LOOK read-only but execute a subprocess / write state:
            "rg --pre 'sh -c touch' x f", "git grep --open-files-in-pager=touch x",
            "sort --compress-program=touch big.txt", "GIT_EXTERNAL_DIFF=touch git diff",
            "uniq in.txt out.txt", "git status",
            # inputs once worried about as FALSE-DENY — moot now, all Bash denies:
            "grep in rm file", "grep foo 2>&1",
        ]
        for cmd in shapes:
            self.assertEqual(self._bash(cmd)["decision"], "deny", f"{cmd!r} must deny (all-Bash-deny)")

    # --- P1-c: recursive `_match_segments` blew the Python recursion limit on deep paths. ---

    def test_deep_path_glob_match_does_not_crash(self):
        # ~1100 path segments raised RecursionError (limit 1000) in the recursive matcher,
        # crashing the hook (uncaught in main()) — fail-open or wedge depending on the CC
        # contract; either way unacceptable. The matcher must handle arbitrary depth without
        # blowing the stack (caught in review).
        deep_under = "phase2_investigation/" + "/".join(["a"] * 2000) + "/leak.md"
        # Must still produce a correct decision (it IS under phase2_*, so a structured-tool
        # write is allowed; the point is: no crash).
        self.assertTrue(guard._matches_any(deep_under, ["phase2_*/**"]))
        deep_other = "phase3_analysis/" + "/".join(["a"] * 2000) + "/leak.md"
        self.assertFalse(guard._matches_any(deep_other, ["phase2_*/**"]))
        # And end-to-end through evaluate_decision (the path that actually crashed).
        p = payload("Write", {"file_path": os.path.join(self.ws, deep_under), "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        self.assertEqual(self.decide(p)["decision"], "allow")


class MalformedPayloadTest(unittest.TestCase):
    """Valid-JSON-wrong-shape and odd tool_input must not crash (must pass through)."""

    def decide(self, p):
        return guard.evaluate_decision(p, TEST_MANIFEST, "/tmp")

    def test_list_payload_does_not_crash(self):
        # evaluate_decision is the pure core; main() guards non-dict payloads. Here we
        # assert tool_input of the wrong type does not crash the core.
        p = {"tool_name": "Bash", "tool_input": [], "cwd": "/tmp"}
        d = self.decide(p)
        self.assertEqual(d["decision"], "allow")  # no catchable target, no agent -> allow

    def test_null_tool_input_does_not_crash(self):
        p = {"tool_name": "Write", "tool_input": None, "cwd": "/tmp", "agent_type": "bibliography_agent"}
        # Write with no usable file_path -> schema-drift deny (fail closed), not a crash.
        d = self.decide(p)
        self.assertEqual(d["decision"], "deny")
        self.assertTrue(d.get("schema_drift_advisory"))


class PluginRootInfraScopeTest(unittest.TestCase):
    """#448 — infra self-protection is anchored on the PLUGIN root, not the user's PROJECT
    root. Under a plugin install the two differ; the user's own project files that happen to
    share a filename with an ARS infra file (CLAUDE.md, hooks/*.sh, shared/agents/*.md, ...)
    must NOT be denied. The ARS plugin's OWN files stay protected.
    """

    def setUp(self):
        # Two DISTINCT roots: a user project and a separate plugin install dir.
        self._proj = tempfile.TemporaryDirectory()
        self._plugin = tempfile.TemporaryDirectory()
        self.ws = os.path.realpath(self._proj.name)        # user project (workspace_root)
        self.plugin = os.path.realpath(self._plugin.name)  # ARS plugin install (plugin_root)
        for d in ("phase2_investigation", ".claude", "hooks", "shared/agents"):
            os.makedirs(os.path.join(self.ws, d), exist_ok=True)
        for d in ("scripts", "hooks", ".claude", "shared/agents", "agents"):
            os.makedirs(os.path.join(self.plugin, d), exist_ok=True)

    def tearDown(self):
        self._proj.cleanup()
        self._plugin.cleanup()

    def decide_in_project(self, p):
        # workspace = user project; plugin_root = the separate ARS install.
        return guard.evaluate_decision(p, TEST_MANIFEST, self.ws, self.plugin)

    # --- the reported bug: user's own CLAUDE.md must be writable by the main session ---

    def test_user_project_root_claude_md_allowed_main_session(self):
        # This is exactly #448. Pre-fix this was DENY; post-fix it must be ALLOW.
        p = payload("Write", {"file_path": os.path.join(self.ws, "CLAUDE.md"), "content": "x"},
                    cwd=self.ws)  # no agent_type = main session
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_user_project_dotclaude_claude_md_allowed_main_session(self):
        p = payload("Write", {"file_path": os.path.join(self.ws, ".claude/CLAUDE.md"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_user_project_shared_agents_md_allowed(self):
        # `shared/agents/*.md` is an ARS infra glob but ALSO a plausible user-project path.
        p = payload("Write", {"file_path": os.path.join(self.ws, "shared/agents/foo.md"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_user_project_hooks_json_allowed(self):
        p = payload("Write", {"file_path": os.path.join(self.ws, "hooks/hooks.json"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_user_project_hooks_sh_allowed(self):
        p = payload("Write", {"file_path": os.path.join(self.ws, "hooks/install.sh"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    # --- self-protection PRESERVED: the plugin's OWN files stay denied ---

    def test_plugin_own_claude_md_allowed(self):
        # #459: CLAUDE.md is no longer infra-protected, even the plugin's OWN copy. It is a
        # doc, not a load-bearing enforcement file — editing it cannot fail the guard open,
        # so it must NOT be denied. (The load-bearing files below stay protected; see
        # test_plugin_own_guard_script_denied / _hooks_json_denied / _shared_agents_md_denied.)
        p = payload("Write", {"file_path": os.path.join(self.plugin, "CLAUDE.md"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_plugin_own_dotclaude_claude_md_allowed(self):
        # Same for .claude/CLAUDE.md inside the plugin root (#459).
        os.makedirs(os.path.join(self.plugin, ".claude"), exist_ok=True)
        p = payload("Write", {"file_path": os.path.join(self.plugin, ".claude/CLAUDE.md"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_plugin_own_guard_script_denied(self):
        p = payload("Write",
                    {"file_path": os.path.join(self.plugin, "scripts/ars_write_scope_guard.py"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_plugin_own_hooks_json_denied(self):
        p = payload("Write", {"file_path": os.path.join(self.plugin, "hooks/hooks.json"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_plugin_own_shared_agents_md_denied(self):
        p = payload("Write", {"file_path": os.path.join(self.plugin, "shared/agents/bar.md"), "content": "x"},
                    cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_plugin_own_toplevel_agents_md_denied(self):
        # The #413-materialized top-level agents/*.md carry the agent_type==name binding too;
        # #448 added `agents/*.md` to the infra globs. A user-project agents/foo.md is still
        # allowed (covered by no deny test -> it falls through to Step 3 allow); only the
        # PLUGIN's own copy is protected.
        p = payload("Write", {"file_path": os.path.join(self.plugin, "agents/synthesis_agent.md"),
                              "content": "x"}, cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_user_project_toplevel_agents_md_allowed(self):
        # The mirror: a user's OWN agents/foo.md (inside their project, outside plugin_root)
        # must remain writable — the #448 carve-out applies to agents/*.md too.
        os.makedirs(os.path.join(self.ws, "agents"), exist_ok=True)
        p = payload("Write", {"file_path": os.path.join(self.ws, "agents/my_agent.md"),
                              "content": "x"}, cwd=self.ws)
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    # --- fallback: plugin_root=None -> conservative pre-fix behavior (workspace-anchored).
    #     This is the clone+symlink layout / ARS-on-ARS home turf, where plugin_root
    #     collapses onto workspace_root — the #459 crux: the SAME runtime condition is both
    #     "protect ARS infra" and "don't false-deny the user's CLAUDE.md". The #459 fix makes
    #     that condition decidable WITHOUT distinguishing the layouts: CLAUDE.md left the infra
    #     list (so it's allowed everywhere), while the load-bearing files stay protected. ---

    def test_fallback_none_plugin_root_claude_md_allowed(self):
        # #459: even under the collapsed fallback, the user's own CLAUDE.md is writable —
        # because CLAUDE.md is no longer infra, not because we detected the layout.
        p = payload("Write", {"file_path": os.path.join(self.ws, "CLAUDE.md"), "content": "x"},
                    cwd=self.ws)
        d = guard.evaluate_decision(p, TEST_MANIFEST, self.ws)  # 3-arg: plugin_root defaults None
        self.assertEqual(d["decision"], "allow")

    def test_fallback_none_plugin_root_still_protects_load_bearing_infra(self):
        # The protection that MUST survive #459: under the collapsed fallback, the load-bearing
        # enforcement files (here the guard script) are still denied. Dropping CLAUDE.md did not
        # weaken self-protection of the files that can actually fail the guard open.
        os.makedirs(os.path.join(self.ws, "scripts"), exist_ok=True)
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "scripts/ars_write_scope_guard.py"), "content": "x"},
                    cwd=self.ws)
        d = guard.evaluate_decision(p, TEST_MANIFEST, self.ws)  # 3-arg: plugin_root defaults None
        self.assertEqual(d["decision"], "deny")
        self.assertIn("infrastructure", d["reason"])

    # --- Bucket A phase-scope is UNCHANGED by the dual-root split ---

    def test_bucket_a_phase_scope_unaffected_allow(self):
        p = payload("Write",
                    {"file_path": os.path.join(self.ws, "phase2_investigation/bib.md"), "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        self.assertEqual(self.decide_in_project(p)["decision"], "allow")

    def test_bucket_a_cannot_reach_user_claude_md(self):
        # A Bucket A agent still can't write the user's root CLAUDE.md — not because of infra
        # protection now, but because it's outside the agent's phase glob (Step 4). The guard
        # is unchanged for agents; only the main session gained access.
        p = payload("Write", {"file_path": os.path.join(self.ws, "CLAUDE.md"), "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        d = self.decide_in_project(p)
        self.assertEqual(d["decision"], "deny")
        self.assertIn("bibliography_agent", d["reason"])  # phase-scope deny, not infra deny

    # --- dual-root regression variants (codex P2-b): traversal / symlink / Bucket A escape
    #     toward the plugin's OWN infra, under a real plugin_root != workspace_root install ---

    def test_dual_root_traversal_from_phase_into_plugin_infra_denied(self):
        # A relative target that escapes the phase dir and `..`-walks all the way into the
        # plugin tree's hooks/hooks.json. realpath in _infra_protected_target must resolve it
        # and deny — the infra check runs BEFORE the workspace-escape branch.
        rel_into_plugin = os.path.relpath(
            os.path.join(self.plugin, "hooks/hooks.json"),
            os.path.join(self.ws, "phase2_investigation"))
        raw = "phase2_investigation/" + rel_into_plugin
        p = payload("Write", {"file_path": raw, "content": "x"}, cwd=self.ws)  # main session
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_dual_root_symlink_into_plugin_infra_denied(self):
        # A symlink inside the user workspace pointing at a plugin infra file. realpath
        # resolves the link to the plugin tree -> infra-protected -> deny.
        link = os.path.join(self.ws, "sneaky_link.py")
        target = os.path.join(self.plugin, "scripts/ars_write_scope_guard.py")
        os.makedirs(os.path.dirname(target), exist_ok=True)
        with open(target, "w") as fh:
            fh.write("# real guard\n")
        symlink_or_skip(self, target, link)
        p = payload("Write", {"file_path": link, "content": "x"}, cwd=self.ws)  # main session
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_dual_root_bucket_a_escape_toward_plugin_infra_denied(self):
        # Bucket A agent trying to reach the plugin's own guard script. It is denied — the
        # infra check fires first; even if it didn't, the escape fence (#302) would catch it.
        p = payload("Write",
                    {"file_path": os.path.join(self.plugin, "scripts/ars_write_scope_guard.py"),
                     "content": "x"},
                    cwd=self.ws, agent_type="bibliography_agent")
        self.assertEqual(self.decide_in_project(p)["decision"], "deny")

    def test_dual_root_bucket_a_sibling_worktree_escape_still_allowed_for_main(self):
        # Sanity: a NON-infra escape (a sibling worktree outside both roots) is still allowed
        # for the main session — the infra reorder didn't over-deny genuine escapes.
        sibling = os.path.realpath(os.path.join(self.ws, "..", "sibling_worktree"))
        os.makedirs(sibling, exist_ok=True)
        try:
            p = payload("Write", {"file_path": os.path.join(sibling, "notes.md"), "content": "x"},
                        cwd=self.ws)  # main session
            self.assertEqual(self.decide_in_project(p)["decision"], "allow")
        finally:
            import shutil
            shutil.rmtree(sibling, ignore_errors=True)


class MainPluginRootComputationTest(unittest.TestCase):
    """main() must compute plugin_root from CLAUDE_PLUGIN_ROOT, else the resolved repo root
    (resolve() to follow the ~/.claude/skills symlink install). codex P2-b."""

    def test_plugin_root_from_env(self):
        import subprocess
        guard_path = os.path.join(REPO_ROOT, "scripts", "ars_write_scope_guard.py")
        with tempfile.TemporaryDirectory() as proj, tempfile.TemporaryDirectory() as plug:
            # Writing the user project's own CLAUDE.md must pass through (no permissionDecision)
            # when CLAUDE_PLUGIN_ROOT points elsewhere.
            env = dict(os.environ, CLAUDE_PROJECT_DIR=proj, CLAUDE_PLUGIN_ROOT=plug)
            inp = json.dumps({"tool_name": "Write", "cwd": proj,
                              "tool_input": {"file_path": os.path.join(proj, "CLAUDE.md"),
                                             "content": "x"}})
            out = subprocess.run([sys.executable, guard_path], input=inp, env=env,
                                 capture_output=True, text=True)
            decision = json.loads(out.stdout)
            self.assertNotIn("permissionDecision", decision["hookSpecificOutput"])

    def test_plugin_own_file_denied_via_env(self):
        import subprocess
        guard_path = os.path.join(REPO_ROOT, "scripts", "ars_write_scope_guard.py")
        with tempfile.TemporaryDirectory() as proj, tempfile.TemporaryDirectory() as plug:
            os.makedirs(os.path.join(plug, "scripts"))
            env = dict(os.environ, CLAUDE_PROJECT_DIR=proj, CLAUDE_PLUGIN_ROOT=plug)
            inp = json.dumps({"tool_name": "Write", "cwd": proj,
                              "tool_input": {"file_path": os.path.join(plug, "scripts/ars_write_scope_guard.py"),
                                             "content": "x"}})
            out = subprocess.run([sys.executable, guard_path], input=inp, env=env,
                                 capture_output=True, text=True)
            decision = json.loads(out.stdout)
            self.assertEqual(decision["hookSpecificOutput"].get("permissionDecision"), "deny")


if __name__ == "__main__":
    unittest.main()
