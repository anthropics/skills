"""Unit tests for check_collaboration_depth_rubric.py (ARS v3.5)."""
from __future__ import annotations

import textwrap
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_collaboration_depth_rubric.py"


def _run(root: Path):
    return run_script(SCRIPT, "--path", str(root))


def _valid_rubric_text() -> str:
    return textwrap.dedent("""\
        ---
        rubric_version: "1.0"
        paper_citation: "Wang, S., & Zhang, H. (2026). IJETHE 23:11. DOI 10.1186/s41239-026-00585-x"
        ---

        # Collaboration Depth Rubric

        Based on Wang & Zhang (2026).

        ## Delegation Intensity
        Whole-category handoffs vs scattered micro-asks.

        ## Cognitive Vigilance
        User challenges AI claims; requests source verification.

        ## Cognitive Reallocation
        Freed capacity invested in higher-order work.

        ## Zone Classification
        Zone 1 / Zone 2 / Zone 3 synthesis.
        """)


def _valid_agent_text() -> str:
    return textwrap.dedent("""\
        ---
        name: collaboration_depth_agent
        measures: collaboration_depth
        blocking: false
        rubric_ref: shared/collaboration_depth_rubric.md
        ---

        # collaboration_depth_agent

        Observer. Reads dialogue log; scores per rubric at shared/collaboration_depth_rubric.md.
        """)


def _valid_orchestrator_text() -> str:
    return textwrap.dedent("""\
        # pipeline_orchestrator_agent

        At every FULL checkpoint and at pipeline completion, dispatch
        collaboration_depth_agent (advisory only; never blocks).
        """)


def _valid_skill_md_text() -> str:
    return textwrap.dedent("""\
        ---
        metadata:
          data_access_level: verified_only
          task_type: orchestration
        ---

        # academic-pipeline

        The collaboration_depth_agent runs at checkpoints as advisory only and
        never blocks progression.
        """)


def _make_repo(root: Path) -> None:
    (root / "shared").mkdir(parents=True)
    (root / "shared" / "collaboration_depth_rubric.md").write_text(_valid_rubric_text())
    agents = root / "academic-pipeline" / "agents"
    agents.mkdir(parents=True)
    (agents / "collaboration_depth_agent.md").write_text(_valid_agent_text())
    (agents / "pipeline_orchestrator_agent.md").write_text(_valid_orchestrator_text())
    (root / "academic-pipeline" / "SKILL.md").write_text(_valid_skill_md_text())


class TestCollaborationDepthRubric(unittest.TestCase):
    def test_valid_layout_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            r = _run(root)
            self.assertEqual(r.returncode, 0, msg=r.stdout + r.stderr)

    def test_missing_rubric_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            (root / "shared" / "collaboration_depth_rubric.md").unlink()
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("collaboration_depth_rubric.md does not exist", r.stdout)

    def test_rubric_without_doi_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            path = root / "shared" / "collaboration_depth_rubric.md"
            path.write_text(_valid_rubric_text().replace("10.1186/s41239-026-00585-x", ""))
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("Wang & Zhang", r.stdout)

    def test_rubric_without_version_field_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            path = root / "shared" / "collaboration_depth_rubric.md"
            path.write_text(_valid_rubric_text().replace('rubric_version: "1.0"', "unused: true"))
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("rubric_version", r.stdout)

    def test_rubric_missing_dimension_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            path = root / "shared" / "collaboration_depth_rubric.md"
            path.write_text(_valid_rubric_text().replace("## Cognitive Vigilance", "## Something Else"))
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("Cognitive Vigilance", r.stdout)

    def test_agent_without_rubric_ref_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            agent = root / "academic-pipeline" / "agents" / "collaboration_depth_agent.md"
            agent.write_text(_valid_agent_text().replace("shared/collaboration_depth_rubric.md", "nope.md"))
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("rubric_ref", r.stdout)

    def test_agent_with_drifted_frontmatter_but_correct_body_fails(self) -> None:
        """Frontmatter is the machine-readable contract; body text is not.

        Regression for codex-review P2 (rubric_ref drift): if `rubric_ref:`
        points to the wrong path but the body still mentions the real path
        (copy-paste artefact), the lint must still fail.
        """
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            agent = root / "academic-pipeline" / "agents" / "collaboration_depth_agent.md"
            drifted = _valid_agent_text().replace(
                "rubric_ref: shared/collaboration_depth_rubric.md",
                "rubric_ref: nope.md",
            )
            # Sanity: the drifted text still has the right path in the body.
            assert "shared/collaboration_depth_rubric.md" in drifted
            agent.write_text(drifted)
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("rubric_ref", r.stdout)

    def test_agent_blocking_true_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            agent = root / "academic-pipeline" / "agents" / "collaboration_depth_agent.md"
            agent.write_text(_valid_agent_text().replace("blocking: false", "blocking: true"))
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("blocking", r.stdout)

    def test_orchestrator_missing_invocation_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            orch = root / "academic-pipeline" / "agents" / "pipeline_orchestrator_agent.md"
            orch.write_text("# pipeline_orchestrator_agent\n\nNo observer mentioned.\n")
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("collaboration_depth_agent", r.stdout)

    def test_orchestrator_without_completion_context_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            orch = root / "academic-pipeline" / "agents" / "pipeline_orchestrator_agent.md"
            orch.write_text(
                "At FULL checkpoint, dispatch collaboration_depth_agent.\n"
            )
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("pipeline-completion", r.stdout)

    def test_orchestrator_keyword_only_without_dispatch_fails(self) -> None:
        """Keyword presence without dispatch semantics must not pass.

        Regression for codex-review P2 (keyword-only lint): a real orchestrator
        file contains the substrings 'checkpoint' and 'stage 6' in many
        unrelated sections. If the actual dispatch anchor were removed, the
        lint must still fail.
        """
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            orch = root / "academic-pipeline" / "agents" / "pipeline_orchestrator_agent.md"
            # Mentions the agent, checkpoints, and stage 6 — but no dispatch
            # verb anywhere near the agent name. Must fail.
            orch.write_text(
                "# pipeline_orchestrator_agent\n\n"
                "Checkpoints exist. Stage 6 is the last stage.\n\n"
                "The Agent Team includes collaboration_depth_agent as the "
                "fourth member; see the Agent Team table.\n"
            )
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("dispatch anchor", r.stdout.lower())

    def test_skill_md_without_nonblocking_phrase_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _make_repo(root)
            skill = root / "academic-pipeline" / "SKILL.md"
            skill.write_text("# academic-pipeline\n\nWe use collaboration_depth_agent.\n")
            r = _run(root)
            self.assertEqual(r.returncode, 1)
            self.assertIn("non-blocking", r.stdout)


if __name__ == "__main__":
    unittest.main()
