"""Mutation tests for check_model_tiering.py (#517 classification drift guard)."""
import json
import tempfile
import unittest
from pathlib import Path

from tests.test_helpers import load_module_from_path, run_script

SCRIPT = Path(__file__).resolve().parent / "check_model_tiering.py"


def _fixture_repo(tmp: Path, *, manifest_agents=None, doc_text=None, disk_paths=None):
    """Build a minimal repo tree: two agent files, matching manifest + doc by default."""
    default_paths = [
        "deep-research/agents/synthesis_agent.md",
        "academic-paper/agents/formatter_agent.md",
    ]
    disk_paths = default_paths if disk_paths is None else disk_paths
    for rel in disk_paths:
        p = tmp / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("# agent\n", encoding="utf-8")
    if manifest_agents is None:
        manifest_agents = [
            {"path": "deep-research/agents/synthesis_agent.md", "tier": "judgment"},
            {"path": "academic-paper/agents/formatter_agent.md", "tier": "execution"},
        ]
    (tmp / "scripts").mkdir(exist_ok=True)
    (tmp / "scripts" / "model_tiering_manifest.json").write_text(
        json.dumps({"version": 1, "agents": manifest_agents}), encoding="utf-8"
    )
    if doc_text is None:
        doc_text = (
            "# Model Tiering\n\n"
            "### Judgment-type (1)\n\n"
            "| Skill | Agents |\n|---|---|\n"
            "| deep-research (1) | `synthesis` |\n\n"
            "### Execution-type (1)\n\n"
            "| Skill | Agents |\n|---|---|\n"
            "| academic-paper (1) | `formatter` |\n"
        )
    (tmp / "shared").mkdir(exist_ok=True)
    (tmp / "shared" / "model_tiering.md").write_text(doc_text, encoding="utf-8")


def _run_on(tmp: Path) -> int:
    module = load_module_from_path("check_model_tiering", SCRIPT)
    module.REPO = tmp
    module.MANIFEST = tmp / "scripts" / "model_tiering_manifest.json"
    module.DOC = tmp / "shared" / "model_tiering.md"
    return module.main()


class ModelTieringLintTests(unittest.TestCase):

    def test_repo_baseline_passes(self) -> None:
        """The committed manifest + canonical doc + agent files must pass."""
        result = run_script(SCRIPT)
        self.assertEqual(result.returncode, 0, msg=f"stdout: {result.stdout}\nstderr: {result.stderr}")
        self.assertIn("PASS", result.stdout)
        self.assertIn("39 agents", result.stdout)

    def test_clean_fixture_passes(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(tmp)
            self.assertEqual(_run_on(tmp), 0)

    def test_new_agent_without_classification_fails(self) -> None:
        """The load-bearing drift case: an agent file lands with no tier."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(
                tmp,
                disk_paths=[
                    "deep-research/agents/synthesis_agent.md",
                    "academic-paper/agents/formatter_agent.md",
                    "deep-research/agents/brand_new_agent.md",
                ],
            )
            self.assertEqual(_run_on(tmp), 1)

    def test_manifest_orphan_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(
                tmp,
                manifest_agents=[
                    {"path": "deep-research/agents/synthesis_agent.md", "tier": "judgment"},
                    {"path": "academic-paper/agents/formatter_agent.md", "tier": "execution"},
                    {"path": "deep-research/agents/deleted_agent.md", "tier": "execution"},
                ],
            )
            self.assertEqual(_run_on(tmp), 1)

    def test_invalid_tier_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(
                tmp,
                manifest_agents=[
                    {"path": "deep-research/agents/synthesis_agent.md", "tier": "frontier"},
                    {"path": "academic-paper/agents/formatter_agent.md", "tier": "execution"},
                ],
            )
            self.assertEqual(_run_on(tmp), 1)

    def test_doc_count_mismatch_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (2)\n\n"
                "| deep-research (1) | `synthesis` |\n\n"
                "### Execution-type (1)\n\n"
                "| academic-paper (1) | `formatter` |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)

    def test_agent_listed_in_wrong_section_fails(self) -> None:
        """Manifest says execution, doc table lists it under judgment."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (1)\n\n"
                "| deep-research (1) | `synthesis` |\n"
                "| academic-paper (1) | `formatter` |\n\n"
                "### Execution-type (1)\n\n"
                "| some-other (0) | |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)

    def test_agent_in_both_sections_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (1)\n\n"
                "| deep-research (1) | `synthesis` |\n\n"
                "### Execution-type (1)\n\n"
                "| academic-paper (1) | `formatter` |\n"
                "| deep-research (1) | `synthesis` |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)

    def test_duplicate_manifest_path_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(
                tmp,
                manifest_agents=[
                    {"path": "deep-research/agents/synthesis_agent.md", "tier": "judgment"},
                    {"path": "deep-research/agents/synthesis_agent.md", "tier": "judgment"},
                    {"path": "academic-paper/agents/formatter_agent.md", "tier": "execution"},
                ],
            )
            self.assertEqual(_run_on(tmp), 1)

    def test_missing_doc_heading_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(tmp, doc_text="# Model Tiering\n\nno tier sections here\n")
            self.assertEqual(_run_on(tmp), 1)

    def test_extra_doc_token_fails(self) -> None:
        """A token in the doc table with no manifest backing must fail (subset-only trap)."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (1)\n\n"
                "| Skill | Agents |\n|---|---|\n"
                "| deep-research (2) | `synthesis`, `phantom` |\n\n"
                "### Execution-type (1)\n\n"
                "| Skill | Agents |\n|---|---|\n"
                "| academic-paper (1) | `formatter` |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)

    def test_wrong_per_row_count_fails(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (1)\n\n"
                "| Skill | Agents |\n|---|---|\n"
                "| deep-research (3) | `synthesis` |\n\n"
                "### Execution-type (1)\n\n"
                "| Skill | Agents |\n|---|---|\n"
                "| academic-paper (1) | `formatter` |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)

    def test_duplicate_skill_row_fails(self) -> None:
        """A contradictory second row for the same skill must not be shadowed."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (1)\n\n"
                "| Skill | Agents |\n|---|---|\n"
                "| deep-research (1) | `synthesis` |\n"
                "| deep-research (1) | `something_else` |\n\n"
                "### Execution-type (1)\n\n"
                "| Skill | Agents |\n|---|---|\n"
                "| academic-paper (1) | `formatter` |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)

    def test_agent_in_unknown_skill_dir_fails(self) -> None:
        """Repo-wide sweep: a *_agent.md under a NEW skill dir (not in AGENT_DIRS) fails."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            _fixture_repo(tmp)
            stray = tmp / "brand-new-skill" / "agents" / "novel_agent.md"
            stray.parent.mkdir(parents=True)
            stray.write_text("# agent\n", encoding="utf-8")
            self.assertEqual(_run_on(tmp), 1)

    def test_skill_label_prefix_collision_is_not_a_false_pass(self) -> None:
        """`academic-paper-reviewer` row must not satisfy an `academic-paper` agent."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            doc = (
                "### Judgment-type (1)\n\n"
                "| deep-research (1) | `synthesis` |\n\n"
                "### Execution-type (1)\n\n"
                "| academic-paper-reviewer (1) | `formatter` |\n"
            )
            _fixture_repo(tmp, doc_text=doc)
            self.assertEqual(_run_on(tmp), 1)


if __name__ == "__main__":
    unittest.main()
