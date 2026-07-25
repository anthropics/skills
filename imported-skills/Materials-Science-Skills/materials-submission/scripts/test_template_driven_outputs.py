"""Regression tests for template-driven submission package outputs."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path

import yaml

SKILL_DIR = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = SKILL_DIR / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

import build_submission_package
import generate_checklist
import generate_cover_letter
import generate_highlights
import validate_journal_templates
from template_support import load_template

DATA_SCRIPTS_DIR = SKILL_DIR.parent / "materials-data" / "scripts"
sys.path.insert(0, str(DATA_SCRIPTS_DIR))

import build_fair_package


def manifest_for(journal: str, article_type: str = "research-article") -> dict:
    return {
        "target_journal": journal,
        "article_type": article_type,
        "title": "Template-driven submission test",
        "corresponding_author": "Test Author",
        "funding": "Test Grant",
        "conflicts": "No competing interests.",
        "data_availability_status": "ready",
        "code_availability_status": "ready",
        "live_verification_acknowledged": True,
    }


def data_package_manifest() -> str:
    return yaml.safe_dump(
        {
            "contract": "data-package",
            "contract_version": "1.0",
            "status": "ready",
            "producer": "materials-data",
            "package_dir": ".",
            "artifacts": {
                "metadata": {"status": "ready", "path": "metadata.md"},
                "readme": {"status": "ready", "path": "README.md"},
                "data_availability_statement": {
                    "status": "ready",
                    "path": "data_availability_statement.md",
                },
                "fair_audit": {"status": "ready", "path": "fair_audit.md"},
                "raw_data": {"status": "ready", "path": "raw_data"},
                "processed_data": {"status": "ready", "path": "processed_data"},
                "figures": {"status": "ready", "path": "figures"},
            },
        },
        sort_keys=False,
    )


def write_ready_data_package(directory: Path, *, mutate: object | None = None) -> Path:
    for relative_path in (
        "metadata.md",
        "README.md",
        "data_availability_statement.md",
        "fair_audit.md",
        "raw_data",
        "processed_data",
        "figures",
    ):
        path = directory / relative_path
        if path.suffix:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"# {relative_path}\n", encoding="utf-8")
        else:
            path.mkdir(parents=True, exist_ok=True)
            (path / ".gitkeep").write_text("", encoding="utf-8")

    data = yaml.safe_load(data_package_manifest())
    if mutate is not None:
        mutate(data)
    manifest_path = directory / "data-package.yaml"
    manifest_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
    return manifest_path


class TemplateDrivenOutputTests(unittest.TestCase):
    def run_package_builder(self, directory: Path, manifest: dict) -> tuple[int, Path, str, str]:
        manifest_path = directory / "submission-manifest.yaml"
        output_dir = directory / "submission-package"
        manifest_path.write_text(yaml.safe_dump(manifest), encoding="utf-8")
        stdout = StringIO()
        stderr = StringIO()

        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = build_submission_package.main(
                ["--manifest", str(manifest_path), "--output-dir", str(output_dir)]
            )

        return status, output_dir, stdout.getvalue(), stderr.getvalue()

    def test_nature_materials_omits_disabled_keywords_and_funding(self) -> None:
        template = load_template("nature-materials")
        manifest = manifest_for("nature-materials", "short-communication")

        checklist = generate_checklist.render_checklist(template, "short-communication")
        declarations = build_submission_package.render_declarations(manifest, template)
        cover_letter = generate_cover_letter.render_cover_letter(manifest, template, "")

        self.assertNotIn("Keywords", checklist)
        self.assertNotIn("Funding:", declarations)
        self.assertNotIn("Funding:", cover_letter)

        with tempfile.TemporaryDirectory() as directory:
            package_dir = Path(directory) / "submission-package"
            written = build_submission_package.write_package(
                package_dir,
                manifest,
                template,
                {},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "",
            )
            self.assertNotIn("keywords.md", written)
            self.assertFalse((package_dir / "keywords.md").exists())

    def test_jmca_omits_disabled_funding_in_all_declaration_outputs(self) -> None:
        template = load_template("jmca")
        manifest = manifest_for("jmca", "perspective")

        declarations = build_submission_package.render_declarations(manifest, template)
        cover_letter = build_submission_package.render_cover_letter_inline(manifest, template, "")

        self.assertNotIn("Funding:", declarations)
        self.assertNotIn("Funding:", cover_letter)

    def test_building_environment_letter_marks_abstract_not_required(self) -> None:
        template = load_template("building-environment")
        letter = next(
            item for item in template["article_types"] if item["id"] == "letter"
        )

        checklist = generate_checklist.render_checklist(template, "letter")

        self.assertIn("abstract", letter.get("required_fields_exclude", []))
        self.assertIn("No abstract required for this article type", checklist)
        self.assertNotIn("abstract within", checklist)

    def test_validator_rejects_missing_article_type_field_exclusion(self) -> None:
        content = """
journal_id: example
article_types:
  - id: letter
    submission_label: Letter
    abstract_required: false
required_fields:
  - title
  - abstract
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "example.yaml"
            path.write_text(content, encoding="utf-8")
            path.with_suffix(".md").write_text("# Example\n", encoding="utf-8")
            issues: list[str] = []

            validate_journal_templates.validate_template(path, issues)

        self.assertTrue(
            any("disables abstract" in issue for issue in issues),
            issues,
        )

    def test_invalid_article_type_dry_run_does_not_raise_while_listing_files(self) -> None:
        manifest = SKILL_DIR / "evals" / "invalid-acta-review.yaml"
        stdout = StringIO()
        stderr = StringIO()

        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = build_submission_package.main(
                ["--manifest", str(manifest), "--dry-run"]
            )

        self.assertEqual(0, status)
        self.assertIn("article_type 'review-article' not in", stderr.getvalue())
        self.assertIn("Files that would be written:", stdout.getvalue())

    def test_disabled_data_availability_is_omitted_from_declarations(self) -> None:
        template = copy.deepcopy(load_template("nature-materials"))
        template["declaration_requirements"]["data_availability"] = False
        manifest = manifest_for("nature-materials")

        declarations = build_submission_package.render_declarations(manifest, template)
        cover_letter = generate_cover_letter.render_cover_letter(manifest, template, "")

        self.assertNotIn("Data availability", declarations)
        self.assertNotIn("Data availability", cover_letter)

    def test_validator_rejects_invalid_declaration_requirement_value(self) -> None:
        content = """
journal_id: example
article_types:
  - id: research-article
    submission_label: Article
required_fields:
  - title
declaration_requirements:
  data_availability: "false"
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "example.yaml"
            path.write_text(content, encoding="utf-8")
            path.with_suffix(".md").write_text("# Example\n", encoding="utf-8")
            issues: list[str] = []

            validate_journal_templates.validate_template(path, issues)

        self.assertTrue(
            any("invalid declaration requirement" in issue for issue in issues),
            issues,
        )

    def test_reusing_package_directory_removes_only_stale_owned_artifacts(self) -> None:
        cbm = load_template("cbm")
        nature = load_template("nature-materials")
        manifest = manifest_for("cbm")

        with tempfile.TemporaryDirectory() as directory:
            package_dir = Path(directory) / "submission-package"
            build_submission_package.write_package(
                package_dir,
                manifest,
                cbm,
                {"keywords": ["emulsion", "bonding"]},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "A test abstract.",
            )
            (package_dir / "user-notes.md").write_text("keep me", encoding="utf-8")

            build_submission_package.write_package(
                package_dir,
                manifest_for("nature-materials"),
                nature,
                {},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "A test abstract.",
            )

            self.assertFalse((package_dir / "highlights.md").exists())
            self.assertFalse((package_dir / "keywords.md").exists())
            self.assertTrue((package_dir / "declarations.md").exists())

            no_declarations = copy.deepcopy(nature)
            no_declarations["required_fields"].remove("declarations")
            build_submission_package.write_package(
                package_dir,
                manifest_for("nature-materials"),
                no_declarations,
                {},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "A test abstract.",
            )

            self.assertFalse((package_dir / "declarations.md").exists())
            self.assertEqual("keep me", (package_dir / "user-notes.md").read_text(encoding="utf-8"))

    def test_reusing_package_directory_preserves_modified_optional_artifact(self) -> None:
        cbm = load_template("cbm")
        nature = load_template("nature-materials")
        manifest = manifest_for("cbm")

        with tempfile.TemporaryDirectory() as directory:
            package_dir = Path(directory) / "submission-package"
            build_submission_package.write_package(
                package_dir,
                manifest,
                cbm,
                {"keywords": ["emulsion", "bonding"]},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "A test abstract.",
            )
            manual_keywords = "# Keywords\n\n- manually curated term\n"
            (package_dir / "keywords.md").write_text(manual_keywords, encoding="utf-8")

            build_submission_package.write_package(
                package_dir,
                manifest_for("nature-materials"),
                nature,
                {},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "A test abstract.",
            )

            self.assertEqual(
                manual_keywords,
                (package_dir / "keywords.md").read_text(encoding="utf-8"),
            )
            handoff = yaml.safe_load(
                (package_dir / "submission-package.yaml").read_text(encoding="utf-8")
            )
            keyword_record = handoff["artifacts"]["keywords"]
            self.assertEqual("ready", keyword_record["status"])
            self.assertEqual("keywords.md", keyword_record["path"])
            self.assertEqual("user-preserved", keyword_record["ownership"])
            self.assertEqual(
                hashlib.sha256((package_dir / "keywords.md").read_bytes()).hexdigest(),
                keyword_record["sha256"],
            )

            build_submission_package.write_package(
                package_dir,
                manifest_for("nature-materials"),
                nature,
                {},
                {"G6": "not_applicable", "G7": "not_applicable"},
                "A test abstract.",
            )

            self.assertTrue((package_dir / "keywords.md").exists())
            self.assertEqual(
                manual_keywords,
                (package_dir / "keywords.md").read_text(encoding="utf-8"),
            )
            handoff = yaml.safe_load(
                (package_dir / "submission-package.yaml").read_text(encoding="utf-8")
            )
            keyword_record = handoff["artifacts"]["keywords"]
            self.assertEqual("ready", keyword_record["status"])
            self.assertEqual("keywords.md", keyword_record["path"])
            self.assertEqual("user-preserved", keyword_record["ownership"])
            self.assertEqual(
                hashlib.sha256((package_dir / "keywords.md").read_bytes()).hexdigest(),
                keyword_record["sha256"],
            )

    def test_refused_rebuild_removes_stale_owned_handoff_but_keeps_user_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = manifest_for("cbm")
            manifest["data_availability_status"] = "not-applicable"

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            self.assertTrue((package_dir / "submission-package.yaml").is_file())
            (package_dir / "user-notes.md").write_text("keep me", encoding="utf-8")

            manifest["live_verification_acknowledged"] = False
            status, _, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("Refusal conditions met:", stderr)
            self.assertFalse((package_dir / "submission-package.yaml").exists())
            self.assertEqual("keep me", (package_dir / "user-notes.md").read_text(encoding="utf-8"))

    def test_write_error_removes_stale_owned_handoff_before_partial_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            package_dir = Path(directory) / "submission-package"
            package_dir.mkdir()
            (package_dir / "submission-package.yaml").write_text(
                "status: ready\n",
                encoding="utf-8",
            )
            (package_dir / "cover-letter.md").mkdir()

            with self.assertRaises(OSError):
                build_submission_package.write_package(
                    package_dir,
                    dict(manifest_for("cbm"), data_availability_status="not-applicable"),
                    load_template("cbm"),
                    {},
                    {"G6": "not_applicable", "G7": "not_applicable"},
                    "",
                )

            self.assertFalse((package_dir / "submission-package.yaml").exists())

    def test_package_handoff_is_parseable_and_satisfies_shared_contract(self) -> None:
        contract_path = SKILL_DIR.parents[1] / "_shared" / "contracts" / "submission-package.yaml"
        contract = yaml.safe_load(contract_path.read_text(encoding="utf-8"))

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fair_manifest = write_ready_data_package(root)
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(fair_manifest)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            handoff_path = package_dir / "submission-package.yaml"
            self.assertTrue(handoff_path.is_file())
            handoff = yaml.safe_load(handoff_path.read_text(encoding="utf-8"))
            self.assertIsInstance(handoff, dict)
            self.assertTrue(set(contract["required_fields"]).issubset(handoff))
            self.assertEqual("ready", handoff["status"])
            self.assertEqual(str(package_dir.resolve()), handoff["package_dir"])
            self.assertEqual("cbm", handoff["target_journal"])
            self.assertEqual("research-article", handoff["article_type"])
            self.assertEqual("ready", handoff["artifacts"]["cover_letter"]["status"])
            self.assertEqual("cover-letter.md", handoff["artifacts"]["cover_letter"]["path"])
            self.assertIn("word_limit", handoff["verification"]["placeholders"])

    def test_writing_state_supplies_missing_submission_metadata_before_validation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state_path = root / "state.json"
            state_path.write_text(
                json.dumps(
                    {
                        "project": {"title": "Writing-state title"},
                        "abstract": "Writing-state abstract.",
                        "authors": [{"name": "Writing Author", "corresponding": True}],
                        "keywords": ["interface", "adhesion"],
                    }
                ),
                encoding="utf-8",
            )
            manifest = {
                "target_journal": "cbm",
                "article_type": "research-article",
                "data_availability_status": "not-applicable",
                "writing_state_path": str(state_path),
                "live_verification_acknowledged": True,
            }

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            self.assertTrue(package_dir.is_dir())
            self.assertIn("Writing-state title", (package_dir / "cover-letter.md").read_text(encoding="utf-8"))
            self.assertIn("Writing Author", (package_dir / "cover-letter.md").read_text(encoding="utf-8"))
            self.assertIn("- interface", (package_dir / "keywords.md").read_text(encoding="utf-8"))

    def test_explicit_submission_manifest_metadata_overrides_writing_state(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state_path = root / "state.json"
            state_path.write_text(
                json.dumps(
                    {
                        "project": {"title": "Writing-state title"},
                        "authors": [{"name": "Writing Author", "corresponding": True}],
                    }
                ),
                encoding="utf-8",
            )
            manifest = {
                "target_journal": "cbm",
                "article_type": "research-article",
                "title": "Explicit manifest title",
                "corresponding_author": "Explicit Author",
                "data_availability_status": "not-applicable",
                "writing_state_path": str(state_path),
                "live_verification_acknowledged": True,
            }

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            cover_letter = (package_dir / "cover-letter.md").read_text(encoding="utf-8")
            self.assertIn("Explicit manifest title", cover_letter)
            self.assertIn("Explicit Author", cover_letter)
            self.assertNotIn("Writing-state title", cover_letter)

    def test_explicit_author_list_supplies_corresponding_author_before_writing_state(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state_path = root / "state.json"
            state_path.write_text(
                json.dumps(
                    {
                        "corresponding_author": "Writing-state Author",
                        "authors": [{"name": "Writing-state Author", "corresponding": True}],
                    }
                ),
                encoding="utf-8",
            )
            manifest = {
                "target_journal": "cbm",
                "article_type": "research-article",
                "title": "Explicit authors",
                "authors": [{"name": "Explicit Author", "corresponding": True}],
                "data_availability_status": "not-applicable",
                "writing_state_path": str(state_path),
                "live_verification_acknowledged": True,
            }

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            cover_letter = (package_dir / "cover-letter.md").read_text(encoding="utf-8")
            self.assertIn("Explicit Author", cover_letter)
            self.assertNotIn("Writing-state Author", cover_letter)

    def test_figure_and_fair_inputs_are_loaded_into_handoff_statuses(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            figure_manifest = root / "figure-package.yaml"
            figure_manifest.write_text(
                "status: ready\ncaption_boundary: checked\n",
                encoding="utf-8",
            )
            fair_manifest = write_ready_data_package(root)
            manifest = manifest_for("cbm")
            manifest["figure_package_path"] = str(figure_manifest)
            manifest["fair_package_path"] = str(fair_manifest)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            handoff_path = package_dir / "submission-package.yaml"
            self.assertTrue(handoff_path.is_file())
            handoff = yaml.safe_load(handoff_path.read_text(encoding="utf-8"))
            self.assertEqual("loaded", handoff["inputs"]["figure_package"]["status"])
            self.assertEqual("ready", handoff["inputs"]["figure_package"]["artifact_status"])
            self.assertEqual("loaded", handoff["inputs"]["fair_package"]["status"])
            self.assertEqual("ready", handoff["inputs"]["fair_package"]["artifact_status"])

    def test_materials_data_producer_package_directory_is_accepted_as_ready_fair_input(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            data_package_dir = build_fair_package.build_package(
                "Submission FAIR data",
                "asphalt",
                "cbm",
                root,
            )
            data_manifest = data_package_dir / "data-package.yaml"
            self.assertTrue(data_manifest.is_file())

            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(data_package_dir)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            handoff = yaml.safe_load(
                (package_dir / "submission-package.yaml").read_text(encoding="utf-8")
            )
            fair_input = handoff["inputs"]["fair_package"]
            self.assertEqual("loaded", fair_input["status"])
            self.assertEqual("ready", fair_input["artifact_status"])
            self.assertEqual("data-package", fair_input["contract"])
            self.assertEqual(str(data_manifest.resolve()), fair_input["resolved_path"])

    def test_ready_fair_status_rejects_arbitrary_ready_mapping(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fake_manifest = root / "fake-ready.yaml"
            fake_manifest.write_text("status: ready\n", encoding="utf-8")
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(fake_manifest)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("expected data-package contract", stderr)
            self.assertFalse(package_dir.exists())

    def test_ready_fair_status_rejects_submission_handoff_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            submission_handoff = root / "submission-package.yaml"
            submission_handoff.write_text(
                "contract: submission-package\nstatus: ready\n",
                encoding="utf-8",
            )
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(submission_handoff)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("expected data-package contract", stderr)
            self.assertFalse(package_dir.exists())

    def test_figure_package_directory_uses_asset_manifest_json(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            figure_package = root / "figure-package"
            figure_package.mkdir()
            (figure_package / "asset_manifest.json").write_text(
                json.dumps({"title": "Figure package", "panels": []}),
                encoding="utf-8",
            )
            manifest = manifest_for("cbm")
            manifest["figure_package_path"] = str(figure_package)
            manifest["data_availability_status"] = "not-applicable"

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status, stderr)
            handoff = yaml.safe_load(
                (package_dir / "submission-package.yaml").read_text(encoding="utf-8")
            )
            figure_input = handoff["inputs"]["figure_package"]
            self.assertEqual("loaded", figure_input["status"])
            self.assertEqual(
                str((figure_package / "asset_manifest.json").resolve()),
                figure_input["resolved_path"],
            )

    def test_ready_fair_status_requires_a_parseable_fair_manifest(self) -> None:
        template = load_template("cbm")
        manifest = manifest_for("cbm")
        manifest["fair_package_path"] = "does-not-exist.yaml"

        declarations = build_submission_package.render_declarations(manifest, template)

        self.assertNotIn("ready (see FAIR package)", declarations)
        self.assertIn("[LIVE-VERIFICATION:", declarations)

        with tempfile.TemporaryDirectory() as directory:
            status, package_dir, _, stderr = self.run_package_builder(Path(directory), manifest)

            self.assertEqual(0, status)
            self.assertIn("data_availability_status is ready", stderr)
            self.assertFalse(package_dir.exists())

    def test_ready_fair_status_rejects_manifest_without_ready_status(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fair_manifest = root / "fair-package.yaml"
            fair_manifest.write_text("{}\n", encoding="utf-8")
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(fair_manifest)

            status, package_dir, stdout, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("status ready", stderr)
            self.assertNotIn("ready (see FAIR package)", stdout)
            self.assertFalse(package_dir.exists())

    def test_ready_fair_status_enforces_data_package_contract_details(self) -> None:
        cases = [
            (
                "bad contract_version",
                lambda data: data.__setitem__("contract_version", "2.0"),
                "contract_version must be 1.0",
            ),
            (
                "missing status",
                lambda data: data.pop("status"),
                "missing required field status",
            ),
            (
                "missing package_dir",
                lambda data: data.pop("package_dir"),
                "missing required field package_dir",
            ),
            (
                "missing artifacts",
                lambda data: data.pop("artifacts"),
                "missing required field artifacts",
            ),
            (
                "missing required artifact key",
                lambda data: data["artifacts"].pop("fair_audit"),
                "missing required artifact fair_audit",
            ),
            (
                "missing artifact status",
                lambda data: data["artifacts"]["metadata"].pop("status"),
                "artifact metadata missing status",
            ),
            (
                "invalid artifact status",
                lambda data: data["artifacts"]["metadata"].__setitem__("status", "blocked"),
                "artifact metadata status blocked not in",
            ),
            (
                "ready package requires ready artifact",
                lambda data: data["artifacts"]["metadata"].__setitem__("status", "missing"),
                "ready data-package requires artifact metadata status ready",
            ),
        ]

        for label, mutate, expected_error in cases:
            with self.subTest(label=label):
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    fair_manifest = write_ready_data_package(root, mutate=mutate)
                    manifest = manifest_for("cbm")
                    manifest["fair_package_path"] = str(fair_manifest)

                    status, package_dir, _, stderr = self.run_package_builder(root, manifest)

                    self.assertEqual(0, status)
                    self.assertIn(expected_error, stderr)
                    self.assertFalse(package_dir.exists())

    def test_ready_fair_status_rejects_missing_package_dir(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fair_manifest = write_ready_data_package(
                root,
                mutate=lambda data: data.__setitem__("package_dir", "missing-data-package"),
            )
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(fair_manifest)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("package_dir does not exist", stderr)
            self.assertFalse(package_dir.exists())

    def test_ready_fair_status_rejects_missing_ready_artifact_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fair_manifest = write_ready_data_package(
                root,
                mutate=lambda data: data["artifacts"]["metadata"].__setitem__(
                    "path",
                    "missing-metadata.md",
                ),
            )
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(fair_manifest)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("artifact metadata path does not exist", stderr)
            self.assertFalse(package_dir.exists())

    def test_ready_fair_status_rejects_artifact_path_outside_package_dir(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "outside-metadata.md").write_text("# outside\n", encoding="utf-8")
            fair_manifest = write_ready_data_package(
                root / "data-package",
                mutate=lambda data: data["artifacts"]["metadata"].__setitem__(
                    "path",
                    "../outside-metadata.md",
                ),
            )
            manifest = manifest_for("cbm")
            manifest["fair_package_path"] = str(fair_manifest)

            status, package_dir, _, stderr = self.run_package_builder(root, manifest)

            self.assertEqual(0, status)
            self.assertIn("artifact metadata path escapes package_dir", stderr)
            self.assertFalse(package_dir.exists())

    def test_eval_valid_fair_fixture_declares_data_package_contract(self) -> None:
        fixture = SKILL_DIR / "evals" / "valid-fair-package.yaml"

        self.assertTrue(fixture.is_file())
        data = yaml.safe_load(fixture.read_text(encoding="utf-8"))

        self.assertEqual("data-package", data.get("contract"))
        self.assertEqual("1.0", data.get("contract_version"))
        self.assertEqual("ready", data.get("status"))
        package_dir = (fixture.parent / data["package_dir"]).resolve()
        self.assertTrue(package_dir.is_dir())
        for artifact in data["artifacts"].values():
            self.assertTrue((package_dir / artifact["path"]).exists())

    def test_malformed_submission_manifest_returns_nonzero_with_clear_error(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest_path = root / "submission-manifest.yaml"
            manifest_path.write_text("target_journal: [unterminated\n", encoding="utf-8")
            stdout = StringIO()
            stderr = StringIO()

            with redirect_stdout(stdout), redirect_stderr(stderr):
                status = build_submission_package.main(
                    ["--manifest", str(manifest_path), "--dry-run"]
                )

            self.assertEqual(1, status)
            self.assertIn("could not parse manifest", stderr.getvalue())
            self.assertNotIn("=== DRY RUN ===", stdout.getvalue())

    def test_highlights_reject_counts_outside_template_range(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for count in (2, 6):
                highlights_path = root / f"{count}-highlights.md"
                highlights_path.write_text(
                    "\n".join(f"{index}. Highlight {index}" for index in range(1, count + 1)),
                    encoding="utf-8",
                )
                stderr = StringIO()

                with redirect_stderr(stderr):
                    status = generate_highlights.main(
                        ["--journal", "cbm", "--highlights-file", str(highlights_path)]
                    )

                self.assertEqual(1, status, stderr.getvalue())
                self.assertIn(f"found {count}", stderr.getvalue())

    def test_highlights_reject_items_over_template_character_limit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            highlights_path = Path(directory) / "long-highlights.md"
            highlights_path.write_text(
                "\n".join(
                    [
                        "1. Short highlight",
                        "2. " + "x" * 86,
                        "3. Another short highlight",
                    ]
                ),
                encoding="utf-8",
            )
            stderr = StringIO()

            with redirect_stderr(stderr):
                status = generate_highlights.main(
                    ["--journal", "cbm", "--highlights-file", str(highlights_path)]
                )

            self.assertEqual(1, status, stderr.getvalue())
            self.assertIn("Highlights exceeding character limit:", stderr.getvalue())
            self.assertIn("(86 chars)", stderr.getvalue())

    def test_checklist_uses_only_template_declared_figure_and_reference_items(self) -> None:
        cbm_checklist = generate_checklist.render_checklist(
            load_template("cbm"),
            "research-article",
        )
        acta_checklist = generate_checklist.render_checklist(
            load_template("acta-materialia"),
            "research-article",
        )

        self.assertNotIn("Figures meet resolution and format requirements", cbm_checklist)
        self.assertNotIn("References in journal style", cbm_checklist)
        self.assertNotIn("Panel labels lowercase in parentheses", cbm_checklist)
        self.assertNotIn("Graphical abstract", cbm_checklist)
        self.assertIn("Graphical abstract", acta_checklist)

    def test_submission_manifest_does_not_route_ijpe_to_rmpd_template(self) -> None:
        manifest = yaml.safe_load((SKILL_DIR / "manifest.yaml").read_text(encoding="utf-8"))
        rmpd_route = manifest["axes"]["journal"]["values"]["rmpd"]
        rmpd_reference = manifest["references"]["on_demand"]["journal-rmpd-facts"]

        self.assertNotIn("IJPE", rmpd_route["triggers"])
        self.assertNotIn("International Journal of Pavement Engineering", rmpd_route["triggers"])
        self.assertNotIn("IJPE", rmpd_reference["when"])

    def test_submission_docs_route_final_assembly_to_ten_supported_templates(self) -> None:
        repo_root = SKILL_DIR.parents[3]
        root_readme = (repo_root / "README.md").read_text(encoding="utf-8")
        companion = (
            repo_root
            / "plugins"
            / "materials-skills"
            / "skills"
            / "materials-research"
            / "references"
            / "companion-modules.md"
        ).read_text(encoding="utf-8")
        orchestrator = (
            repo_root
            / "plugins"
            / "materials-skills"
            / "skills"
            / "materials-research"
            / "references"
            / "paper-production-orchestrator.md"
        ).read_text(encoding="utf-8")
        fragment = (
            repo_root
            / "plugins"
            / "materials-skills"
            / "skills"
            / "materials-research"
            / "static"
            / "fragments"
            / "task"
            / "submission-package.md"
        ).read_text(encoding="utf-8")
        submission_readme = (SKILL_DIR / "README.md").read_text(encoding="utf-8")
        skills_index = (repo_root / "docs" / "skills-index.md").read_text(encoding="utf-8")

        self.assertIn("10 supported journal templates", root_readme)
        self.assertIn("initial four-journal pilot", root_readme)
        self.assertEqual(14, root_readme.count("| [`materials-"))
        self.assertIn("Skill index (14 skills)", root_readme)
        self.assertIn("10 supported journal templates", companion)
        self.assertIn("| Final assembly | materials-submission |", orchestrator)
        self.assertIn("submission-package.yaml", orchestrator)
        self.assertIn("Hand off final assembly to `materials-submission`", fragment)
        self.assertIn("10 supported journal templates", submission_readme)
        self.assertIn("10 supported journal templates", skills_index)


if __name__ == "__main__":
    unittest.main()
