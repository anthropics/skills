"""Assemble a submission package from a manifest.

Reads submission-manifest.yaml, checks refusal conditions, loads journal
facts and template, and writes submission-package/ with cover letter,
highlights, checklist, declarations, keywords, SOURCE stubs, and
reviewer-risk-regression. Use --dry-run to validate without writing.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import sys
from pathlib import Path
from typing import Any

import yaml

from template_support import (
    SUPPORTED_JOURNALS,
    append_declaration_checklist_items,
    append_required_field_items,
    append_required_artifacts,
    article_type_label,
    find_article_type,
    field_is_required,
    load_template,
    required_fields_for_article_type,
)

SKILL_DIR = Path(__file__).resolve().parents[1]
DATA_PACKAGE_CONTRACT_PATH = SKILL_DIR.parents[1] / "_shared" / "contracts" / "data-package.yaml"
MANAGED_OPTIONAL_ARTIFACTS = (
    "highlights.md",
    "keywords.md",
    "declarations.md",
)
MANAGED_HANDOFF_ARTIFACT = "submission-package.yaml"
DIRECTORY_MANIFEST_CANDIDATES = (
    "submission-package.yaml",
    "package_manifest.yaml",
    "package_manifest.json",
    "manifest.yaml",
    "manifest.json",
    "asset_manifest.json",
    "figure-handoff.yaml",
    "figure_handoff.yaml",
    "fair-package.yaml",
    "fair_package.yaml",
    "experiment_record_link.yaml",
)
FAIR_DIRECTORY_MANIFEST_CANDIDATES = (
    "data-package.yaml",
    "data_package.yaml",
)
EXPECTED_FAIR_CONTRACT = "data-package"


def load_yaml(path: Path) -> dict:
    data, status = load_structured_mapping(path)
    if status != "loaded":
        raise ValueError(f"could not parse manifest: {path} ({status})")
    return data


def load_structured_mapping(path: Path) -> tuple[dict, str]:
    """Load a YAML or JSON mapping without treating malformed input as usable."""
    if not path.exists():
        return {}, "missing"
    if not path.is_file():
        return {}, "unparseable"
    try:
        with path.open(encoding="utf-8") as fh:
            value = yaml.safe_load(fh)
    except OSError:
        return {}, "unreadable"
    except yaml.YAMLError:
        return {}, "unparseable"
    if not isinstance(value, dict):
        return {}, "unparseable"
    return value, "loaded"


def resolve_input_path(path_text: str, base_dir: Path | None = None) -> Path:
    path = Path(path_text).expanduser()
    if not path.is_absolute() and base_dir is not None:
        path = base_dir / path
    return path.resolve()


def _declared_contract(data: dict) -> str | None:
    for key in ("contract", "name", "handoff"):
        value = data.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return None


def _contract_validation_error(
    data: dict,
    expected_contract: str,
    manifest_dir: Path | None = None,
) -> str | None:
    if expected_contract == EXPECTED_FAIR_CONTRACT:
        return _data_package_validation_error(data, manifest_dir)
    contract = _declared_contract(data)
    if contract != expected_contract:
        found = contract or "none"
        return f"expected {expected_contract} contract, found {found}"
    version = data.get("contract_version") or data.get("version")
    if not isinstance(version, str) or not version.strip():
        return f"expected {expected_contract} contract_version"
    return None


def _data_package_contract() -> dict:
    return yaml.safe_load(DATA_PACKAGE_CONTRACT_PATH.read_text(encoding="utf-8"))


def _missing_required_field(data: dict, field: str) -> bool:
    if field not in data or data[field] is None:
        return True
    value = data[field]
    if isinstance(value, str):
        return not value.strip()
    if field == "artifacts":
        return not isinstance(value, dict) or not value
    return False


def _is_relative_to(path: Path, base: Path) -> bool:
    try:
        path.relative_to(base)
        return True
    except ValueError:
        return False


def _data_package_validation_error(data: dict, manifest_dir: Path | None = None) -> str | None:
    contract = _data_package_contract()
    declared = _declared_contract(data)
    if declared != EXPECTED_FAIR_CONTRACT:
        found = declared or "none"
        return f"expected {EXPECTED_FAIR_CONTRACT} contract, found {found}"

    expected_version = str(contract.get("version", ""))
    if data.get("contract_version") != expected_version:
        return f"contract_version must be {expected_version}"

    for field in contract.get("required_fields", []):
        if _missing_required_field(data, field):
            return f"missing required field {field}"

    status = data.get("status")
    status_values = contract.get("status_values", [])
    if status not in status_values:
        return f"status {status} not in {status_values}"

    artifacts = data.get("artifacts")
    if not isinstance(artifacts, dict):
        return "missing required field artifacts"

    package_dir_text = data.get("package_dir")
    if not isinstance(package_dir_text, str) or not package_dir_text.strip():
        return "missing required field package_dir"
    package_dir = resolve_input_path(package_dir_text, manifest_dir)
    if not package_dir.is_dir():
        return "package_dir does not exist"

    artifact_status_values = contract.get("artifact_status_values", [])
    for key in contract.get("required_artifacts", []):
        artifact = artifacts.get(key)
        if not isinstance(artifact, dict):
            return f"missing required artifact {key}"
        artifact_status = artifact.get("status")
        if not isinstance(artifact_status, str) or not artifact_status.strip():
            return f"artifact {key} missing status"
        if artifact_status not in artifact_status_values:
            return f"artifact {key} status {artifact_status} not in {artifact_status_values}"
        if status == "ready" and artifact_status != "ready":
            return f"ready data-package requires artifact {key} status ready"
        if artifact_status == "ready":
            artifact_path_text = artifact.get("path")
            if not isinstance(artifact_path_text, str) or not artifact_path_text.strip():
                return f"artifact {key} missing path"
            artifact_path = resolve_input_path(artifact_path_text, package_dir)
            if not _is_relative_to(artifact_path, package_dir):
                return f"artifact {key} path escapes package_dir"
            if not artifact_path.exists():
                return f"artifact {key} path does not exist"
    return None


def input_record(
    path_text: str,
    base_dir: Path | None = None,
    *,
    expected_contract: str | None = None,
    directory_manifest_candidates: tuple[str, ...] = DIRECTORY_MANIFEST_CANDIDATES,
) -> tuple[dict, dict]:
    """Read one optional structured artifact and return its handoff status."""
    record: dict[str, Any] = {
        "path": path_text or None,
        "resolved_path": None,
        "status": "not_supplied",
        "artifact_status": "not_applicable",
        "contract": None,
        "validation_error": None,
    }
    if not path_text:
        return {}, record

    candidate = resolve_input_path(path_text, base_dir)
    if not candidate.exists():
        record["resolved_path"] = str(candidate)
        record["status"] = "missing"
        record["artifact_status"] = "missing"
        return {}, record
    if candidate.is_dir():
        manifest_path = next(
            (
                candidate / filename
                for filename in directory_manifest_candidates
                if (candidate / filename).is_file()
            ),
            None,
        )
        if manifest_path is None:
            record["resolved_path"] = str(candidate)
            record["status"] = "unparseable"
            record["artifact_status"] = "not_declared"
            if expected_contract:
                record["validation_error"] = (
                    f"expected {expected_contract} contract manifest in directory"
                )
            return {}, record
        candidate = manifest_path

    data, status = load_structured_mapping(candidate)
    record["resolved_path"] = str(candidate)
    record["status"] = status
    if status == "loaded":
        record["contract"] = _declared_contract(data)
        if expected_contract:
            validation_error = _contract_validation_error(data, expected_contract, candidate.parent)
            if validation_error:
                record["status"] = "unparseable"
                record["artifact_status"] = "wrong_contract"
                record["validation_error"] = validation_error
                return data, record
        artifact_status = data.get("status")
        record["artifact_status"] = (
            str(artifact_status) if isinstance(artifact_status, str) and artifact_status else "not_declared"
        )
    else:
        record["artifact_status"] = "not_declared"
    return data, record


def _present(value: object) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    return bool(value)


def _author_name(author: object) -> str | None:
    if isinstance(author, str) and author.strip():
        return author.strip()
    if isinstance(author, dict):
        for field in ("name", "full_name", "display_name"):
            value = author.get(field)
            if isinstance(value, str) and value.strip():
                return value.strip()
    return None


def corresponding_author_from_authors(authors: object) -> str | None:
    """Return the marked corresponding author from a conventional author list."""
    if not isinstance(authors, list):
        return None
    for author in authors:
        if not isinstance(author, dict):
            continue
        if author.get("corresponding") or author.get("is_corresponding"):
            return _author_name(author)
    return None


def _writing_value(writing_state: dict, field: str) -> object:
    manuscript = writing_state.get("manuscript")
    manuscript = manuscript if isinstance(manuscript, dict) else {}
    project = writing_state.get("project")
    project = project if isinstance(project, dict) else {}

    if field == "title":
        return writing_state.get("title") or manuscript.get("title") or project.get("title")
    if field == "corresponding_author":
        direct = writing_state.get(field) or manuscript.get(field)
        if _present(direct):
            return direct
        return corresponding_author_from_authors(
            writing_state.get("authors") or manuscript.get("authors")
        )
    return writing_state.get(field) or manuscript.get(field)


def hydrate_manifest_from_writing_state(manifest: dict, writing_state: dict) -> dict:
    """Apply writing-state metadata only where the submission manifest is blank."""
    hydrated = dict(manifest)
    for field in ("title", "abstract", "authors", "keywords"):
        if not _present(hydrated.get(field)):
            value = _writing_value(writing_state, field)
            if _present(value):
                hydrated[field] = value
    if not _present(hydrated.get("corresponding_author")):
        explicit_author = corresponding_author_from_authors(hydrated.get("authors"))
        if _present(explicit_author):
            hydrated["corresponding_author"] = explicit_author
        else:
            value = _writing_value(writing_state, "corresponding_author")
            if _present(value):
                hydrated["corresponding_author"] = value
    return hydrated


def prepare_submission_inputs(manifest: dict, manifest_dir: Path) -> tuple[dict, dict, dict]:
    """Load optional inputs before validation and preserve their usable statuses."""
    writing_state, writing_input = input_record(
        str(manifest.get("writing_state_path") or ""),
        manifest_dir,
    )
    _, figure_input = input_record(
        str(manifest.get("figure_package_path") or ""),
        manifest_dir,
    )
    _, fair_input = input_record(
        str(manifest.get("fair_package_path") or ""),
        manifest_dir,
        expected_contract=EXPECTED_FAIR_CONTRACT,
        directory_manifest_candidates=FAIR_DIRECTORY_MANIFEST_CANDIDATES,
    )
    inputs = {
        "writing_state": writing_input,
        "figure_package": figure_input,
        "fair_package": fair_input,
    }
    return hydrate_manifest_from_writing_state(manifest, writing_state), writing_state, inputs


def check_refusal(
    manifest: dict,
    template: dict | None = None,
    inputs: dict | None = None,
) -> list[str]:
    reasons = []
    if not manifest.get("live_verification_acknowledged"):
        reasons.append("live_verification_acknowledged is false")
    journal = manifest.get("target_journal")
    if journal not in SUPPORTED_JOURNALS:
        reasons.append(f"target_journal {journal!r} not in supported journals {SUPPORTED_JOURNALS}")
    fair_input = (inputs or {}).get("fair_package", {})
    if (
        manifest.get("data_availability_status") == "ready"
        and (
            fair_input.get("status") != "loaded"
            or fair_input.get("artifact_status") != "ready"
        )
    ):
        detail = fair_input.get("validation_error")
        suffix = f" ({detail})" if detail else ""
        reasons.append(
            "data_availability_status is ready but fair_package_path is not an existing readable "
            f"parseable data-package manifest with status ready{suffix}"
        )
    if manifest.get("data_availability_status") == "pending" and not manifest.get("fair_package_path"):
        reasons.append("data_availability_status is pending but no fair_package_path set")
    if not manifest.get("title"):
        reasons.append("title is missing")
    if not manifest.get("corresponding_author"):
        reasons.append("corresponding_author is missing")
    # Validate article_type against journal template
    article_type = manifest.get("article_type", "research-article")
    if template and template.get("article_types"):
        valid_types = [at.get("id") for at in template["article_types"]]
        if article_type not in valid_types:
            reasons.append(f"article_type {article_type!r} not in {valid_types}")
    return reasons


def read_writing_state(path: str, base_dir: Path | None = None) -> dict:
    if not path:
        return {}
    state, _ = input_record(path, base_dir)
    return state


def read_weakness_routing(path: str, base_dir: Path | None = None) -> list[dict]:
    if not path:
        return []
    rows = []
    resolved_path = resolve_input_path(path, base_dir)
    if not resolved_path.is_file():
        return rows
    with resolved_path.open(encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            rows.append(row)
    return rows


def compute_gate_status(rows: list[dict]) -> dict:
    g6 = "not_applicable"
    g7 = "not_applicable"
    for row in rows:
        gate = row.get("gate_id", "")
        status = row.get("status", "")
        if gate == "G6":
            g6 = status or g6
        if gate == "G7":
            g7 = status or g7
    return {"G6": g6, "G7": g7}


def _default_input_records(manifest: dict) -> dict:
    """Keep direct library callers backward compatible with source stubs."""
    records = {}
    for key, field in (
        ("writing_state", "writing_state_path"),
        ("figure_package", "figure_package_path"),
        ("fair_package", "fair_package_path"),
    ):
        path = str(manifest.get(field) or "")
        records[key] = {
            "path": path or None,
            "resolved_path": None,
            "status": "supplied" if path else "not_supplied",
            "artifact_status": "not_declared" if path else "not_applicable",
        }
    return records


def _data_availability_line(manifest: dict, inputs: dict | None = None) -> str:
    status = manifest.get("data_availability_status", "")
    fair_input = (inputs or {}).get("fair_package", {})
    if (
        status == "ready"
        and fair_input.get("status") == "loaded"
        and fair_input.get("artifact_status") == "ready"
    ):
        return "Data availability: ready (see FAIR package)"
    if status == "not-applicable":
        return "Data availability: not applicable"
    return "[LIVE-VERIFICATION: data availability - user must verify]"


def render_manifest_md(
    manifest: dict,
    template: dict,
    writing_state: dict,
    gates: dict,
    inputs: dict | None = None,
) -> str:
    inputs = inputs or _default_input_records(manifest)
    lines = ["# Submission Package Manifest", ""]
    lines.append(f"Target journal: {manifest.get('target_journal')}")
    lines.append(f"Article type: {manifest.get('article_type')}")
    lines.append(f"Title: {manifest.get('title', '[missing]')}")
    lines.append(f"Corresponding author: {manifest.get('corresponding_author', '[missing]')}")
    lines.append("")
    lines.append("## Source artifacts")
    for label, key in (
        ("writing_state", "writing_state"),
        ("figure_package", "figure_package"),
        ("fair_package", "fair_package"),
    ):
        record = inputs.get(key, {})
        lines.append(
            f"- {label}: {record.get('path') or 'not supplied'} "
            f"(status: {record.get('status', 'not_supplied')}; "
            f"artifact: {record.get('artifact_status', 'not_applicable')})"
        )
    lines.append(f"- weakness_routing: {manifest.get('weakness_routing_path') or 'not supplied'}")
    lines.append("")
    lines.append("## Gate status")
    lines.append(f"- G6 Reviewer Simulation: {gates.get('G6', 'not_applicable')}")
    lines.append(f"- G7 Submission Fit: {gates.get('G7', 'not_applicable')}")
    lines.append("")
    lines.append("## Live verification")
    for field in template.get("live_verification_fields", []):
        lines.append(f"- [LIVE-VERIFICATION: {field}]")
    return "\n".join(lines)


def render_declarations(manifest: dict, template: dict, inputs: dict | None = None) -> str:
    decl_req = template.get("declaration_requirements", {})
    lines = ["# Declarations", ""]
    def _line(label: str, value: str, key: str) -> str:
        if value and value.strip():
            return f"- {label}: {value.strip()}"
        return f"- {label}: [LIVE-VERIFICATION: {key} — user must verify]"
    if decl_req.get("funding"):
        lines.append(_line("Funding", manifest.get("funding", ""), "funding"))
    if decl_req.get("conflict_of_interest"):
        lines.append(_line("Conflict of interest", manifest.get("conflicts", ""), "conflict of interest"))
    if decl_req.get("data_availability"):
        lines.append(f"- Data availability: {_data_availability_line(manifest, inputs)}")
    if decl_req.get("code_availability"):
        code_status = manifest.get("code_availability_status", "")
        if code_status == "ready":
            lines.append("- Code availability: ready")
        elif code_status == "not-applicable":
            lines.append("- Code availability: not applicable")
        else:
            lines.append("- Code availability: [LIVE-VERIFICATION: code availability - verify if custom code was used]")
    if decl_req.get("credit_author_statement"):
        lines.append("- CRediT author statement: [LIVE-VERIFICATION: user must fill CRediT roles]")
    if decl_req.get("ethics"):
        lines.append("- Ethics statement: [LIVE-VERIFICATION: fill if human/animal subjects involved]")
    return "\n".join(lines)


def render_source_stub(label: str, path: str, status: str) -> str:
    lines = [f"# {label} Source", ""]
    lines.append(f"Path: {path or 'not supplied'}")
    lines.append(f"Status: {status}")
    lines.append("")
    lines.append("This stub records the source path. The submission package does not copy content.")
    return "\n".join(lines)


def render_reviewer_risk(gates: dict) -> str:
    lines = ["# Reviewer-Risk Regression", ""]
    lines.append(f"G6 Reviewer Simulation: {gates.get('G6', 'not_applicable')}")
    lines.append(f"G7 Submission Fit: {gates.get('G7', 'not_applicable')}")
    lines.append("")
    if gates.get("G6") == "not_applicable":
        lines.append("Reviewer simulation has not been run. Consider running materials-reviewer before submission.")
    return "\n".join(lines)


def get_suggested_reviewers(manifest: dict) -> list[str]:
    reviewers = manifest.get("suggested_reviewers") or []
    if isinstance(reviewers, str):
        return [reviewers] if reviewers.strip() else []
    if not isinstance(reviewers, list):
        return []
    return [reviewer for reviewer in reviewers if isinstance(reviewer, str) and reviewer.strip()]


def _sha256_file(path: Path) -> str | None:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def _previous_handoff(pkg_dir: Path) -> dict:
    data, status = load_structured_mapping(pkg_dir / MANAGED_HANDOFF_ARTIFACT)
    if status == "loaded" and data.get("contract") == "submission-package":
        return data
    return {}


def _remove_stale_owned_artifacts(pkg_dir: Path, expected: set[str]) -> None:
    """Remove stale optional files only when the previous handoff owns the bytes."""
    previous = _previous_handoff(pkg_dir)
    artifacts = previous.get("artifacts") if isinstance(previous.get("artifacts"), dict) else {}
    for filename in MANAGED_OPTIONAL_ARTIFACTS:
        candidate = pkg_dir / filename
        if filename not in expected and candidate.is_file():
            key = Path(filename).stem
            record = artifacts.get(key) if isinstance(artifacts, dict) else None
            if isinstance(record, dict) and record.get("ownership") == "user-preserved":
                continue
            recorded_hash = record.get("sha256") if isinstance(record, dict) else None
            if recorded_hash and _sha256_file(candidate) == recorded_hash:
                candidate.unlink()


def _remove_stale_handoff(pkg_dir: Path) -> None:
    """Prevent a prior ready handoff from representing a failed rebuild."""
    candidate = pkg_dir / MANAGED_HANDOFF_ARTIFACT
    if candidate.is_file():
        candidate.unlink()


def _artifact_record(package_dir: Path, written: set[str], path: str) -> dict:
    record = {
        "status": "ready" if path in written else "not_required",
        "path": path if path in written else None,
    }
    if path in written:
        digest = _sha256_file(package_dir / path)
        if digest:
            record["sha256"] = digest
            record["generated_by"] = "materials-submission"
    elif (package_dir / path).is_file():
        digest = _sha256_file(package_dir / path)
        record = {
            "status": "ready",
            "path": path,
            "ownership": "user-preserved",
        }
        if digest:
            record["sha256"] = digest
    return record


def render_submission_handoff(
    manifest: dict,
    template: dict,
    package_dir: Path,
    manifest_path: Path | None,
    written: set[str],
    inputs: dict,
    gates: dict,
) -> dict:
    """Build the machine-readable handoff described by submission-package.yaml."""
    artifacts = {
        "package_manifest": _artifact_record(package_dir, written, "MANIFEST.md"),
        "handoff_manifest": {"status": "ready", "path": "submission-package.yaml"},
        "cover_letter": _artifact_record(package_dir, written, "cover-letter.md"),
        "highlights": _artifact_record(package_dir, written, "highlights.md"),
        "keywords": _artifact_record(package_dir, written, "keywords.md"),
        "declarations": _artifact_record(package_dir, written, "declarations.md"),
        "submission_checklist": _artifact_record(package_dir, written, "submission-checklist.md"),
        "manuscript_source": _artifact_record(package_dir, written, "manuscript/SOURCE.md"),
        "figure_source": _artifact_record(package_dir, written, "figures/SOURCE.md"),
        "data_source": _artifact_record(package_dir, written, "data/SOURCE.md"),
        "reviewer_risk_regression": _artifact_record(package_dir, written, "reviewer-risk-regression.md"),
    }
    return {
        "contract": "submission-package",
        "contract_version": "1.0",
        "status": "ready",
        "manifest_path": str(manifest_path.resolve()) if manifest_path else None,
        "target_journal": manifest.get("target_journal"),
        "article_type": manifest.get("article_type"),
        "package_dir": str(package_dir.resolve()),
        "artifacts": artifacts,
        "inputs": inputs,
        "verification": {
            "live_verification_acknowledged": bool(manifest.get("live_verification_acknowledged")),
            "placeholders": list(template.get("live_verification_fields", [])),
            "gate_status": gates,
        },
    }


def write_package(
    pkg_dir: Path,
    manifest: dict,
    template: dict,
    writing_state: dict,
    gates: dict,
    abstract: str,
    inputs: dict | None = None,
    manifest_path: Path | None = None,
) -> list[str]:
    pkg_dir.mkdir(parents=True, exist_ok=True)
    inputs = inputs or _default_input_records(manifest)
    article_type = manifest.get("article_type", "research-article")
    expected_optional = set()
    if template.get("highlights_required"):
        expected_optional.add("highlights.md")
    if field_is_required(template, article_type, "keywords"):
        expected_optional.add("keywords.md")
    if field_is_required(template, article_type, "declarations"):
        expected_optional.add("declarations.md")
    _remove_stale_owned_artifacts(pkg_dir, expected_optional)
    _remove_stale_handoff(pkg_dir)

    written = []
    (pkg_dir / "MANIFEST.md").write_text(
        render_manifest_md(manifest, template, writing_state, gates, inputs),
        encoding="utf-8",
    )
    written.append("MANIFEST.md")
    (pkg_dir / "cover-letter.md").write_text(
        render_cover_letter_inline(manifest, template, abstract, inputs),
        encoding="utf-8",
    )
    written.append("cover-letter.md")
    if template.get("highlights_required"):
        (pkg_dir / "highlights.md").write_text(render_highlights_inline(abstract, template), encoding="utf-8")
        written.append("highlights.md")
    if field_is_required(template, article_type, "keywords"):
        keywords = manifest.get("keywords") or writing_state.get("keywords") or []
        (pkg_dir / "keywords.md").write_text("# Keywords\n\n" + "\n".join(f"- {k}" for k in keywords) + "\n", encoding="utf-8")
        written.append("keywords.md")
    if field_is_required(template, article_type, "declarations"):
        (pkg_dir / "declarations.md").write_text(
            render_declarations(manifest, template, inputs),
            encoding="utf-8",
        )
        written.append("declarations.md")
    (pkg_dir / "submission-checklist.md").write_text(render_checklist_inline(manifest, template), encoding="utf-8")
    written.append("submission-checklist.md")
    (pkg_dir / "manuscript").mkdir(exist_ok=True)
    ws_path = manifest.get("writing_state_path", "")
    ws_status = inputs["writing_state"].get("status", "not_supplied")
    (pkg_dir / "manuscript" / "SOURCE.md").write_text(
        render_source_stub("Manuscript", ws_path, ws_status), encoding="utf-8"
    )
    written.append("manuscript/SOURCE.md")
    (pkg_dir / "figures").mkdir(exist_ok=True)
    fig_path = manifest.get("figure_package_path", "")
    fig_status = inputs["figure_package"].get("status", "not_supplied")
    (pkg_dir / "figures" / "SOURCE.md").write_text(
        render_source_stub("Figures", fig_path, fig_status), encoding="utf-8"
    )
    written.append("figures/SOURCE.md")
    (pkg_dir / "data").mkdir(exist_ok=True)
    fair_path = manifest.get("fair_package_path", "")
    fair_status = inputs["fair_package"].get("status", "not_supplied")
    (pkg_dir / "data" / "SOURCE.md").write_text(
        render_source_stub("Data", fair_path, fair_status), encoding="utf-8"
    )
    written.append("data/SOURCE.md")
    (pkg_dir / "reviewer-risk-regression.md").write_text(render_reviewer_risk(gates), encoding="utf-8")
    written.append("reviewer-risk-regression.md")
    handoff = render_submission_handoff(
        manifest,
        template,
        pkg_dir,
        manifest_path,
        set(written),
        inputs,
        gates,
    )
    (pkg_dir / "submission-package.yaml").write_text(
        yaml.safe_dump(handoff, sort_keys=False, allow_unicode=False),
        encoding="utf-8",
    )
    written.append("submission-package.yaml")
    return written


def render_cover_letter_inline(
    manifest: dict,
    template: dict,
    abstract: str,
    inputs: dict | None = None,
) -> str:
    import datetime as _dt
    journal_name = template.get("full_name", "")
    title = manifest.get("title", "[TITLE MISSING]")
    article_type = manifest.get("article_type", "research-article")
    article_label = article_type_label(template, article_type)
    decl_req = template.get("declaration_requirements", {})
    corresponding = manifest.get("corresponding_author", "[CORRESPONDING AUTHOR MISSING]")
    funding = manifest.get("funding", "").strip() or "[LIVE-VERIFICATION: funding — user must verify]"
    conflicts = manifest.get("conflicts", "").strip() or "[LIVE-VERIFICATION: conflict of interest — user must verify]"
    data_line = _data_availability_line(manifest, inputs)
    code_line = ""
    if decl_req.get("code_availability"):
        code_status = manifest.get("code_availability_status", "")
        if code_status == "ready":
            code_line = "Code availability: ready"
        elif code_status == "not-applicable":
            code_line = "Code availability: not applicable"
        else:
            code_line = "[LIVE-VERIFICATION: code availability - verify if custom code was used]"
    today = _dt.date.today().isoformat()
    lines = [
        f"# Cover Letter — {journal_name}", "",
        today, "",
        "Editorial Office", journal_name, "",
        "Dear Editor,",
        "",
        f'We wish to submit our manuscript entitled "{title}" for consideration as a {article_label} in {journal_name}.',
        "",
        "[LLM: One paragraph summarizing the problem, approach, and key finding. "
        "Use the title, abstract, and journal triage points. Do not repeat detailed methods or results.]",
        "",
    ]
    if abstract:
        lines += ["Abstract (for LLM reference):", abstract, ""]
    points = template.get("cover_letter_required_points", [])
    if points:
        lines.append("Journal triage points (for LLM reference):")
        for p in points:
            lines.append(f"- {p}")
        lines.append("")
    lines += [
        f"We believe this work aligns with the scope of {journal_name} because "
        "[LLM: one sentence explaining the specific fit].",
        "",
    ]
    if any(decl_req.get(name) for name in ("funding", "conflict_of_interest", "data_availability", "code_availability")):
        lines.append("Declarations:")
    if decl_req.get("funding"):
        lines.append(f"- Funding: {funding}")
    if decl_req.get("conflict_of_interest"):
        lines.append(f"- Conflicts of interest: {conflicts}")
    if decl_req.get("data_availability"):
        lines.append(f"- {data_line}")
    if code_line:
        lines.append(f"- {code_line}")
    reviewers = get_suggested_reviewers(manifest)
    if reviewers:
        lines.append("- Suggested reviewers:")
        for r in reviewers:
            lines.append(f"  - {r}")
    else:
        lines.append("- Suggested reviewers: [omitted — supply real names only if available]")
    lines += [
        "",
        "Thank you for your consideration.",
        "",
        "Sincerely,",
        corresponding,
    ]
    return "\n".join(lines)


def render_highlights_inline(abstract: str, template: dict) -> str:
    rules = template.get("highlights_rules", {})
    max_count = rules.get("max_count", 5)
    max_chars = rules.get("max_characters_per_item", 85)
    lines = [
        "# Highlights", "",
        f"Target: {rules.get('min_count',3)}-{max_count} items, each ≤{max_chars} characters.", "",
        "[LLM: Extract highlights from the abstract below. Each highlight must be a single line ≤85 characters. Do not invent findings absent from the abstract.]",
        "",
        "Abstract:",
        abstract or "[no abstract supplied — ask user to fill manifest or writing state]",
        "",
        "Highlights:",
    ]
    for i in range(1, max_count + 1):
        lines.append(f"{i}. [LLM: highlight {i}]")
    return "\n".join(lines)


def render_checklist_inline(manifest: dict, template: dict) -> str:
    article_type = manifest.get("article_type", "research-article")
    at = find_article_type(template, article_type)
    lines = [
        f"# Submission Checklist - {template.get('full_name', template.get('journal_id'))}", "",
        f"Article type: {article_type_label(template, article_type)}",
        f"Word limit: {at.get('word_limit', 'verify')}",
        f"Abstract words: {at.get('abstract_words', 'verify')}" if at.get("abstract_required") is not False else "Abstract: not required",
        "",
        "## Mandatory items",
    ]
    append_required_field_items(lines, template, article_type)
    if template.get("highlights_required"):
        rules = template.get("highlights_rules", {})
        lines.append(f"- [ ] Highlights {rules.get('min_count',3)}-{rules.get('max_count',5)} items, ≤{rules.get('max_characters_per_item',85)} characters each")
    if field_is_required(template, article_type, "declarations"):
        lines += ["", "## Declarations"]
        append_declaration_checklist_items(lines, template)
    append_required_artifacts(lines, template)
    lines += ["", "## Cover letter"]
    for point in template.get("cover_letter_required_points", []):
        lines.append(f"- [ ] Cover letter states: {point}")
    lines += ["", "## Live-verification items"]
    for field in template.get("live_verification_fields", []):
        lines.append(f"- [LIVE-VERIFICATION: {field} — re-check against current Guide for Authors]")
    lines += ["", f"Official class: {template.get('official_class', 'verify')}",
              f"Submission portal: {template.get('submission_portal', 'verify')}"]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, help="path to submission-manifest.yaml")
    parser.add_argument("--output-dir", default="submission-package", help="output directory")
    parser.add_argument("--dry-run", action="store_true", help="validate without writing")
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest).resolve()
    if not manifest_path.exists():
        print(f"manifest not found: {manifest_path}", file=sys.stderr)
        return 1
    try:
        manifest = load_yaml(manifest_path)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    manifest, writing_state, inputs = prepare_submission_inputs(
        manifest,
        manifest_path.parent,
    )

    journal = manifest.get("target_journal", "")
    template = load_template(journal) if journal in SUPPORTED_JOURNALS else {}
    # Check refusal conditions (with template for article_type validation)
    reasons = check_refusal(manifest, template if template else None, inputs)
    if reasons:
        print("Refusal conditions met:", file=sys.stderr)
        for r in reasons:
            print(f"  - {r}", file=sys.stderr)
        print("Emitting dry-run only.", file=sys.stderr)
        if not args.dry_run:
            _remove_stale_handoff(Path(args.output_dir))
        args.dry_run = True

    abstract = manifest.get("abstract") or writing_state.get("abstract") or ""
    rows = read_weakness_routing(
        str(manifest.get("weakness_routing_path") or ""),
        manifest_path.parent,
    )
    gates = compute_gate_status(rows)

    if args.dry_run:
        print("=== DRY RUN ===")
        print(render_manifest_md(manifest, template, writing_state, gates, inputs))
        print("")
        print("Files that would be written:")
        article_type = manifest.get("article_type", "research-article")
        try:
            required_fields = set(required_fields_for_article_type(template, article_type))
        except KeyError:
            required_fields = set(template.get("required_fields") or [])
        files = ["MANIFEST.md", "submission-package.yaml", "cover-letter.md"]
        if template.get("highlights_required"):
            files.append("highlights.md")
        if "keywords" in required_fields:
            files.append("keywords.md")
        if "declarations" in required_fields:
            files.append("declarations.md")
        files += ["submission-checklist.md", "manuscript/SOURCE.md", "figures/SOURCE.md", "data/SOURCE.md", "reviewer-risk-regression.md"]
        for f in files:
            print(f"  {f}")
        return 0

    pkg_dir = Path(args.output_dir)
    written = write_package(
        pkg_dir,
        manifest,
        template,
        writing_state,
        gates,
        abstract,
        inputs,
        manifest_path,
    )
    print(f"wrote {len(written)} files to {pkg_dir}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
