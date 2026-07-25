#!/usr/bin/env python3
"""Validate materials-submission journal template pairs and schema."""

from __future__ import annotations

from pathlib import Path
import sys

import yaml

from template_support import JOURNAL_TEMPLATES

SKILL_DIR = Path(__file__).resolve().parents[1]
MANIFEST_PATH = SKILL_DIR / "manifest.yaml"
VALID_ARTIFACT_STAGES = {"initial-submission", "revision"}
VALID_ARTIFACT_REQUIREMENTS = {True, False, "conditional", "recommended"}
VALID_REQUIRED_FIELDS = {
    "title",
    "abstract",
    "keywords",
    "authors",
    "affiliations",
    "corresponding_author",
    "declarations",
}
VALID_DECLARATION_REQUIREMENT_KEYS = {
    "data_availability",
    "code_availability",
    "credit_author_statement",
    "conflict_of_interest",
    "funding",
    "ethics",
}
VALID_DECLARATION_REQUIREMENT_VALUES = {True, False, "conditional"}
UNSUPPORTED_RMPD_ALIASES = {
    "ijpe",
    "international journal of pavement engineering",
}


def load_yaml(path: Path) -> dict | None:
    try:
        with path.open(encoding="utf-8") as handle:
            value = yaml.safe_load(handle)
    except (OSError, yaml.YAMLError) as exc:
        return {"__error__": str(exc)}
    return value if isinstance(value, dict) else {}


def validate_template(path: Path, issues: list[str]) -> set[str]:
    template = load_yaml(path)
    if template is None:
        issues.append(f"{path.name}: empty YAML document")
        return set()
    if "__error__" in template:
        issues.append(f"{path.name}: YAML parse error: {template['__error__']}")
        return set()

    journal_id = template.get("journal_id")
    if journal_id != path.stem:
        issues.append(f"{path.name}: journal_id must equal {path.stem!r}")
    if not path.with_suffix(".md").is_file():
        issues.append(f"{path.name}: missing Markdown companion")

    required_fields_value = template.get("required_fields")
    if not isinstance(required_fields_value, list) or not required_fields_value:
        issues.append(f"{path.name}: required_fields must be a non-empty list")
        required_fields: set[str] = set()
    else:
        required_fields = set()
        for field in required_fields_value:
            if not isinstance(field, str) or field not in VALID_REQUIRED_FIELDS:
                issues.append(f"{path.name}: invalid required field {field!r}")
                continue
            if field in required_fields:
                issues.append(f"{path.name}: duplicate required field {field!r}")
            required_fields.add(field)

    declaration_requirements = template.get("declaration_requirements", {})
    if not isinstance(declaration_requirements, dict):
        issues.append(f"{path.name}: declaration_requirements must be a mapping")
    else:
        for declaration, requirement in declaration_requirements.items():
            if declaration not in VALID_DECLARATION_REQUIREMENT_KEYS:
                issues.append(f"{path.name}: invalid declaration requirement key {declaration!r}")
            elif requirement not in VALID_DECLARATION_REQUIREMENT_VALUES:
                issues.append(
                    f"{path.name}: invalid declaration requirement {declaration!r}={requirement!r}"
                )

    highlights_required = template.get("highlights_required")
    highlights_rules = template.get("highlights_rules")
    if not isinstance(highlights_required, bool):
        issues.append(f"{path.name}: highlights_required must be boolean")
    if not isinstance(highlights_rules, dict):
        issues.append(f"{path.name}: highlights_rules must be a mapping")
    else:
        min_count = highlights_rules.get("min_count")
        max_count = highlights_rules.get("max_count")
        max_characters = highlights_rules.get("max_characters_per_item")
        if not all(isinstance(value, int) for value in (min_count, max_count, max_characters)):
            issues.append(f"{path.name}: highlights rules must use integer limits")
        elif highlights_required:
            if min_count < 1 or max_count < min_count or max_characters < 1:
                issues.append(f"{path.name}: required highlights need positive ordered limits")
        elif any(value != 0 for value in (min_count, max_count, max_characters)):
            issues.append(f"{path.name}: disabled highlights must use zero limits")

    article_type_ids: set[str] = set()
    article_types = template.get("article_types")
    if not isinstance(article_types, list) or not article_types:
        issues.append(f"{path.name}: article_types must be a non-empty list")
    else:
        for entry in article_types:
            article_type = entry.get("id") if isinstance(entry, dict) else None
            if not isinstance(article_type, str) or not article_type:
                issues.append(f"{path.name}: article type missing id")
            elif article_type in article_type_ids:
                issues.append(f"{path.name}: duplicate article type {article_type!r}")
            else:
                article_type_ids.add(article_type)
            if not isinstance(entry, dict):
                continue
            excluded_fields = entry.get("required_fields_exclude", [])
            if not isinstance(excluded_fields, list) or not all(isinstance(field, str) for field in excluded_fields):
                issues.append(f"{path.name}: article type {article_type!r} required_fields_exclude must be a list of strings")
                continue
            for field in excluded_fields:
                if field not in required_fields:
                    issues.append(f"{path.name}: article type {article_type!r} excludes non-required field {field!r}")
            if entry.get("abstract_required") is False and "abstract" in required_fields and "abstract" not in excluded_fields:
                issues.append(
                    f"{path.name}: article type {article_type!r} disables abstract but does not exclude it from required_fields"
                )

    structures = {
        entry.get("abstract_structure")
        for entry in article_types or []
        if isinstance(entry, dict) and entry.get("abstract_required") is not False
    }
    if "structured_abstract" in required_fields and "unstructured" in structures:
        issues.append(f"{path.name}: structured_abstract conflicts with unstructured article type")
    if "unstructured_abstract" in required_fields and "structured" in structures:
        issues.append(f"{path.name}: unstructured_abstract conflicts with structured article type")

    artifacts = template.get("required_artifacts", [])
    if artifacts is not None and not isinstance(artifacts, list):
        issues.append(f"{path.name}: required_artifacts must be a list")
    elif isinstance(artifacts, list):
        artifact_ids: set[str] = set()
        for artifact in artifacts:
            if not isinstance(artifact, dict):
                issues.append(f"{path.name}: required_artifacts entries must be mappings")
                continue
            artifact_id = artifact.get("id")
            if not isinstance(artifact_id, str) or not artifact_id:
                issues.append(f"{path.name}: artifact missing id")
            elif artifact_id in artifact_ids:
                issues.append(f"{path.name}: duplicate artifact {artifact_id!r}")
            else:
                artifact_ids.add(artifact_id)
            if not isinstance(artifact.get("label"), str) or not artifact["label"].strip():
                issues.append(f"{path.name}: artifact {artifact_id!r} missing label")
            if artifact.get("stage") not in VALID_ARTIFACT_STAGES:
                issues.append(f"{path.name}: artifact {artifact_id!r} has invalid stage")
            if artifact.get("required", True) not in VALID_ARTIFACT_REQUIREMENTS:
                issues.append(f"{path.name}: artifact {artifact_id!r} has invalid required value")
    return article_type_ids


def validate_manifest_article_routes(article_type_ids: set[str], issues: list[str]) -> None:
    manifest = load_yaml(MANIFEST_PATH)
    if manifest is None or "__error__" in manifest:
        issues.append("materials-submission manifest could not be parsed")
        return
    routes = (
        manifest.get("axes", {})
        .get("article_type", {})
        .get("values", {})
    )
    if not isinstance(routes, dict):
        issues.append("materials-submission manifest article_type routes must be a mapping")
        return
    for article_type in routes:
        if article_type not in article_type_ids:
            issues.append(f"manifest article type has no journal support: {article_type}")


def validate_manifest_journal_routes(issues: list[str]) -> None:
    """Reject aliases that would route IJPE to the RMPD-only template."""
    manifest = load_yaml(MANIFEST_PATH)
    if manifest is None or "__error__" in manifest:
        issues.append("materials-submission manifest could not be parsed")
        return
    journal_values = (
        manifest.get("axes", {})
        .get("journal", {})
        .get("values", {})
    )
    if not isinstance(journal_values, dict):
        issues.append("materials-submission manifest journal routes must be a mapping")
        return
    rmpd_route = journal_values.get("rmpd", {})
    rmpd_triggers = rmpd_route.get("triggers", []) if isinstance(rmpd_route, dict) else []
    if not isinstance(rmpd_triggers, list):
        issues.append("materials-submission rmpd triggers must be a list")
    elif any(
        isinstance(trigger, str) and trigger.strip().casefold() in UNSUPPORTED_RMPD_ALIASES
        for trigger in rmpd_triggers
    ):
        issues.append("materials-submission rmpd route includes IJPE aliases without an IJPE template")

    references = manifest.get("references", {}).get("on_demand", {})
    rmpd_facts = references.get("journal-rmpd-facts", {}) if isinstance(references, dict) else {}
    when = rmpd_facts.get("when", "") if isinstance(rmpd_facts, dict) else ""
    if isinstance(when, str) and any(alias in when.casefold() for alias in UNSUPPORTED_RMPD_ALIASES):
        issues.append("materials-submission rmpd facts reference IJPE without an IJPE template")


def validate_templates() -> list[str]:
    """Return all journal-template structural and routing issues."""
    issues: list[str] = []
    all_article_type_ids: set[str] = set()
    yaml_paths = sorted(JOURNAL_TEMPLATES.glob("*.yaml"))
    for path in yaml_paths:
        all_article_type_ids.update(validate_template(path, issues))
    for path in sorted(JOURNAL_TEMPLATES.glob("*.md")):
        if not path.with_suffix(".yaml").is_file():
            issues.append(f"{path.name}: missing YAML companion")
    validate_manifest_article_routes(all_article_type_ids, issues)
    validate_manifest_journal_routes(issues)
    return issues


def main() -> int:
    issues = validate_templates()
    if issues:
        for issue in issues:
            print(f"FAIL: {issue}", file=sys.stderr)
        return 1
    print("PASS: journal templates valid")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
