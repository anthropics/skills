"""Shared helpers for materials-submission journal templates."""

from __future__ import annotations

from pathlib import Path

import yaml

PLUGIN_ROOT = Path(__file__).resolve().parents[3]
JOURNAL_TEMPLATES = PLUGIN_ROOT / "_shared" / "journal-templates"


def supported_journals() -> tuple[str, ...]:
    """Return journal IDs declared by YAML templates."""
    return tuple(sorted(path.stem for path in JOURNAL_TEMPLATES.glob("*.yaml")))


SUPPORTED_JOURNALS = supported_journals()

CHECKLIST_FIELD_LABELS = {
    "title": "Title",
    "authors": "Authors",
    "affiliations": "Affiliations",
    "corresponding_author": "Corresponding author",
    "keywords": "Keywords (3-6)",
}

DECLARATION_CHECKLIST_ITEMS = (
    ("data_availability", "Data availability statement", None),
    ("code_availability", "Code availability statement", "if custom code used"),
    ("credit_author_statement", "CRediT author statement", None),
    ("conflict_of_interest", "Declaration of competing interest", None),
    ("funding", "Funding statement", None),
    ("ethics", "Ethics statement", "if applicable"),
)


def load_template(journal_id: str) -> dict:
    """Load one journal template or raise a clear missing-template error."""
    path = JOURNAL_TEMPLATES / f"{journal_id}.yaml"
    if not path.exists():
        raise FileNotFoundError(f"journal template not found: {path}")
    with path.open(encoding="utf-8") as handle:
        return yaml.safe_load(handle) or {}


def find_article_type(template: dict, article_type: str) -> dict:
    """Return one article-type declaration from a journal template."""
    for entry in template.get("article_types", []):
        if entry.get("id") == article_type:
            return entry
    journal = template.get("journal_id", "journal")
    raise KeyError(f"article_type {article_type!r} not in {journal} template")


def article_type_label(template: dict, article_type: str) -> str:
    """Return the publisher-facing article-type label."""
    entry = find_article_type(template, article_type)
    return str(entry.get("submission_label") or article_type)


def required_fields_for_article_type(template: dict, article_type: str) -> tuple[str, ...]:
    """Resolve journal-level required fields after article-type exclusions."""
    article = find_article_type(template, article_type)
    required_fields = template.get("required_fields") or []
    excluded_fields = set(article.get("required_fields_exclude") or [])
    return tuple(field for field in required_fields if field not in excluded_fields)


def field_is_required(template: dict, article_type: str, field: str) -> bool:
    """Return whether a field is required for one journal article type."""
    return field in required_fields_for_article_type(template, article_type)


def abstract_checklist_item(article_type: dict) -> str:
    """Render an article-type-specific abstract checklist item."""
    if article_type.get("abstract_required") is False:
        return "- [ ] No abstract required for this article type"
    structure = article_type.get("abstract_structure", "unstructured")
    words = article_type.get("abstract_words", "verify")
    if isinstance(words, str) and words.startswith("verify"):
        return f"- [ ] {structure} abstract word limit [LIVE-VERIFICATION: {words}]"
    return f"- [ ] {structure} abstract within {words} words"


def append_required_field_items(lines: list[str], template: dict, article_type: str) -> None:
    """Append mandatory manuscript-field checklist entries from a template."""
    article = find_article_type(template, article_type)
    required_fields = required_fields_for_article_type(template, article_type)
    for field in required_fields:
        if field == "abstract":
            lines.append(abstract_checklist_item(article))
        elif field == "declarations":
            continue
        else:
            label = CHECKLIST_FIELD_LABELS.get(field, field.replace("_", " ").title())
            lines.append(f"- [ ] {label}")
    if article.get("abstract_required") is False and "abstract" not in required_fields:
        lines.append(abstract_checklist_item(article))


def declaration_is_enabled(template: dict, declaration: str) -> bool:
    """Return whether a declaration applies, including conditional declarations."""
    return bool(template.get("declaration_requirements", {}).get(declaration))


def append_declaration_checklist_items(lines: list[str], template: dict) -> None:
    """Append declaration checklist entries that the template enables."""
    for declaration, label, conditional_suffix in DECLARATION_CHECKLIST_ITEMS:
        if not declaration_is_enabled(template, declaration):
            continue
        suffix = f" ({conditional_suffix})" if conditional_suffix else ""
        lines.append(f"- [ ] {label}{suffix}")


def append_required_artifacts(lines: list[str], template: dict) -> None:
    """Append stage-specific required or recommended artifacts to checklist lines."""
    artifacts = template.get("required_artifacts", [])
    if not artifacts:
        return

    headings = (
        ("initial-submission", "Required submission artifacts"),
        ("revision", "Required at revision"),
    )
    for stage, heading in headings:
        stage_artifacts = [item for item in artifacts if item.get("stage") == stage]
        if not stage_artifacts:
            continue
        lines.extend(["", f"## {heading}"])
        for item in stage_artifacts:
            requirement = item.get("required", True)
            suffix = ""
            if requirement == "conditional":
                suffix = " (if applicable)"
            elif requirement == "recommended":
                suffix = " (recommended)"
            lines.append(f"- [ ] {item.get('label', item.get('id', 'artifact'))}{suffix}")
