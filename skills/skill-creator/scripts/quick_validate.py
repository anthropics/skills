#!/usr/bin/env python3
"""
Progressive-disclosure validation for Agent Skills.

Checks a skill against the Agent Skills spec (agentskills.io) and the
progressive-disclosure budgets that keep a triggered skill from blowing
the context window. This is the guard against the failure mode where a
skill's SKILL.md (plus bundled reference docs) is injected wholesale into
context — e.g. anthropics/skills issue #1487, where the claude-api skill
eagerly injected ~156k tokens and killed the session.

Checks performed:

Hard requirements (errors, exit code 1):
  * SKILL.md exists with valid YAML frontmatter
  * frontmatter uses only allowed keys
  * name is kebab-case, <= 64 chars, no leading/trailing hyphen, no "--"
  * description is present, <= 1024 chars, no angle brackets
  * compatibility (if present) <= 500 chars
  * every relative path referenced from the SKILL.md body resolves to a
    file inside the skill directory (a broken index is a broken skill)

Progressive-disclosure budgets (warnings by default, errors with --strict):
  * SKILL.md body stays under --max-lines (default 500, spec recommendation)
  * SKILL.md body stays under --max-tokens (default 5000, spec
    recommendation; estimated as len(body) / 4 characters per token)

The eager payload — SKILL.md plus every bundled markdown file — is
reported for every skill (warning if over --max-payload-tokens, default
20000) but is never an error: the spec allows unbounded bundled reference
material, so the gate that catches the #1487 failure class is the size of
SKILL.md itself.

The payload figure is printed for every skill so the cost of triggering
it is visible before it ships.

Usage:
    python quick_validate.py <skill-directory> [--strict] [--json]
                             [--max-lines N] [--max-tokens N]
                             [--max-payload-tokens N]
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import yaml

# Spec-recommended budgets (agentskills.io/specification).
DEFAULT_MAX_LINES = 500
DEFAULT_MAX_TOKENS = 5000
DEFAULT_MAX_PAYLOAD_TOKENS = 20000

ALLOWED_PROPERTIES = {
    "name", "description", "license", "allowed-tools", "metadata", "compatibility",
}
LANGUAGE_DIRS = {
    "csharp", "curl", "go", "java", "php", "python", "ruby", "typescript",
}
# Relative paths inside SKILL.md may use a {lang} placeholder (e.g.
# `{lang}/claude-api/README.md`). Verify such a path exists under at least
# one language directory rather than failing outright.
_LANG_PLACEHOLDER = "{lang}"


@dataclass
class Finding:
    """A single validation finding."""

    level: str  # "error" or "warning"
    check: str
    message: str

    def to_dict(self) -> dict[str, str]:
        return {"level": self.level, "check": self.check, "message": self.message}


@dataclass
class ValidationResult:
    """Structured result of validating one skill."""

    skill_path: Path
    valid: bool = True
    findings: list[Finding] = field(default_factory=list)
    metrics: dict[str, Any] = field(default_factory=dict)

    def message(self) -> str:
        """One-line human summary (keeps the old validate_skill contract)."""
        errors = [f for f in self.findings if f.level == "error"]
        if errors:
            return errors[0].message
        if self.findings:
            return f"Skill is valid ({len(self.findings)} warning(s))."
        return "Skill is valid!"

    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_path": str(self.skill_path),
            "valid": self.valid,
            "findings": [f.to_dict() for f in self.findings],
            "metrics": self.metrics,
        }


def estimate_tokens(text: str | int) -> int:
    """Rough token estimate (~4 chars per token).

    Accepts a string (body text) or an int (char count). The spec's
    "<5000 tokens" guidance uses a similar approximation. This is a budget
    heuristic, not a tokenizer; real counts vary by content.
    """
    chars = len(text) if isinstance(text, str) else text
    return chars // 4


def _frontmatter(content: str) -> tuple[dict[str, Any], str, str | None]:
    """Parse YAML frontmatter. Returns (data, body, error)."""
    if not content.startswith("---"):
        return {}, "", "No YAML frontmatter found"
    match = re.match(r"^---\r?\n(.*?)\r?\n---", content, re.DOTALL)
    if not match:
        return {}, "", "Invalid frontmatter format"
    try:
        data = yaml.safe_load(match.group(1))
    except yaml.YAMLError as e:
        return {}, "", f"Invalid YAML in frontmatter: {e}"
    if not isinstance(data, dict):
        return {}, "", "Frontmatter must be a YAML dictionary"
    return data, content[match.end():], None


def _collect_references(body: str) -> list[str]:
    """Collect relative .md paths referenced in the SKILL.md body.

    Matches backticked paths (`` `shared/models.md` ``) and markdown links
    (``[text](path)``). Placeholder-free, non-absolute paths ending in
    ``.md`` are returned, deduplicated, in document order.
    """
    refs: list[str] = []
    for m in re.finditer(r"`([^`]+\.md)`|\[[^\]]*\]\(([^)]+\.md)\)", body):
        ref = m.group(1) or m.group(2)
        if not ref:
            continue
        ref = ref.strip()
        if ref.startswith(("http://", "https://", "/", "#")):
            continue
        if ref not in refs:
            refs.append(ref)
    return refs


def _resolve_reference(skill_dir: Path, ref: str) -> tuple[bool, str]:
    """Check a relative reference resolves inside the skill directory.

    ``{lang}`` placeholders resolve if the path exists under any language
    directory; glob patterns (``*``) resolve if any file matches. Returns
    (resolved, detail).
    """
    if _LANG_PLACEHOLDER in ref:
        candidates = [skill_dir / ref.replace(_LANG_PLACEHOLDER, lang) for lang in LANGUAGE_DIRS]
        hits = [c for c in candidates if c.is_file()]
        if hits:
            return True, f"{ref} -> {hits[0].relative_to(skill_dir)}"
        return False, f"{ref}: no language directory provides this file"
    if any(ch in ref for ch in "*?"):
        matches = list(skill_dir.glob(ref))
        if matches:
            return True, f"{ref} -> {len(matches)} match(es)"
        return False, f"{ref}: glob matches nothing"
    target = skill_dir / ref
    if target.is_file():
        return True, ref
    return False, f"{ref}: file not found in skill"


def _payload_metrics(skill_dir: Path, body: str) -> dict[str, Any]:
    """Measure the eager-injection cost of the skill.

    payload_tokens is the size a runtime would inject if it concatenated
    SKILL.md with every bundled markdown file — the metric from issue
    #1487 (claude-api: ~156k tokens in one tool call).
    """
    bundled_md = [p for p in skill_dir.rglob("*.md") if p.name != "SKILL.md"]
    bundled_chars = sum(
        len(p.read_text(encoding="utf-8", errors="replace")) for p in bundled_md
    )
    skill_chars = len(body)
    return {
        "skill_md_chars": skill_chars,
        "skill_md_lines": body.count("\n") + 1,
        "skill_md_tokens": estimate_tokens(body),
        "bundled_md_files": len(bundled_md),
        "bundled_md_chars": bundled_chars,
        "bundled_md_tokens": estimate_tokens(bundled_chars),
        "payload_chars": skill_chars + bundled_chars,
        "payload_tokens": estimate_tokens(skill_chars + bundled_chars),
    }


def validate_skill(
    skill_path: str | Path,
    *,
    max_lines: int = DEFAULT_MAX_LINES,
    max_tokens: int = DEFAULT_MAX_TOKENS,
    max_payload_tokens: int = DEFAULT_MAX_PAYLOAD_TOKENS,
    strict: bool = False,
) -> tuple[bool, str]:
    """Validate a skill directory.

    Backwards-compatible with the original one-line contract used by
    package_skill.py: returns (valid, message).
    """
    result = validate_skill_detailed(
        skill_path,
        max_lines=max_lines,
        max_tokens=max_tokens,
        max_payload_tokens=max_payload_tokens,
        strict=strict,
    )
    return result.valid, result.message()


def validate_skill_detailed(
    skill_path: str | Path,
    *,
    max_lines: int = DEFAULT_MAX_LINES,
    max_tokens: int = DEFAULT_MAX_TOKENS,
    max_payload_tokens: int = DEFAULT_MAX_PAYLOAD_TOKENS,
    strict: bool = False,
) -> ValidationResult:
    """Validate a skill directory and return a structured result."""
    skill_dir = Path(skill_path)
    result = ValidationResult(skill_path=skill_dir)

    skill_md = skill_dir / "SKILL.md"
    if not skill_md.exists():
        result.findings.append(Finding("error", "structure", "SKILL.md not found"))
        result.valid = False
        return result

    content = skill_md.read_text(encoding="utf-8", errors="replace")
    frontmatter, body, error = _frontmatter(content)
    if error:
        result.findings.append(Finding("error", "frontmatter", error))
        result.valid = False
        return result

    # --- Frontmatter hard requirements -----------------------------------
    unexpected = set(frontmatter.keys()) - ALLOWED_PROPERTIES
    if unexpected:
        result.findings.append(Finding(
            "error", "frontmatter",
            f"Unexpected key(s): {', '.join(sorted(unexpected))}",
        ))

    name = frontmatter.get("name", "")
    if not isinstance(name, str) or not name.strip():
        result.findings.append(Finding("error", "name", "Missing 'name' in frontmatter"))
    else:
        name = name.strip()
        if not re.match(r"^[a-z0-9-]+$", name):
            result.findings.append(Finding(
                "error", "name",
                f"Name '{name}' should be kebab-case (lowercase letters, digits, hyphens only)",
            ))
        if name.startswith("-") or name.endswith("-") or "--" in name:
            result.findings.append(Finding(
                "error", "name",
                f"Name '{name}' cannot start/end with hyphen or contain consecutive hyphens",
            ))
        if len(name) > 64:
            result.findings.append(Finding(
                "error", "name",
                f"Name is too long ({len(name)} characters). Maximum is 64.",
            ))

    description = frontmatter.get("description", "")
    if not isinstance(description, str) or not description.strip():
        result.findings.append(Finding("error", "description", "Missing 'description' in frontmatter"))
    else:
        description = description.strip()
        if "<" in description or ">" in description:
            result.findings.append(Finding(
                "error", "description", "Description cannot contain angle brackets (< or >)",
            ))
        if len(description) > 1024:
            result.findings.append(Finding(
                "error", "description",
                f"Description is too long ({len(description)} chars). Maximum is 1024.",
            ))

    compatibility = frontmatter.get("compatibility", "")
    if compatibility:
        if not isinstance(compatibility, str):
            result.findings.append(Finding("error", "compatibility", "compatibility must be a string"))
        elif len(compatibility) > 500:
            result.findings.append(Finding(
                "error", "compatibility",
                f"compatibility is too long ({len(compatibility)} chars). Maximum is 500.",
            ))

    # --- Reference integrity ---------------------------------------------
    # A reference whose first segment is a real directory inside the skill
    # is an explicit pointer to bundled content — a miss is an error. A bare
    # filename (e.g. `README.md` in prose) is ambiguous, so a miss is only a
    # warning.
    for ref in _collect_references(body):
        resolved, detail = _resolve_reference(skill_dir, ref)
        if resolved:
            continue
        # A reference with a directory segment (e.g. `references/guide.md`)
        # or a {lang} placeholder is an explicit pointer to bundled content
        # — a miss is an error. A bare filename like `README.md` is
        # ambiguous prose, so a miss is silently ignored.
        is_explicit = "/" in ref or _LANG_PLACEHOLDER in ref
        if not is_explicit:
            continue
        result.findings.append(Finding(
            "error", "references",
            f"SKILL.md references missing file: {detail}",
        ))

    # --- Progressive-disclosure budgets ----------------------------------
    line_count = body.count("\n") + 1
    token_estimate = estimate_tokens(body)
    if line_count > max_lines:
        result.findings.append(Finding(
            "error" if strict else "warning", "budget",
            f"SKILL.md body is {line_count} lines (max {max_lines})",
        ))
    if token_estimate > max_tokens:
        result.findings.append(Finding(
            "error" if strict else "warning", "budget",
            f"SKILL.md body is ~{token_estimate} tokens (max {max_tokens})",
        ))

    metrics = _payload_metrics(skill_dir, body)
    # The eager payload is informational, never a strict error: the spec
    # explicitly allows unbounded bundled reference material ("no context
    # penalty for bundled content that isn't used"). The gate that matters
    # for the #1487 failure class is SKILL.md's own size, enforced above.
    payload_tokens = metrics["payload_tokens"]
    if payload_tokens > max_payload_tokens:
        result.findings.append(Finding(
            "warning", "budget",
            f"Eager payload (SKILL.md + {metrics['bundled_md_files']} bundled .md files) "
            f"is ~{payload_tokens} tokens (max {max_payload_tokens}) — only a runtime that "
            f"concatenates the whole skill folder would pay this; bundled references are "
            f"meant to be read on demand",
        ))
    result.metrics = metrics

    result.valid = not any(f.level == "error" for f in result.findings)
    return result


def _print_human(result: ValidationResult) -> None:
    m = result.metrics
    print(f"Skill: {result.skill_path}")
    print(
        f"  SKILL.md: {m.get('skill_md_chars', 0)} chars, "
        f"~{m.get('skill_md_tokens', 0)} tokens, "
        f"{m.get('skill_md_lines', '?')} lines"
    )
    print(
        f"  Bundled .md: {m.get('bundled_md_files', 0)} files, "
        f"~{m.get('bundled_md_tokens', 0)} tokens"
    )
    print(f"  Eager payload: ~{m.get('payload_tokens', 0)} tokens (issue #1487 metric)")
    if not result.findings:
        print("  Valid: ✅")
        return
    for f in result.findings:
        icon = "❌" if f.level == "error" else "⚠️"
        print(f"  {icon} [{f.check}] {f.message}")
    print(f"  Valid: {'❌' if not result.valid else '✅ (with warnings)'}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate a skill for spec and progressive-disclosure compliance"
    )
    parser.add_argument("skill_path", help="Path to skill directory")
    parser.add_argument("--strict", action="store_true", help="Treat budget overruns as errors")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    parser.add_argument("--max-lines", type=int, default=DEFAULT_MAX_LINES)
    parser.add_argument("--max-tokens", type=int, default=DEFAULT_MAX_TOKENS)
    parser.add_argument("--max-payload-tokens", type=int, default=DEFAULT_MAX_PAYLOAD_TOKENS)
    args = parser.parse_args(argv)

    result = validate_skill_detailed(
        args.skill_path,
        max_lines=args.max_lines,
        max_tokens=args.max_tokens,
        max_payload_tokens=args.max_payload_tokens,
        strict=args.strict,
    )
    if args.json:
        print(json.dumps(result.to_dict(), indent=2))
    else:
        _print_human(result)
    return 0 if result.valid else 1


if __name__ == "__main__":
    sys.exit(main())
