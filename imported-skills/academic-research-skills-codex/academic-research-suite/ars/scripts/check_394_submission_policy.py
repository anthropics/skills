#!/usr/bin/env python3
"""#394 slice-4 submission-package terminality lint.

Runs alongside the other policy lints (check_v3_10_policy.py pattern).
Verifies the slice-4 contract across the terminal-policies schema, the
orchestrator prompt, the formatter prompt, the verifier script, and the
report schema. Spec: docs/design/2026-06-10-394-submission-package-verifier-
spec.md §5.2/§5.3/§7.

Invariants (plan D5, post-gate-1):
  1. terminal_policies.schema.json `submission_package` enum is EXACTLY
     {advisory, strict} and carries no JSON-Schema `default` (the absent-key
     default is an evaluator runtime convention — a schema default would be
     non-operational false comfort, the Invariant-3 lesson).
  2. The orchestrator's Submission-Package Terminal Gate section exists and
     carries the load-bearing literals: the fix-loop bound ("bounded: 2 fix
     rounds"), VERIFICATION-INCOMPLETE, --check-freshness, the sole-reader
     sentence, and the gate-on-tokens-not-exit-codes sentence.
  3. The formatter carries the Submission Package Advisories section with its
     emptiness contract ("mandatory and non-empty iff") and the stamp-only
     boundary (Invariant 13 stays cited in the section).
  4. AST single-homed guard (§5.3): verify_submission_package.py contains NO
     runtime ACCESS of the "terminal_policies" key — no Subscript
     x["terminal_policies"] and no .get("terminal_policies") anywhere in the
     module. Docstrings / comments / help text may mention the word freely
     (a literal grep would die on the module docstring — gate-1 P2).
  5. The report schema's policy_slug is the closed enum
     {null, advisory, strict} — exactly the values the CLI stamps — and its
     description documents the null-never-fresh semantics.
"""
from __future__ import annotations

import ast
import json
import sys
from pathlib import Path

if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from _skill_lint import check_section_literals

REPO_ROOT = Path(__file__).resolve().parent.parent
TP_SCHEMA = REPO_ROOT / "shared/contracts/passport/terminal_policies.schema.json"
REPORT_SCHEMA = (
    REPO_ROOT / "shared/contracts/submission/"
    "submission_verification_report.schema.json"
)
ORCHESTRATOR = (
    REPO_ROOT / "academic-pipeline/agents/pipeline_orchestrator_agent.md"
)
FORMATTER = REPO_ROOT / "academic-paper/agents/formatter_agent.md"
VERIFIER = REPO_ROOT / "scripts/verify_submission_package.py"

ORCH_HEADING = "## Submission-Package Terminal Gate"
FMT_HEADING = "## Submission Package Advisories"


def check_tp_schema(schema: dict) -> list[str]:
    """Invariant 1."""
    fails: list[str] = []
    sp = schema.get("properties", {}).get("submission_package")
    if sp is None:
        return ["invariant 1: terminal_policies schema has no "
                "submission_package key"]
    if set(sp.get("enum", [])) != {"advisory", "strict"}:
        fails.append(
            "invariant 1: submission_package enum is "
            f"{sp.get('enum')!r}, expected exactly ['advisory', 'strict']")
    if "default" in sp:
        fails.append(
            "invariant 1: submission_package MUST NOT carry a JSON-Schema "
            "`default` (absent-key advisory is an evaluator runtime "
            "convention; a schema default is non-operational)")
    return fails


def check_orchestrator(text: str) -> list[str]:
    """Invariant 2."""
    return check_section_literals(2, text, ORCH_HEADING,
                                   "orchestrator gate", {
        "fix-loop bound": "bounded: 2 fix rounds",
        "fail-closed verdict": "VERIFICATION-INCOMPLETE",
        "freshness guard": "--check-freshness",
        "sole-reader sentence":
            "SOLE reader of `terminal_policies.submission_package`",
        "token-not-exit-code sentence":
            "Gate on stdout tokens, NEVER on exit codes",
        "recompute discipline": "Recompute each pass",
    })


def check_formatter(text: str) -> list[str]:
    """Invariant 3."""
    return check_section_literals(3, text, FMT_HEADING,
                                   "formatter advisories", {
        "emptiness contract": "mandatory and non-empty iff",
        "stamp-only boundary": "Invariant 13",
        "not_applicable exclusion": "`not_applicable` rows",
    })


def find_terminal_policies_access(source: str) -> list[str]:
    """Invariant 4 core: return descriptions of every runtime ACCESS of the
    'terminal_policies' key — a Subscript x["terminal_policies"] or a
    .get("terminal_policies", ...) call. Mentions in docstrings, comments, or
    help text never match (this is the AST replacement for the dead-on-
    arrival literal grep, gate-1 P2)."""
    hits: list[str] = []
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, ast.Subscript):
            sl = node.slice
            if isinstance(sl, ast.Constant) and sl.value == "terminal_policies":
                hits.append(f"Subscript access at line {node.lineno}")
        elif (isinstance(node, ast.Call)
              and isinstance(node.func, ast.Attribute)
              and node.func.attr == "get"
              and node.args
              and isinstance(node.args[0], ast.Constant)
              and node.args[0].value == "terminal_policies"):
            hits.append(f".get() access at line {node.lineno}")
    return hits


def check_verifier_single_homed(source: str) -> list[str]:
    """Invariant 4."""
    return [
        f"invariant 4: verify_submission_package.py reads the "
        f"terminal_policies key ({hit}) — the script must stay single-homed "
        f"(§5.3: the orchestrator is the only policy reader)"
        for hit in find_terminal_policies_access(source)
    ]


def check_report_schema(schema: dict) -> list[str]:
    """Invariant 5."""
    fails: list[str] = []
    slug = (schema.get("properties", {}).get("header", {})
            .get("properties", {}).get("policy_slug"))
    if slug is None:
        return ["invariant 5: report schema has no header.policy_slug"]
    # Direct value comparison — None must be JSON null, not the string
    # "None" (a str() mapping would let the two collide; final-round P3).
    if set(slug.get("enum", [])) != {None, "advisory", "strict"}:
        fails.append(
            f"invariant 5: policy_slug enum is {slug.get('enum')!r}, "
            "expected exactly [null, 'advisory', 'strict'] — the closed set "
            "of values the CLI stamps")
    desc = slug.get("description", "")
    if "null" not in desc or "freshness" not in desc:
        fails.append(
            "invariant 5: policy_slug description must document the "
            "null-stamped-never-fresh semantics")
    return fails


def main() -> int:
    failures: list[str] = []
    failures += check_tp_schema(
        json.loads(TP_SCHEMA.read_text(encoding="utf-8")))
    failures += check_orchestrator(ORCHESTRATOR.read_text(encoding="utf-8"))
    failures += check_formatter(FORMATTER.read_text(encoding="utf-8"))
    failures += check_verifier_single_homed(
        VERIFIER.read_text(encoding="utf-8"))
    failures += check_report_schema(
        json.loads(REPORT_SCHEMA.read_text(encoding="utf-8")))
    if failures:
        print("#394 slice-4 submission-policy lint FAILED:")
        for f in failures:
            print(f"- {f}")
        return 1
    print("#394 slice-4 submission-policy lint OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
