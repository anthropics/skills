#!/usr/bin/env python3
"""
Mermaid diagram validator (pure standard library, no dependencies).

Performs lightweight static checks on Mermaid source so common mistakes are
caught *before* attempting to render. This is intentionally a linter, not a full
parser: it favors actionable warnings over strict spec compliance.

Usage:
    python3 validate.py diagram.mmd
    python3 validate.py diagram.mmd --json
    cat diagram.mmd | python3 validate.py -

Exit codes:
    0  no errors (warnings may still be printed)
    1  one or more errors found
    2  usage / file error
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from typing import List

# Diagram-type keywords that may legally start a Mermaid definition.
# A leading "%%{ ... }%%" init directive or "---" front-matter block is allowed
# before these; that is handled in _find_diagram_type().
DIAGRAM_TYPES = {
    "graph": "flowchart",
    "flowchart": "flowchart",
    "sequenceDiagram": "sequence",
    "classDiagram": "class",
    "stateDiagram": "state",
    "stateDiagram-v2": "state",
    "erDiagram": "entity-relationship",
    "journey": "user-journey",
    "gantt": "gantt",
    "pie": "pie",
    "mindmap": "mindmap",
    "timeline": "timeline",
    "quadrantChart": "quadrant",
    "gitGraph": "git-graph",
    "C4Context": "c4",
    "sankey-beta": "sankey",
    "xychart-beta": "xychart",
    "block-beta": "block",
    "requirementDiagram": "requirement",
}

# Valid flowchart orientations after "graph"/"flowchart".
FLOWCHART_DIRECTIONS = {"TB", "TD", "BT", "RL", "LR"}


@dataclass
class Issue:
    severity: str          # "error" | "warning"
    line: int              # 1-based; 0 == file-level
    message: str
    hint: str = ""


@dataclass
class Report:
    ok: bool = True
    diagram_type: str = "unknown"
    issues: List[Issue] = field(default_factory=list)

    def add(self, severity, line, message, hint=""):
        self.issues.append(Issue(severity, line, message, hint))
        if severity == "error":
            self.ok = False


def _strip_comments(line: str) -> str:
    """Remove Mermaid line comments (%% ...) but keep init directives intact."""
    if line.lstrip().startswith("%%{"):
        return line  # init directive, not a comment
    idx = line.find("%%")
    return line[:idx] if idx != -1 else line


def _find_diagram_type(lines: List[str]) -> (str, int):
    """Return (diagram_type, line_index) of the first declaration line."""
    in_frontmatter = False
    for i, raw in enumerate(lines):
        stripped = raw.strip()
        if not stripped:
            continue
        # YAML front-matter block delimited by --- ... ---
        if stripped == "---":
            in_frontmatter = not in_frontmatter
            continue
        if in_frontmatter:
            continue
        # Skip init directives like %%{init: {...}}%%
        if stripped.startswith("%%{") and stripped.endswith("}%%"):
            continue
        if stripped.startswith("%%"):
            continue
        first_token = stripped.split()[0]
        for kw, kind in DIAGRAM_TYPES.items():
            if first_token == kw or stripped.startswith(kw):
                return kind, i
        return "unknown", i
    return "unknown", -1


# In erDiagram, "{" / "}" appear inside cardinality glyphs such as "||--o{",
# "}o--||", "|{", "}|" — there they are notation, not brackets. We strip the
# relationship glyphs before counting so the balance check does not false-positive.
def _check_balanced(text: str, report: Report, diagram_type: str = ""):
    """Check bracket / parenthesis / quote balance across the whole document."""
    pairs = {")": "(", "]": "[", "}": "{"}
    openers = set(pairs.values())
    stack = []
    in_quote = False
    lines = text.splitlines()

    for raw in lines:
        line = raw
        # For ER relationship lines, remove cardinality braces around "--".
        if diagram_type == "entity-relationship" and "--" in line:
            line = re.sub(r"[|o}{]+--[|o}{]+", "--", line)
        for ch in line:
            if ch == '"':
                in_quote = not in_quote
                continue
            if in_quote:
                continue
            if ch in openers:
                stack.append(ch)
            elif ch in pairs:
                if not stack or stack[-1] != pairs[ch]:
                    report.add("error", 0,
                               f"Unbalanced bracket: unexpected '{ch}'.",
                               "Every '(', '[', '{' must be matched by a closing partner.")
                    return
                stack.pop()

    if in_quote:
        report.add("error", 0, 'Unterminated double-quote (") in document.',
                   'Node labels with special characters must be wrapped in "..." and closed.')
    if stack:
        report.add("error", 0,
                   f"Unbalanced bracket: {len(stack)} unclosed '{stack[-1]}'.",
                   "Check for a missing closing bracket on a node or subgraph.")


def _check_flowchart(lines: List[str], decl_idx: int, report: Report):
    decl = _strip_comments(lines[decl_idx]).strip()
    tokens = decl.split()
    if len(tokens) >= 2:
        direction = tokens[1].rstrip(";")
        if direction not in FLOWCHART_DIRECTIONS:
            report.add("warning", decl_idx + 1,
                       f"Unknown flowchart direction '{direction}'.",
                       f"Use one of: {', '.join(sorted(FLOWCHART_DIRECTIONS))}.")

    # subgraph / end balance
    depth = 0
    for i, raw in enumerate(lines):
        s = _strip_comments(raw).strip()
        if re.match(r"^subgraph\b", s):
            depth += 1
        elif s == "end":
            depth -= 1
            if depth < 0:
                report.add("error", i + 1,
                           "'end' without a matching 'subgraph'.",
                           "Remove the stray 'end' or add the opening 'subgraph'.")
                depth = 0
    if depth > 0:
        report.add("error", 0,
                   f"{depth} 'subgraph' block(s) missing a closing 'end'.",
                   "Each 'subgraph' must be terminated with 'end'.")


def _check_sequence(lines: List[str], report: Report):
    activate, deactivate = 0, 0
    block_openers = ("loop", "alt", "opt", "par", "critical", "rect", "break")
    block_depth = 0
    for i, raw in enumerate(lines):
        s = _strip_comments(raw).strip()
        if s.startswith("activate "):
            activate += 1
        elif s.startswith("deactivate "):
            deactivate += 1
        first = s.split()[0] if s else ""
        if first in block_openers:
            block_depth += 1
        elif first == "end":
            block_depth -= 1
            if block_depth < 0:
                report.add("error", i + 1,
                           "'end' without a matching block (loop/alt/opt/par/...).")
                block_depth = 0
    if block_depth > 0:
        report.add("error", 0,
                   f"{block_depth} sequence block(s) missing 'end'.",
                   "loop/alt/opt/par/critical/rect blocks each need an 'end'.")
    if activate != deactivate:
        report.add("warning", 0,
                   f"activate ({activate}) / deactivate ({deactivate}) counts differ.",
                   "Each 'activate X' usually pairs with a 'deactivate X'.")


def validate(text: str) -> Report:
    report = Report()
    lines = text.splitlines()

    if not text.strip():
        report.add("error", 0, "Empty diagram source.")
        return report

    diagram_type, decl_idx = _find_diagram_type(lines)
    report.diagram_type = diagram_type

    if diagram_type == "unknown":
        report.add("error", max(decl_idx + 1, 0),
                   "Could not detect a valid diagram type on the first non-comment line.",
                   "Start with one of: " + ", ".join(sorted(DIAGRAM_TYPES.keys())) + ".")
        return report

    _check_balanced(text, report, diagram_type)

    if diagram_type == "flowchart":
        _check_flowchart(lines, decl_idx, report)
    elif diagram_type == "sequence":
        _check_sequence(lines, report)

    # Tabs are a frequent silent cause of parse errors in Mermaid.
    for i, raw in enumerate(lines):
        if "\t" in raw:
            report.add("warning", i + 1,
                       "Tab character found; Mermaid prefers spaces for indentation.",
                       "Replace tabs with spaces to avoid parser quirks.")
            break

    return report


def _format_text(report: Report, source_name: str) -> str:
    out = []
    status = "OK" if report.ok else "FAILED"
    out.append(f"[{status}] {source_name}  (type: {report.diagram_type})")
    if not report.issues:
        out.append("  No issues found.")
    for it in report.issues:
        loc = f"line {it.line}" if it.line else "file"
        out.append(f"  {it.severity.upper():7} {loc}: {it.message}")
        if it.hint:
            out.append(f"          hint: {it.hint}")
    return "\n".join(out)


def main(argv=None):
    parser = argparse.ArgumentParser(description="Validate a Mermaid diagram.")
    parser.add_argument("path", help="Path to .mmd file, or '-' to read stdin.")
    parser.add_argument("--json", action="store_true", help="Emit a JSON report.")
    args = parser.parse_args(argv)

    if args.path == "-":
        text = sys.stdin.read()
        name = "<stdin>"
    else:
        try:
            with open(args.path, "r", encoding="utf-8") as fh:
                text = fh.read()
        except OSError as exc:
            print(f"error: cannot read {args.path}: {exc}", file=sys.stderr)
            return 2
        name = args.path

    report = validate(text)

    if args.json:
        payload = asdict(report)
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(_format_text(report, name))

    return 0 if report.ok else 1


if __name__ == "__main__":
    sys.exit(main())
