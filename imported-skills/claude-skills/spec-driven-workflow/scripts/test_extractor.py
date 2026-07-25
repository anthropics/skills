#!/usr/bin/env python3
"""
Test Extractor - Extracts test case stubs from a feature specification.

Parses acceptance criteria (Given/When/Then) and edge cases from a spec
document, then generates test stubs for the specified framework.

Supported frameworks: pytest, jest, go-test

Exit codes: 0 = success, 1 = warnings (some criteria unparseable), 2 = critical error

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import re
import sys
import textwrap
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


class SpecParser:
    """Parses spec documents to extract testable criteria."""

    def __init__(self, content: str):
        self.content = content
        self.lines = content.split("\n")

    def extract_acceptance_criteria(self) -> List[Dict[str, Any]]:
        """Extract AC-N blocks with Given/When/Then clauses."""
        criteria = []
        ac_pattern = re.compile(r"###\s+AC-(\d+):\s*(.+?)(?:\s*\(([^)]+)\))?\s*$")

        in_ac = False
        current_ac: Optional[Dict[str, Any]] = None
        body_lines: List[str] = []

        for line in self.lines:
            match = ac_pattern.match(line)
            if match:
                # Save previous AC
                if current_ac is not None:
                    current_ac["body"] = "\n".join(body_lines).strip()
                    self._parse_gwt(current_ac)
                    criteria.append(current_ac)

                ac_id = int(match.group(1))
                name = match.group(2).strip()
                refs = match.group(3).strip() if match.group(3) else ""

                current_ac = {
                    "id": f"AC-{ac_id}",
                    "name": name,
                    "references": [r.strip() for r in refs.split(",") if r.strip()] if refs else [],
                    "given": "",
                    "when": "",
                    "then": [],
                    "body": "",
                }
                body_lines = []
                in_ac = True
            elif in_ac:
                # Check if we hit another ## section
                if re.match(r"^##\s+", line) and not re.match(r"^###\s+", line):
                    in_ac = False
                    if current_ac is not None:
                        current_ac["body"] = "\n".join(body_lines).strip()
                        self._parse_gwt(current_ac)
                        criteria.append(current_ac)
                        current_ac = None
                else:
                    body_lines.append(line)

        # Don't forget the last one
        if current_ac is not None:
            current_ac["body"] = "\n".join(body_lines).strip()
            self._parse_gwt(current_ac)
            criteria.append(current_ac)

        return criteria

    def extract_edge_cases(self) -> List[Dict[str, Any]]:
        """Extract EC-N edge case items."""
        edge_cases = []
        ec_pattern = re.compile(r"-\s+EC-(\d+):\s*(.+?)(?:\s*->\s*|\s*->\s*|\s*→\s*)(.+)")

        in_section = False
        for line in self.lines:
            if re.match(r"^##\s+Edge\s+Cases", line, re.IGNORECASE):
                in_section = True
                continue
            if in_section and re.match(r"^##\s+", line):
                break
            if in_section:
                match = ec_pattern.match(line.strip())
                if match:
                    edge_cases.append({
                        "id": f"EC-{match.group(1)}",
                        "condition": match.group(2).strip().rstrip("."),
                        "behavior": match.group(3).strip().rstrip("."),
                    })

        return edge_cases

    def extract_spec_title(self) -> str:
        """Extract the spec title from the first H1."""
        for line in self.lines:
            match = re.match(r"^#\s+(?:Spec:\s*)?(.+)", line)
            if match:
                return match.group(1).strip()
        return "UnknownFeature"

    @staticmethod
    def _parse_gwt(ac: Dict[str, Any]):
        """Parse Given/When/Then from the AC body text."""
        body = ac["body"]
        lines = body.split("\n")

        current_section = None
        for line in lines:
            stripped = line.strip()
            if not stripped:
                continue

            lower = stripped.lower()
            if lower.startswith("given "):
                current_section = "given"
                ac["given"] = stripped[6:].strip()
            elif lower.startswith("when "):
                current_section = "when"
                ac["when"] = stripped[5:].strip()
            elif lower.startswith("then "):
                current_section = "then"
                ac["then"].append(stripped[5:].strip())
            elif lower.startswith("and "):
                if current_section == "then":
                    ac["then"].append(stripped[4:].strip())
                elif current_section == "given":
                    ac["given"] += " AND " + stripped[4:].strip()
                elif current_section == "when":
                    ac["when"] += " AND " + stripped[4:].strip()


def _sanitize_name(name: str) -> str:
    """Convert a human-readable name to a valid function/method name."""
    # Remove parenthetical references like (FR-1)
    name = re.sub(r"\([^)]*\)", "", name)
    # Replace non-alphanumeric with underscore
    name = re.sub(r"[^a-zA-Z0-9]+", "_", name)
    # Remove leading/trailing underscores
    name = name.strip("_").lower()
    return name or "unnamed"


def _to_pascal_case(name: str) -> str:
    """Convert to PascalCase for Go test names."""
    parts = _sanitize_name(name).split("_")
    return "".join(p.capitalize() for p in parts if p)


class PytestGenerator:
    """Generates pytest test stubs."""

    def generate(self, title: str, criteria: List[Dict], edge_cases: List[Dict]) -> str:
        class_name = "Test" + _to_pascal_case(title)
        lines = [
            '"""',
            f"Test suite for: {title}",
            f"Auto-generated from spec. {len(criteria)} acceptance criteria, {len(edge_cases)} edge cases.",
            "",
            "All tests are stubs — implement the test body to make them pass.",
            '"""',
            "",
            "import pytest",
            "",
            "",
            f"class {class_name}:",
            f'    """Tests for {title}."""',
            "",
        ]

        for ac in criteria:
            method_name = f"test_{ac['id'].lower().replace('-', '')}_{_sanitize_name(ac['name'])}"
            docstring = f'{ac["id"]}: {ac["name"]}'
            ref_str = f" [{', '.join(ac['references'])}]" if ac["references"] else ""

            lines.append(f"    def {method_name}(self):")
            lines.append(f'        """{docstring}{ref_str}"""')

            if ac["given"]:
                lines.append(f"        # Given {ac['given']}")
            if ac["when"]:
                lines.append(f"        # When {ac['when']}")
            for t in ac["then"]:
                lines.append(f"        # Then {t}")

            lines.append('        raise NotImplementedError("Implement this test")')
            lines.append("")

        if edge_cases:
            lines.append("    # --- Edge Cases ---")
            lines.append("")

        for ec in edge_cases:
            method_name = f"test_{ec['id'].lower().replace('-', '')}_{_sanitize_name(ec['condition'])}"
            lines.append(f"    def {method_name}(self):")
            lines.append(f'        """{ec["id"]}: {ec["condition"]} -> {ec["behavior"]}"""')
            lines.append(f"        # Condition: {ec['condition']}")
            lines.append(f"        # Expected: {ec['behavior']}")
            lines.append('        raise NotImplementedError("Implement this test")')
            lines.append("")

        return "\n".join(lines)


class JestGenerator:
    """Generates Jest/Vitest test stubs (TypeScript)."""

    def generate(self, title: str, criteria: List[Dict], edge_cases: List[Dict]) -> str:
        lines = [
            f"/**",
            f" * Test suite for: {title}",
            f" * Auto-generated from spec. {len(criteria)} acceptance criteria, {len(edge_cases)} edge cases.",
            f" *",
            f" * All tests are stubs — implement the test body to make them pass.",
            f" */",
            "",
            f'describe("{title}", () => {{',
        ]

        for ac in criteria:
            ref_str = f" [{', '.join(ac['references'])}]" if ac["references"] else ""
            test_name = f"{ac['id']}: {ac['name']}{ref_str}"

            lines.append(f'  it("{test_name}", () => {{')
            if ac["given"]:
                lines.append(f"    // Given {ac['given']}")
            if ac["when"]:
                lines.append(f"    // When {ac['when']}")
            for t in ac["then"]:
                lines.append(f"    // Then {t}")
            lines.append("")
            lines.append('    throw new Error("Not implemented");')
            lines.append("  });")
            lines.append("")

        if edge_cases:
            lines.append("  // --- Edge Cases ---")
            lines.append("")

        for ec in edge_cases:
            test_name = f"{ec['id']}: {ec['condition']}"
            lines.append(f'  it("{test_name}", () => {{')
            lines.append(f"    // Condition: {ec['condition']}")
            lines.append(f"    // Expected: {ec['behavior']}")
            lines.append("")
            lines.append('    throw new Error("Not implemented");')
            lines.append("  });")
            lines.append("")

        lines.append("});")
        lines.append("")

        return "\n".join(lines)


class GoTestGenerator:
    """Generates Go test stubs."""

    def generate(self, title: str, criteria: List[Dict], edge_cases: List[Dict]) -> str:
        package_name = _sanitize_name(title).split("_")[0] or "feature"

        lines = [
            f"package {package_name}_test",
            "",
            "import (",
            '\t"testing"',
            ")",
            "",
            f"// Test suite for: {title}",
            f"// Auto-generated from spec. {len(criteria)} acceptance criteria, {len(edge_cases)} edge cases.",
            f"// All tests are stubs — implement the test body to make them pass.",
            "",
        ]

        for ac in criteria:
            func_name = "Test" + _to_pascal_case(ac["id"] + " " + ac["name"])
            ref_str = f" [{', '.join(ac['references'])}]" if ac["references"] else ""

            lines.append(f"// {ac['id']}: {ac['name']}{ref_str}")
            lines.append(f"func {func_name}(t *testing.T) {{")

            if ac["given"]:
                lines.append(f"\t// Given {ac['given']}")
            if ac["when"]:
                lines.append(f"\t// When {ac['when']}")
            for then_clause in ac["then"]:
                lines.append(f"\t// Then {then_clause}")

            lines.append("")
            lines.append('\tt.Fatal("Not implemented")')
            lines.append("}")
            lines.append("")

        if edge_cases:
            lines.append("// --- Edge Cases ---")
            lines.append("")

        for ec in edge_cases:
            func_name = "Test" + _to_pascal_case(ec["id"] + " " + ec["condition"])
            lines.append(f"// {ec['id']}: {ec['condition']} -> {ec['behavior']}")
            lines.append(f"func {func_name}(t *testing.T) {{")
            lines.append(f"\t// Condition: {ec['condition']}")
            lines.append(f"\t// Expected: {ec['behavior']}")
            lines.append("")
            lines.append('\tt.Fatal("Not implemented")')
            lines.append("}")
            lines.append("")

        return "\n".join(lines)


GENERATORS = {
    "pytest": PytestGenerator,
    "jest": JestGenerator,
    "go-test": GoTestGenerator,
}

FILE_EXTENSIONS = {
    "pytest": ".py",
    "jest": ".test.ts",
    "go-test": "_test.go",
}


def main():
    parser = argparse.ArgumentParser(
        description="Extract test case stubs from a feature specification.",
        epilog="Example: python test_extractor.py --file spec.md --framework pytest --output tests/test_feature.py",
    )
    parser.add_argument(
        "--file",
        "-f",
        required=True,
        help="Path to the spec markdown file",
    )
    parser.add_argument(
        "--framework",
        choices=list(GENERATORS.keys()),
        default="pytest",
        help="Target test framework (default: pytest)",
    )
    parser.add_argument(
        "--output",
        "-o",
        default=None,
        help="Output file path (default: stdout)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_flag",
        help="Output extracted criteria as JSON instead of test code",
    )

    args = parser.parse_args()

    file_path = Path(args.file)
    if not file_path.exists():
        print(f"Error: File not found: {file_path}", file=sys.stderr)
        sys.exit(2)

    content = file_path.read_text(encoding="utf-8")
    if not content.strip():
        print(f"Error: File is empty: {file_path}", file=sys.stderr)
        sys.exit(2)

    spec_parser = SpecParser(content)
    title = spec_parser.extract_spec_title()
    criteria = spec_parser.extract_acceptance_criteria()
    edge_cases = spec_parser.extract_edge_cases()

    if not criteria and not edge_cases:
        print("Error: No acceptance criteria or edge cases found in spec.", file=sys.stderr)
        sys.exit(2)

    warnings = []
    for ac in criteria:
        if not ac["given"] and not ac["when"]:
            warnings.append(f"{ac['id']}: Could not parse Given/When/Then — check format.")

    if args.json_flag:
        result = {
            "spec_title": title,
            "framework": args.framework,
            "acceptance_criteria": criteria,
            "edge_cases": edge_cases,
            "warnings": warnings,
            "counts": {
                "acceptance_criteria": len(criteria),
                "edge_cases": len(edge_cases),
                "total_test_cases": len(criteria) + len(edge_cases),
            },
        }
        output = json.dumps(result, indent=2)
    else:
        generator_class = GENERATORS[args.framework]
        generator = generator_class()
        output = generator.generate(title, criteria, edge_cases)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(output, encoding="utf-8")
        total = len(criteria) + len(edge_cases)
        print(f"Generated {total} test stubs -> {out_path}", file=sys.stderr)
    else:
        print(output)

    if warnings:
        for w in warnings:
            print(f"Warning: {w}", file=sys.stderr)
        sys.exit(1)

    sys.exit(0)


if __name__ == "__main__":
    main()
