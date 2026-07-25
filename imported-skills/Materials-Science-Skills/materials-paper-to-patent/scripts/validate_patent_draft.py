#!/usr/bin/env python3
"""Validate the structural shape of a Chinese invention patent draft.json."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any


class Severity(str, Enum):
    ERROR = "ERROR"
    WARNING = "WARNING"


@dataclass
class DraftIssue:
    severity: Severity
    code: str
    message: str
    path: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "severity": self.severity.value,
            "code": self.code,
            "message": self.message,
            "path": self.path,
        }


REQUIRED_TOP_KEYS = (
    "title",
    "metadata",
    "source_map",
    "claims",
    "specification",
    "abstract",
    "invention_concept",
    "abstract_figure_number",
)

REQUIRED_METADATA_KEYS = ("jurisdiction", "invention_type", "language_mode")


def validate_draft(draft: dict) -> list[DraftIssue]:
    issues: list[DraftIssue] = []

    for key in REQUIRED_TOP_KEYS:
        if key not in draft:
            issues.append(DraftIssue(
                Severity.ERROR,
                "missing_top_key",
                f"draft.json 缺少顶层字段 '{key}'",
                path=key,
            ))

    metadata = draft.get("metadata", {})
    if isinstance(metadata, dict):
        for key in REQUIRED_METADATA_KEYS:
            if key not in metadata:
                issues.append(DraftIssue(
                    Severity.ERROR,
                    "missing_metadata_key",
                    f"metadata 缺少字段 '{key}'",
                    path=f"metadata.{key}",
                ))
        if metadata.get("jurisdiction") and "CNIPA" not in str(metadata.get("jurisdiction", "")) and "中国" not in str(metadata.get("jurisdiction", "")):
            issues.append(DraftIssue(
                Severity.WARNING,
                "unexpected_jurisdiction",
                f"jurisdiction='{metadata.get('jurisdiction')}' 预期为 CNIPA / 中国",
                path="metadata.jurisdiction",
            ))

    claims = draft.get("claims")
    if isinstance(claims, list):
        if not claims:
            issues.append(DraftIssue(Severity.ERROR, "no_claims", "claims 数组为空", path="claims"))
        else:
            numbers = [c.get("number") for c in claims]
            expected = list(range(1, len(claims) + 1))
            if numbers != expected:
                issues.append(DraftIssue(
                    Severity.ERROR,
                    "claim_number_sequence",
                    f"权利要求编号应连续 1..N，实际为 {numbers}",
                    path="claims",
                ))
            for claim in claims:
                if not claim.get("text"):
                    issues.append(DraftIssue(
                        Severity.ERROR,
                        "empty_claim",
                        f"权利要求{claim.get('number')} text 为空",
                        path=f"claims[{claim.get('number')}]",
                    ))
                if claim.get("type") == "dependent" and not claim.get("depends_on"):
                    issues.append(DraftIssue(
                        Severity.WARNING,
                        "missing_depends_on",
                        f"从属权利要求{claim.get('number')} 缺少 depends_on 字段",
                        path=f"claims[{claim.get('number')}]",
                    ))

    spec = draft.get("specification", {})
    if isinstance(spec, dict):
        for key in ("技术领域", "背景技术", "发明内容", "具体实施方式"):
            if key not in spec:
                issues.append(DraftIssue(
                    Severity.ERROR,
                    "missing_specification_section",
                    f"说明书缺少 {key} 章节",
                    path=f"specification.{key}",
                ))

    abstract = draft.get("abstract", "")
    if not abstract or len(str(abstract)) < 50:
        issues.append(DraftIssue(
            Severity.WARNING,
            "short_abstract",
            "摘要过短（< 50 字符）",
            path="abstract",
        ))

    concept = draft.get("invention_concept", {})
    if isinstance(concept, dict):
        if not concept.get("problem") or not concept.get("solution"):
            issues.append(DraftIssue(
                Severity.WARNING,
                "incomplete_concept",
                "invention_concept 缺少 problem / solution",
                path="invention_concept",
            ))

    fig_n = draft.get("abstract_figure_number")
    if not isinstance(fig_n, int) or fig_n < 1:
        issues.append(DraftIssue(
            Severity.ERROR,
            "bad_abstract_figure_number",
            f"abstract_figure_number 应为正整数，实际为 {fig_n}",
            path="abstract_figure_number",
        ))

    return issues


def format_report(findings: list[DraftIssue]) -> str:
    if not findings:
        return "PASS: draft.json 结构校验通过。\n"
    lines = [f"{f.severity.value}\t{f.code}\t{f.path}\t{f.message}" for f in findings]
    errors = sum(1 for f in findings if f.severity == Severity.ERROR)
    warnings = sum(1 for f in findings if f.severity == Severity.WARNING)
    lines.append("")
    lines.append(f"汇总: {errors} 个错误, {warnings} 个警告")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("draft", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if not args.draft.exists():
        print(f"ERROR: draft file not found: {args.draft}", file=sys.stderr)
        return 2

    try:
        draft = json.loads(args.draft.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        print(f"ERROR: invalid JSON: {e}", file=sys.stderr)
        return 2

    findings = validate_draft(draft)
    report = format_report(findings)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(report, encoding="utf-8")
    if args.json:
        print(json.dumps([f.to_dict() for f in findings], ensure_ascii=False, indent=2))
    else:
        print(report, end="")
    return 1 if any(f.severity == Severity.ERROR for f in findings) else 0


if __name__ == "__main__":
    raise SystemExit(main())
