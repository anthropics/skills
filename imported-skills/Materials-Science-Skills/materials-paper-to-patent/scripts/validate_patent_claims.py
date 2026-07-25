#!/usr/bin/env python3
"""Validate Chinese invention patent claims content against the civil patent KB.

Exits 0 on pass (no ERROR), 1 on any ERROR, 2 on missing input file.
Mirrors the structure of materials-figure/scripts/validate_materials_claims.py.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any

import yaml


class Severity(str, Enum):
    ERROR = "ERROR"
    WARNING = "WARNING"
    INFO = "INFO"


@dataclass
class ValidationIssue:
    severity: Severity
    code: str
    message: str
    claim_number: int | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "severity": self.severity.value,
            "code": self.code,
            "message": self.message,
            "claim_number": self.claim_number,
        }


def _parse_severity(raw: str) -> Severity:
    if not raw:
        return Severity.WARNING
    raw_u = str(raw).upper()
    return Severity[raw_u] if raw_u in Severity.__members__ else Severity.WARNING


def load_kb(path: Path) -> dict[str, Any]:
    if not path.exists():
        print(f"ERROR: patent_kb.yaml not found: {path}", file=sys.stderr)
        sys.exit(2)
    return yaml.safe_load(path.read_text(encoding="utf-8"))


_INDEPENDENT_VERB = re.compile(r"其特征在于|其改进在于|其中")


def check_independent_claim_technical_features(claims: list[dict], kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    for claim in claims:
        if claim.get("type") != "independent":
            continue
        text = str(claim.get("text", ""))
        if not _INDEPENDENT_VERB.search(text):
            issues.append(ValidationIssue(
                Severity.ERROR,
                "missing_其特征在于",
                f"独立权利要求{claim.get('number')}缺少'其特征在于'引导语",
                claim_number=claim.get("number"),
            ))
        match = _INDEPENDENT_VERB.search(text)
        if match and len(text[match.end():].strip("：:; ，,。")) < 4:
            issues.append(ValidationIssue(
                Severity.ERROR,
                "no_technical_features",
                f"独立权利要求{claim.get('number')}缺少必要技术特征",
                claim_number=claim.get("number"),
            ))
    return issues


def check_dependent_claim_references(claims: list[dict], kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    claim_numbers = {c.get("number") for c in claims}
    ref_pattern = re.compile(r"权利要求\s*(\d+)")
    for claim in claims:
        if claim.get("type") != "dependent":
            continue
        claim_number = claim.get("number")
        text = str(claim.get("text", ""))
        numbers = [int(n) for n in ref_pattern.findall(text)]
        for n in numbers:
            if n not in claim_numbers or (isinstance(claim_number, int) and n >= claim_number):
                issues.append(ValidationIssue(
                    Severity.ERROR,
                    "bad_dependent_reference",
                    f"从属权利要求{claim_number}引用了不存在或非前置的权利要求{n}",
                    claim_number=claim_number,
                ))
        if not numbers:
            issues.append(ValidationIssue(
                Severity.ERROR,
                "no_dependent_reference",
                f"从属权利要求{claim_number}未引用任何权利要求",
                claim_number=claim_number,
            ))
    return issues


def _extract_keywords(text: str) -> set[str]:
    tokens: set[str] = set()
    chinese = re.findall(r"[\u4e00-\u9fff]+", text)
    for segment in chinese:
        if len(segment) < 2:
            continue
        tokens.update(segment[i:i + n] for n in (2, 3) for i in range(len(segment) - n + 1))
    for m in re.finditer(r"[A-Za-z][A-Za-z0-9\-]{1,}", text):
        tokens.add(m.group(0))
    return tokens


def check_support_in_specification(claims: list[dict], specification: dict, kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    spec_text = json.dumps(specification, ensure_ascii=False)
    spec_keywords = _extract_keywords(spec_text)
    for claim in claims:
        text = str(claim.get("text", ""))
        claim_keywords = _extract_keywords(text)
        if not claim_keywords:
            continue
        overlap = sum(1 for k in claim_keywords if k in spec_keywords)
        ratio = overlap / len(claim_keywords)
        if ratio < 0.4:
            issues.append(ValidationIssue(
                Severity.ERROR,
                "no_spec_support",
                f"权利要求{claim.get('number')}的关键术语在说明书中支持不足（覆盖率 {ratio:.0%}）",
                claim_number=claim.get("number"),
            ))
    return issues


def check_anti_patterns(claims: list[dict], kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    patterns = kb.get("claim_anti_patterns", [])
    for claim in claims:
        text = str(claim.get("text", ""))
        for ap in patterns:
            rid = ap.get("id", "")
            if "regex" in ap:
                if re.search(ap["regex"], text):
                    issues.append(ValidationIssue(
                        _parse_severity(ap.get("severity", "warning")),
                        f"anti_pattern:{rid}",
                        f"权利要求{claim.get('number')}触发反模式'{ap.get('description', rid)}'：{ap.get('fix_hint', '')}",
                        claim_number=claim.get("number"),
                    ))
            elif "keywords" in ap:
                for kw in ap["keywords"]:
                    if kw in text:
                        issues.append(ValidationIssue(
                            _parse_severity(ap.get("severity", "warning")),
                            f"anti_pattern:{rid}",
                            f"权利要求{claim.get('number')}触发反模式'{ap.get('description', rid)}'：包含关键词'{kw}'。{ap.get('fix_hint', '')}",
                            claim_number=claim.get("number"),
                        ))
    return issues


def check_unit_consistency(claims: list[dict], kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    unit_aliases = kb.get("unit_aliases", {})
    combined = " ".join(str(c.get("text", "")) for c in claims)
    for unit_type, info in unit_aliases.items():
        canonical = info.get("canonical", "")
        present_canonical = canonical in combined
        present_aliases = [a for a in info.get("aliases", []) if a != canonical and a in combined]
        if present_canonical and present_aliases:
            issues.append(ValidationIssue(
                Severity.WARNING,
                f"unit_mixed_usage:{unit_type}",
                f"单位'{unit_type}'在文本中混用了规范写法'{canonical}'和别名{present_aliases}，建议统一",
            ))
    return issues


def check_invention_type_alignment(claims: list[dict], invention_type: str, kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    patterns = kb.get("invention_type_patterns", {}).get(invention_type, {})
    allowed_verbs = set(patterns.get("typical_independent_claim_verbs", []))
    expected_steps = set(patterns.get("typical_method_steps", []))
    if not allowed_verbs:
        return issues
    for claim in claims:
        if claim.get("type") != "independent":
            continue
        text = str(claim.get("text", ""))
        if not any(v in text for v in allowed_verbs):
            issues.append(ValidationIssue(
                Severity.WARNING,
                "invention_type_verb_mismatch",
                f"权利要求{claim.get('number')}未使用{invention_type}类常见引导词{allowed_verbs}之一",
                claim_number=claim.get("number"),
            ))
        if invention_type == "process-material" and not any(s in text for s in expected_steps):
            issues.append(ValidationIssue(
                Severity.INFO,
                "invention_type_step_hint",
                f"权利要求{claim.get('number')}未包含工艺类典型步骤词（{sorted(expected_steps)[:3]}等）",
                claim_number=claim.get("number"),
            ))
    return issues


def check_claim_count_limits(claims: list[dict], kb: dict) -> list[ValidationIssue]:
    issues: list[ValidationIssue] = []
    independents = [c for c in claims if c.get("type") == "independent"]
    if len(independents) > 2:
        issues.append(ValidationIssue(
            Severity.ERROR,
            "too_many_independents",
            f"独立权利要求有{len(independents)}个，超过2个；除非满足单一性例外，否则应减少",
        ))
    return issues


def validate(draft: dict, invention_type: str, kb: dict) -> list[ValidationIssue]:
    claims = draft.get("claims", [])
    specification = draft.get("specification", {})
    findings: list[ValidationIssue] = []
    findings += check_independent_claim_technical_features(claims, kb)
    findings += check_dependent_claim_references(claims, kb)
    findings += check_support_in_specification(claims, specification, kb)
    findings += check_anti_patterns(claims, kb)
    findings += check_unit_consistency(claims, kb)
    findings += check_invention_type_alignment(claims, invention_type, kb)
    findings += check_claim_count_limits(claims, kb)
    return findings


def format_report(findings: list[ValidationIssue]) -> str:
    if not findings:
        return "PASS: 权利要求通过知识库驱动的内容校验。\n"
    lines = [f"{f.severity.value}\t{f.code}\t{f.message}" for f in findings]
    errors = sum(1 for f in findings if f.severity == Severity.ERROR)
    warnings = sum(1 for f in findings if f.severity == Severity.WARNING)
    lines.append("")
    lines.append(f"汇总: {errors} 个错误, {warnings} 个警告")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("draft", type=Path, help="UTF-8 structured patent draft JSON")
    parser.add_argument(
        "--invention-type",
        default="process-material",
        choices=["process-material", "apparatus-system", "algorithm-software", "mixed"],
        help="Invention type axis value (default: process-material)",
    )
    parser.add_argument("--kb", type=Path, help="Override KB path")
    parser.add_argument("--report", type=Path, help="Write report to a file")
    parser.add_argument("--json", action="store_true", help="Print findings as JSON")
    args = parser.parse_args()

    if not args.draft.exists():
        print(f"ERROR: draft file not found: {args.draft}", file=sys.stderr)
        return 2

    kb_path = args.kb or (Path(__file__).resolve().parent.parent / "static" / "core" / "patent_kb.yaml")
    kb = load_kb(kb_path)
    draft = json.loads(args.draft.read_text(encoding="utf-8"))
    findings = validate(draft, args.invention_type, kb)
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
