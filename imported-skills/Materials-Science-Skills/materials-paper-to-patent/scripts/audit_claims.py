#!/usr/bin/env python3
"""Run deterministic structural checks on Chinese patent claims (materials-paper-to-patent)."""

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path


CLAIM_START = re.compile(r"(?m)^\s*(\d+)\s*[.、．]\s*")
REFERENCE = re.compile(
    r"权利要求\s*(\d+)(?:\s*[-—~～至]\s*(\d+))?"
    r"|权利要求\s*(\d+)\s*(?:或|、)\s*(\d+)"
)
TERM_INTRO = re.compile(r"(?:所述|该)([\u4e00-\u9fffA-Za-z][\u4e00-\u9fffA-Za-z0-9_-]{1,20})")
PLACEHOLDER = re.compile(r"\[(?:TO CONFIRM|待确认)[^\]]*\]", re.IGNORECASE)


@dataclass
class Finding:
    level: str
    claim: int | None
    code: str
    message: str


def split_claims(text: str) -> list[tuple[int, str]]:
    matches = list(CLAIM_START.finditer(text))
    claims = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        claims.append((int(match.group(1)), text[match.end() : end].strip()))
    return claims


def references(body: str) -> list[int]:
    result = []
    for match in REFERENCE.finditer(body):
        if match.group(1):
            start = int(match.group(1))
            finish = int(match.group(2) or start)
            result.extend(range(start, finish + 1))
        else:
            result.extend((int(match.group(3)), int(match.group(4))))
    return sorted(set(result))


def normalize(text: str) -> str:
    return re.sub(r"\s+", "", text)


def audit(text: str) -> list[Finding]:
    claims = split_claims(text)
    findings = []
    if not claims:
        return [Finding("ERROR", None, "NO_CLAIMS", "未识别到以“1.”形式起始的权利要求。")]

    numbers = [number for number, _ in claims]
    expected = list(range(1, len(claims) + 1))
    if numbers != expected:
        findings.append(
            Finding("ERROR", None, "NUMBER_SEQUENCE", f"编号应连续为{expected}，实际为{numbers}。")
        )

    previous_text = ""
    claim_map = {}
    for number, body in claims:
        compact = normalize(body)
        claim_map[number] = compact
        refs = references(body)

        if not body:
            findings.append(Finding("ERROR", number, "EMPTY", "权利要求正文为空。"))
            continue
        if PLACEHOLDER.search(body):
            findings.append(
                Finding("ERROR", number, "PLACEHOLDER", "正式权利要求中仍含待确认标记。")
            )
        if number == 1 and refs:
            findings.append(
                Finding("ERROR", number, "INDEPENDENT_REFERENCE", "权利要求1不应引用其他权利要求。")
            )
        if number > 1 and not refs:
            findings.append(
                Finding("WARNING", number, "NO_REFERENCE", "未检测到从属引用；确认其是否为独立权利要求。")
            )
        for ref in refs:
            if ref >= number:
                findings.append(
                    Finding("ERROR", number, "FORWARD_REFERENCE", f"引用了非在先权利要求{ref}。")
                )
            if ref not in claim_map:
                findings.append(
                    Finding("ERROR", number, "MISSING_REFERENCE", f"引用的权利要求{ref}不存在。")
                )

        if "其特征在于" not in compact:
            findings.append(
                Finding("WARNING", number, "TRANSITION", "未检测到“其特征在于”过渡语。")
            )
        if len(compact) < 25:
            findings.append(
                Finding("WARNING", number, "TOO_SHORT", "权利要求较短，确认是否完整限定技术方案。")
            )
        if re.search(r"(效果更好|性能优异|显著提高|大大提高|最佳|最优)", compact):
            findings.append(
                Finding("WARNING", number, "RESULT_LANGUAGE", "含结果或宣传性措辞，确认是否改为技术限定。")
            )

        searchable_basis = previous_text + "".join(
            claim_map.get(ref, "") for ref in refs
        )
        for term in sorted(set(TERM_INTRO.findall(body))):
            if term in {"方法", "装置", "设备", "系统", "步骤", "程序"}:
                continue
            if term not in searchable_basis and compact.find(term) <= 4:
                findings.append(
                    Finding(
                        "WARNING",
                        number,
                        "ANTECEDENT_BASIS",
                        f"术语“{term}”可能缺少清晰的前置基础。",
                    )
                )
        previous_text += compact

    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("claims", type=Path, help="UTF-8 claims text file")
    parser.add_argument("--json", action="store_true", help="Output findings as JSON")
    args = parser.parse_args()

    text = args.claims.read_text(encoding="utf-8")
    findings = audit(text)
    if args.json:
        print(json.dumps([finding.__dict__ for finding in findings], ensure_ascii=False, indent=2))
    elif not findings:
        print("PASS: 未发现结构性问题。")
    else:
        for finding in findings:
            location = f"权利要求{finding.claim}" if finding.claim else "整体"
            print(f"{finding.level}\t{location}\t{finding.code}\t{finding.message}")
        errors = sum(finding.level == "ERROR" for finding in findings)
        warnings = sum(finding.level == "WARNING" for finding in findings)
        print(f"\n汇总: {errors} 个错误, {warnings} 个警告")

    return 1 if any(finding.level == "ERROR" for finding in findings) else 0


if __name__ == "__main__":
    raise SystemExit(main())
