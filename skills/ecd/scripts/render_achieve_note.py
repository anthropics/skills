#!/usr/bin/env python3
"""
Render a final acceptance-and-archive note under Runs/<run-id>/03-achieve.md.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

FENCE_RE = re.compile(r"```([^\n`]*)\n(.*?)\n```", re.DOTALL)

TEXT = {
    "en": {
        "title": "Acceptance & Archive",
        "goal": "Goal",
        "narrative": "Narrative",
        "verdict": "Verdict",
        "archive_status": "Archive Status",
        "archive_reason": "Archive Reason",
        "acceptance_results": "Acceptance Results",
        "verification_summary": "Verification Summary",
        "residual_issues": "Residual Issues",
        "next_actions": "Next Actions",
        "archive_refs": "Archive References",
        "evidence_refs": "Evidence References",
        "structured_block": "Structured Block",
        "none_recorded": "None recorded.",
    },
    "zh-CN": {
        "title": "验收归档",
        "goal": "目标",
        "narrative": "说明",
        "verdict": "结论",
        "archive_status": "归档状态",
        "archive_reason": "归档说明",
        "acceptance_results": "验收结果",
        "verification_summary": "验证总结",
        "residual_issues": "残留问题",
        "next_actions": "下一步",
        "archive_refs": "归档引用",
        "evidence_refs": "证据引用",
        "structured_block": "结构化块",
        "none_recorded": "暂无记录。",
    },
}


def parse_json_fence(note_path: Path, block_key: str) -> dict | None:
    if not note_path.exists():
        return None
    content = note_path.read_text(encoding="utf-8")
    for info, body in FENCE_RE.findall(content):
        info = info.strip().lower()
        text = body.strip()
        if not text:
            continue
        if info and not info.startswith("json"):
            continue
        try:
            parsed = json.loads(text)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict) and isinstance(parsed.get(block_key), dict):
            return parsed[block_key]
    return None


def quote_yaml_scalar(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def frontmatter(metadata: dict[str, str]) -> str:
    lines = ["---"]
    for key, value in metadata.items():
        lines.append(f"{key}: {quote_yaml_scalar(str(value))}")
    lines.append("---")
    return "\n".join(lines)


def tr(language: str, key: str) -> str:
    return TEXT.get(language, TEXT["en"]).get(key, TEXT["en"].get(key, key))


def ensure_list(value):
    if value is None:
        return []
    if isinstance(value, list):
        return value
    return [value]


def display_item(item) -> str:
    if isinstance(item, dict):
        return json.dumps(item, ensure_ascii=False, sort_keys=True)
    return str(item)


def markdown_list(items, language: str) -> str:
    values = ensure_list(items)
    if not values:
        return f"- {tr(language, 'none_recorded')}"
    return "\n".join(f"- {display_item(item)}" for item in values)


def infer_archive_status(verdict: str) -> str:
    if verdict == "not_achieved":
        return "left_open"
    return "archived"


def infer_archive_reason(verdict: str, language: str) -> str:
    if verdict == "not_achieved":
        if language == "zh-CN":
            return "当前结果未通过冻结验收，因此保持 case 打开，等待重做或重进。"
        return "The result did not satisfy the frozen acceptance bar, so the case stays open."
    if verdict == "achieved_with_followups":
        if language == "zh-CN":
            return "本次交付已通过验收，低影响跟进项单独记录，当前 case 归档关闭。"
        return "The run passed acceptance with only low-impact followups, so archive it as closed."
    if language == "zh-CN":
        return "本次交付已满足冻结验收条件，作为正式闭环记录归档。"
    return "The run satisfied the frozen acceptance contract and should be archived as closed."


def normalize_payload(payload: dict, language: str) -> dict:
    normalized = dict(payload)
    verdict = str(normalized.get("verdict") or "not_achieved")
    run_id = str(normalized.get("run_id") or "").strip()
    archive_status = str(normalized.get("archive_status") or infer_archive_status(verdict))
    archive_refs = ensure_list(normalized.get("archive_refs"))
    if not archive_refs and run_id:
        archive_refs = [
            f"Runs/{run_id}/00-code-run.md",
            f"Runs/{run_id}/01-verification.md",
        ]
    normalized["archive_status"] = archive_status
    normalized["archive_reason"] = str(
        normalized.get("archive_reason") or infer_archive_reason(verdict, language)
    )
    normalized["archive_refs"] = archive_refs
    return normalized


def load_case_context(bundle_dir: Path) -> tuple[str, str]:
    case_block = parse_json_fence(bundle_dir / "00-overview.md", "ecl.case") or {}
    case_title = str(case_block.get("title") or bundle_dir.name)
    language = str(case_block.get("output_language") or case_block.get("request_language") or "en")
    return case_title, language


def build_content(case_title: str, language: str, payload: dict) -> str:
    payload = normalize_payload(payload, language)
    block = {
        "ecl.achieve": {
            "status": payload.get("status", "complete"),
            "run_id": payload["run_id"],
            "verdict": payload["verdict"],
            "archive_status": payload["archive_status"],
            "archive_reason": payload["archive_reason"],
            "acceptance_results": ensure_list(payload.get("acceptance_results")),
            "verification_summary": ensure_list(payload.get("verification_summary")),
            "residual_issues": ensure_list(payload.get("residual_issues")),
            "next_actions": ensure_list(payload.get("next_actions")),
            "archive_refs": ensure_list(payload.get("archive_refs")),
            "evidence_refs": ensure_list(payload.get("evidence_refs")),
        }
    }
    title = f"{tr(language, 'title')} {payload['run_id']}"
    parts = [
        frontmatter(
            {
                "title": title,
                "case": case_title,
                "stage": "run",
                "stage_key": "achieve",
                "status": payload.get("status", "complete"),
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {title}",
        "",
        "[[00-overview]] | [[00-code-run]] | [[01-verification]]",
        "",
        f"## {tr(language, 'goal')}",
        str(payload.get("goal") or ""),
        "",
        f"## {tr(language, 'narrative')}",
        str(payload.get("narrative") or ""),
        "",
        f"## {tr(language, 'verdict')}",
        f"- `{payload['verdict']}`",
        "",
        f"## {tr(language, 'archive_status')}",
        f"- `{payload['archive_status']}`",
        "",
        f"## {tr(language, 'archive_reason')}",
        str(payload.get("archive_reason") or ""),
        "",
        f"## {tr(language, 'acceptance_results')}",
        markdown_list(payload.get("acceptance_results"), language),
        "",
        f"## {tr(language, 'verification_summary')}",
        markdown_list(payload.get("verification_summary"), language),
        "",
        f"## {tr(language, 'residual_issues')}",
        markdown_list(payload.get("residual_issues"), language),
        "",
        f"## {tr(language, 'next_actions')}",
        markdown_list(payload.get("next_actions"), language),
        "",
        f"## {tr(language, 'archive_refs')}",
        markdown_list(payload.get("archive_refs"), language),
        "",
        f"## {tr(language, 'evidence_refs')}",
        markdown_list(payload.get("evidence_refs"), language),
        "",
        f"## {tr(language, 'structured_block')}",
        "```json",
        json.dumps(block, ensure_ascii=False, indent=2),
        "```",
        "",
    ]
    return "\n".join(parts)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Render a final acceptance-and-archive note under Runs/<run-id>/03-achieve.md."
    )
    parser.add_argument("bundle_dir", help="Path to the ECL bundle directory")
    parser.add_argument("achieve_json", help="Path to the achieve payload JSON")
    args = parser.parse_args()

    bundle_dir = Path(args.bundle_dir).expanduser().resolve()
    payload = json.loads(Path(args.achieve_json).expanduser().read_text(encoding="utf-8"))
    payload.setdefault("status", "complete")

    run_id = str(payload.get("run_id") or "").strip()
    if not run_id:
        raise SystemExit("[ERROR] achieve payload requires run_id")

    run_dir = bundle_dir / "Runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    case_title, language = load_case_context(bundle_dir)
    content = build_content(case_title, language, payload)
    output_path = run_dir / "03-achieve.md"
    output_path.write_text(content, encoding="utf-8")
    print(f"[OK] Rendered achieve note: {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
