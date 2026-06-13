#!/usr/bin/env python3
"""
Render append-only ECL v2 /code run notes under Runs/<run-id>/.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    import yaml  # type: ignore
except ImportError:  # pragma: no cover
    yaml = None

FENCE_RE = re.compile(r"```([^\n`]*)\n(.*?)\n```", re.DOTALL)

ALLOWED_OUTCOMES = {
    "completed",
    "completed_with_low_impact_fixes",
    "blocked_for_reentry",
    "refused_by_gate",
}

BLOCKING_OUTCOMES = {"blocked_for_reentry", "refused_by_gate"}

TEXT = {
    "en": {
        "goal": "Goal",
        "narrative": "Narrative",
        "handoff_ref": "Handoff Reference",
        "entry_repo": "Entry Repo",
        "repo_grounding": "Repo Grounding",
        "selected_units": "Selected Units",
        "changed_files": "Changed Files",
        "low_impact_fixes": "Low-Impact Fixes",
        "high_impact_conflicts": "High-Impact Conflicts",
        "outcome": "Outcome",
        "commands_run": "Commands Run",
        "results": "Results",
        "failed_checks": "Failed Checks",
        "evidence_refs": "Evidence References",
        "recommended_reopen_stage": "Recommended Reopen Stage",
        "reason_class": "Reason Class",
        "blocking_evidence": "Blocking Evidence",
        "must_freeze_before_resume": "Must Freeze Before Resume",
        "structured_block": "Structured Block",
        "none_recorded": "None recorded.",
        "code_run_title": "Code Run",
        "verification_title": "Verification",
        "reentry_title": "Reentry Request",
    },
    "zh-CN": {
        "goal": "目标",
        "narrative": "说明",
        "handoff_ref": "交接引用",
        "entry_repo": "入口仓库",
        "repo_grounding": "Repo 落地检查",
        "selected_units": "选中实现单元",
        "changed_files": "变更文件",
        "low_impact_fixes": "低影响修补",
        "high_impact_conflicts": "高影响冲突",
        "outcome": "结果",
        "commands_run": "执行命令",
        "results": "结果记录",
        "failed_checks": "失败检查",
        "evidence_refs": "证据引用",
        "recommended_reopen_stage": "建议重开阶段",
        "reason_class": "原因分类",
        "blocking_evidence": "阻塞证据",
        "must_freeze_before_resume": "恢复前必须冻结",
        "structured_block": "结构化块",
        "none_recorded": "暂无记录。",
        "code_run_title": "代码运行记录",
        "verification_title": "验证记录",
        "reentry_title": "回流请求",
    },
}


def parse_structured_block(info: str, body: str):
    info = info.strip().lower()
    text = body.strip()
    if not text:
        return None
    if info.startswith("json") or text.startswith("{"):
        return json.loads(text)
    if info.startswith("yaml"):
        if yaml is None:
            raise ValueError("Found YAML block but PyYAML is not installed.")
        return yaml.safe_load(text)
    if info:
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        if yaml is None:
            raise ValueError("Block is not valid JSON and YAML parsing is unavailable.")
        return yaml.safe_load(text)


def find_named_block(note_path: Path, block_key: str):
    content = note_path.read_text(encoding="utf-8")
    for info, body in FENCE_RE.findall(content):
        parsed = parse_structured_block(info, body)
        if isinstance(parsed, dict) and block_key in parsed:
            return parsed[block_key]
    raise ValueError(f"Could not find structured block '{block_key}' in {note_path.name}")


def tr(language: str, key: str) -> str:
    bucket = TEXT.get(language, TEXT["en"])
    return bucket.get(key, TEXT["en"].get(key, key))


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


def quote_yaml_scalar(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def frontmatter(metadata: dict[str, str]) -> str:
    lines = ["---"]
    for key, value in metadata.items():
        lines.append(f"{key}: {quote_yaml_scalar(str(value))}")
    lines.append("---")
    return "\n".join(lines)


def build_code_run_content(case_title: str, language: str, payload: dict) -> str:
    block = {
        "ecl.code_run": {
            "status": payload["status"],
            "run_id": payload["run_id"],
            "case_id": payload["case_id"],
            "handoff_ref": payload["handoff_ref"],
            "entry_repo": payload["entry_repo"],
            "selected_units": payload["selected_units"],
            "changed_files": payload["changed_files"],
            "outcome": payload["outcome"],
        }
    }
    parts = [
        frontmatter(
            {
                "title": f"{tr(language, 'code_run_title')} {payload['run_id']}",
                "case": case_title,
                "stage": "run",
                "stage_key": "code_run",
                "status": payload["status"],
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {tr(language, 'code_run_title')} {payload['run_id']}",
        "",
        "[[00-overview]] | [[90-code-handoff]] | [[01-verification]]",
        "",
        f"## {tr(language, 'goal')}",
        payload["goal"],
        "",
        f"## {tr(language, 'narrative')}",
        payload["narrative"],
        "",
        f"## {tr(language, 'handoff_ref')}",
        f"- {payload['handoff_ref']}",
        "",
        f"## {tr(language, 'entry_repo')}",
        f"- {payload['entry_repo'] or tr(language, 'none_recorded')}",
        "",
        f"## {tr(language, 'repo_grounding')}",
        markdown_list(payload["repo_grounding"], language),
        "",
        f"## {tr(language, 'selected_units')}",
        markdown_list(payload["selected_units"], language),
        "",
        f"## {tr(language, 'changed_files')}",
        markdown_list(payload["changed_files"], language),
        "",
        f"## {tr(language, 'low_impact_fixes')}",
        markdown_list(payload["low_impact_fixes"], language),
        "",
        f"## {tr(language, 'high_impact_conflicts')}",
        markdown_list(payload["high_impact_conflicts"], language),
        "",
        f"## {tr(language, 'outcome')}",
        f"- `{payload['outcome']}`",
        "",
        f"## {tr(language, 'structured_block')}",
        "```json",
        json.dumps(block, ensure_ascii=False, indent=2),
        "```",
        "",
    ]
    return "\n".join(parts)


def build_verification_content(case_title: str, language: str, payload: dict) -> str:
    verification = payload["verification"]
    block = {
        "ecl.code_verification": {
            "status": verification["status"],
            "run_id": payload["run_id"],
            "commands_run": verification["commands_run"],
            "results": verification["results"],
            "failed_checks": verification["failed_checks"],
            "evidence_refs": verification["evidence_refs"],
        }
    }
    parts = [
        frontmatter(
            {
                "title": f"{tr(language, 'verification_title')} {payload['run_id']}",
                "case": case_title,
                "stage": "run",
                "stage_key": "code_verification",
                "status": verification["status"],
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {tr(language, 'verification_title')} {payload['run_id']}",
        "",
        "[[00-overview]] | [[00-code-run]]",
        "",
        f"## {tr(language, 'goal')}",
        verification["goal"],
        "",
        f"## {tr(language, 'narrative')}",
        verification["narrative"],
        "",
        f"## {tr(language, 'commands_run')}",
        markdown_list(verification["commands_run"], language),
        "",
        f"## {tr(language, 'results')}",
        markdown_list(verification["results"], language),
        "",
        f"## {tr(language, 'failed_checks')}",
        markdown_list(verification["failed_checks"], language),
        "",
        f"## {tr(language, 'evidence_refs')}",
        markdown_list(verification["evidence_refs"], language),
        "",
        f"## {tr(language, 'structured_block')}",
        "```json",
        json.dumps(block, ensure_ascii=False, indent=2),
        "```",
        "",
    ]
    return "\n".join(parts)


def build_reentry_content(case_title: str, language: str, payload: dict) -> str:
    block = {
        "ecl.reentry_request": {
            "status": "complete",
            "run_id": payload["run_id"],
            "recommended_reopen_stage": payload["reentry"]["recommended_reopen_stage"],
            "reason_class": payload["reentry"]["reason_class"],
            "blocking_evidence": payload["reentry"]["blocking_evidence"],
            "must_freeze_before_resume": payload["reentry"]["must_freeze_before_resume"],
        }
    }
    parts = [
        frontmatter(
            {
                "title": f"{tr(language, 'reentry_title')} {payload['run_id']}",
                "case": case_title,
                "stage": "run",
                "stage_key": "reentry_request",
                "status": "complete",
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {tr(language, 'reentry_title')} {payload['run_id']}",
        "",
        "[[00-overview]] | [[00-code-run]]",
        "",
        f"## {tr(language, 'recommended_reopen_stage')}",
        f"- {payload['reentry']['recommended_reopen_stage']}",
        "",
        f"## {tr(language, 'reason_class')}",
        f"- {payload['reentry']['reason_class']}",
        "",
        f"## {tr(language, 'blocking_evidence')}",
        markdown_list(payload["reentry"]["blocking_evidence"], language),
        "",
        f"## {tr(language, 'must_freeze_before_resume')}",
        markdown_list(payload["reentry"]["must_freeze_before_resume"], language),
        "",
        f"## {tr(language, 'structured_block')}",
        "```json",
        json.dumps(block, ensure_ascii=False, indent=2),
        "```",
        "",
    ]
    return "\n".join(parts)


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def infer_case_title(bundle_dir: Path) -> str:
    overview_path = bundle_dir / "00-overview.md"
    try:
        case_block = find_named_block(overview_path, "ecl.case")
    except Exception:
        return bundle_dir.name
    if isinstance(case_block, dict) and case_block.get("title"):
        return str(case_block["title"])
    return bundle_dir.name


def infer_case_id(bundle_dir: Path) -> str:
    overview_path = bundle_dir / "00-overview.md"
    try:
        case_block = find_named_block(overview_path, "ecl.case")
    except Exception:
        return bundle_dir.name
    if isinstance(case_block, dict) and case_block.get("case_id"):
        return str(case_block["case_id"])
    return bundle_dir.name


def infer_language(payload: dict) -> str:
    if payload.get("output_language"):
        return str(payload["output_language"])
    sample = json.dumps(payload, ensure_ascii=False)
    return "zh-CN" if re.search(r"[\u3400-\u9fff]", sample) else "en"


def require_non_empty_fields(payload: dict, fields: list[str]) -> list[str]:
    missing: list[str] = []
    for field in fields:
        value = payload.get(field)
        if isinstance(value, str):
            if not value.strip():
                missing.append(field)
        elif value is None:
            missing.append(field)
    return missing


def main() -> int:
    parser = argparse.ArgumentParser(description="Render append-only ECL v2 /code run notes.")
    parser.add_argument("bundle_dir", help="Path to the case bundle directory")
    parser.add_argument("input_json", help="Path to the run JSON input")
    args = parser.parse_args()

    bundle_dir = Path(args.bundle_dir).expanduser().resolve()
    input_path = Path(args.input_json).expanduser().resolve()
    if not bundle_dir.exists():
        print(f"[ERROR] Bundle directory not found: {bundle_dir}")
        return 1
    if not input_path.exists():
        print(f"[ERROR] Input JSON not found: {input_path}")
        return 1

    try:
        payload = json.loads(input_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"[ERROR] Invalid JSON: {exc}")
        return 1

    if payload.get("outcome") not in ALLOWED_OUTCOMES:
        print("[ERROR] Invalid outcome in run payload.")
        return 1

    payload.setdefault("status", "complete")
    payload.setdefault("handoff_ref", "90-code-handoff.md")
    payload.setdefault("case_id", infer_case_id(bundle_dir))
    payload.setdefault("entry_repo", "")
    payload.setdefault("selected_units", payload.get("selected_batches", []))
    payload.setdefault("changed_files", [])
    payload.setdefault("repo_grounding", [])
    payload.setdefault("low_impact_fixes", [])
    payload.setdefault("high_impact_conflicts", [])
    payload.setdefault(
        "verification",
        {
            "status": "complete",
            "goal": "Capture verification commands and outcomes for this /code run.",
            "narrative": "",
            "commands_run": [],
            "results": [],
            "failed_checks": [],
            "evidence_refs": [],
        },
    )

    run_id = str(payload.get("run_id", "")).strip()
    if not run_id:
        print("[ERROR] run_id is required.")
        return 1
    missing_fields = require_non_empty_fields(payload, ["goal", "narrative", "outcome"])
    if missing_fields:
        print(f"[ERROR] Missing required run payload fields: {', '.join(missing_fields)}")
        return 1
    if payload["outcome"] in BLOCKING_OUTCOMES and "reentry" not in payload:
        print("[ERROR] Blocking outcomes require a reentry block.")
        return 1

    case_title = infer_case_title(bundle_dir)
    language = infer_language(payload)
    run_dir = bundle_dir / "Runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    write_text(run_dir / "00-code-run.md", build_code_run_content(case_title, language, payload))
    write_text(run_dir / "01-verification.md", build_verification_content(case_title, language, payload))

    if payload["outcome"] in BLOCKING_OUTCOMES:
        write_text(run_dir / "02-reentry.md", build_reentry_content(case_title, language, payload))

    print(f"[OK] Rendered run evidence: {run_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
