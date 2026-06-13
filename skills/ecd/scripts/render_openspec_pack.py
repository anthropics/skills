#!/usr/bin/env python3
"""
Render an OpenSpec-compatible pack from a normalized ECL case JSON.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


CJK_RE = re.compile(r"[\u3400-\u9fff]")

TEXT = {
    "en": {
        "proposal_title": "Proposal",
        "design_title": "Design",
        "tasks_title": "Tasks",
        "spec_title": "Specification",
        "summary": "Summary",
        "why": "Why",
        "in_scope": "In Scope",
        "out_of_scope": "Out of Scope",
        "success_signals": "Success Signals",
        "risks": "Risks",
        "repo_targets": "Repo Targets",
        "repo_grounding": "Repo Grounding",
        "product_decisions": "Frozen Product Decisions",
        "domain_model": "Domain Model",
        "data_contract": "Data Contract",
        "ui_contract": "UI Contract",
        "function_contracts": "Function Contracts",
        "file_plan": "File Plan",
        "verification": "Verification",
        "acceptance": "Acceptance",
        "requirements": "Requirements",
        "validation_targets": "Validation Targets",
        "implementation_units": "Implementation Units",
        "dependency_chain": "Dependency Chain",
        "execution_phases": "Execution Phases",
        "code_batches": "Code Batches",
        "objective": "Objective",
        "scope_label": "Scope",
        "dependencies": "Dependencies",
        "files_label": "Files",
        "functions_label": "Functions",
        "verification_label": "Verification",
        "done_when": "Done When",
        "unit_membership": "Units",
    },
    "zh-CN": {
        "proposal_title": "提案",
        "design_title": "设计",
        "tasks_title": "任务清单",
        "spec_title": "规格说明",
        "summary": "摘要",
        "why": "为什么做",
        "in_scope": "范围内",
        "out_of_scope": "范围外",
        "success_signals": "成功信号",
        "risks": "风险",
        "repo_targets": "目标仓库",
        "repo_grounding": "仓库落地事实",
        "product_decisions": "冻结产品决策",
        "domain_model": "领域模型",
        "data_contract": "数据契约",
        "ui_contract": "界面契约",
        "function_contracts": "函数契约",
        "file_plan": "文件计划",
        "verification": "验证",
        "acceptance": "验收",
        "requirements": "需求",
        "validation_targets": "验证目标",
        "implementation_units": "实现单元",
        "dependency_chain": "依赖链",
        "execution_phases": "执行阶段",
        "code_batches": "代码批次",
        "objective": "目标",
        "scope_label": "范围",
        "dependencies": "依赖",
        "files_label": "文件",
        "functions_label": "函数",
        "verification_label": "验证",
        "done_when": "完成条件",
        "unit_membership": "单元",
    },
}


def ensure_list(value):
    if value is None:
        return []
    if isinstance(value, list):
        return value
    return [value]


def detect_language(case: dict) -> str:
    value = str(case.get("output_language") or case.get("request_language") or "")
    if value:
        return value
    source = str(case.get("source_request") or case.get("title") or "")
    return "zh-CN" if CJK_RE.search(source) else "en"


def tr(language: str, key: str) -> str:
    return TEXT.get(language, TEXT["en"]).get(key, TEXT["en"].get(key, key))


def unwrap_block(raw: dict | None, block_key: str) -> dict:
    if not isinstance(raw, dict):
        return {}
    if isinstance(raw.get(block_key), dict):
        return raw[block_key]
    return raw


def stage(case: dict, key: str, block_key: str) -> dict:
    return unwrap_block(case.get("stages", {}).get(key), block_key)


def artifact(case: dict, key: str, block_key: str) -> dict:
    return unwrap_block(case.get("artifacts", {}).get(key), block_key)


def display_item(item) -> str:
    if isinstance(item, dict):
        return json.dumps(item, ensure_ascii=False, sort_keys=True)
    return str(item)


def markdown_list(items, checked: bool = False) -> str:
    values = ensure_list(items)
    if not values:
        return "- None recorded."
    marker = "- [ ] " if checked else "- "
    return "\n".join(f"{marker}{display_item(item)}" for item in values)


def inline_list(items) -> str:
    values = [display_item(item) for item in ensure_list(items) if item not in (None, "", [])]
    return ", ".join(values) if values else "-"


def select_value(record: dict, *keys: str):
    for key in keys:
        value = record.get(key)
        if value not in (None, "", []):
            return value
    return None


def render_record_section(lines: list[str], language: str, records, heading_key: str, field_specs: list[tuple[str, tuple[str, ...]]]) -> None:
    values = ensure_list(records)
    if not values:
        return
    lines.extend([f"## {tr(language, heading_key)}", ""])
    for index, record in enumerate(values, start=1):
        if not isinstance(record, dict):
            lines.append(f"- [ ] {display_item(record)}")
            continue
        identifier = select_value(record, "id", "name") or f"{heading_key[:1].upper()}{index}"
        title = select_value(record, "title", "name", "label")
        heading = f"{identifier} - {title}" if title and title != identifier else str(identifier)
        lines.append(f"### {heading}")
        for label_key, candidate_keys in field_specs:
            value = select_value(record, *candidate_keys)
            if value is None:
                continue
            if isinstance(value, list):
                text = inline_list(value)
            else:
                text = display_item(value)
            lines.append(f"- {tr(language, label_key)}: {text}")
        lines.append("")


def render_proposal(case: dict, language: str) -> str:
    preprocess = stage(case, "preprocess", "ecl.preprocess")
    requirements = stage(case, "requirements", "ecl.requirements")
    ledger = artifact(case, "constraint_ledger", "ecl.constraint_ledger")
    handoff = artifact(case, "code_handoff", "ecl.code_handoff")
    return "\n".join(
        [
            f"# {case['title']} {tr(language, 'proposal_title')}",
            "",
            f"## {tr(language, 'summary')}",
            str(case.get("summary") or ledger.get("retained_goal") or case.get("source_request") or ""),
            "",
            f"## {tr(language, 'why')}",
            str(ledger.get("retained_goal") or preprocess.get("reframed_request") or case.get("source_request") or ""),
            "",
            f"## {tr(language, 'in_scope')}",
            markdown_list(handoff.get("implementation_scope")),
            "",
            f"## {tr(language, 'out_of_scope')}",
            markdown_list(requirements.get("non_goals")),
            "",
            f"## {tr(language, 'success_signals')}",
            markdown_list(preprocess.get("success_signals")),
            "",
            f"## {tr(language, 'risks')}",
            markdown_list(ledger.get("risks")),
            "",
        ]
    )


def render_design(case: dict, language: str) -> str:
    closure = stage(case, "closure", "ecl.dependencies")
    execution_manifest = artifact(case, "execution_manifest", "ecl.execution_manifest")
    handoff = artifact(case, "code_handoff", "ecl.code_handoff")
    return "\n".join(
        [
            f"# {case['title']} {tr(language, 'design_title')}",
            "",
            f"## {tr(language, 'repo_targets')}",
            markdown_list(handoff.get("repo_targets")),
            "",
            f"## {tr(language, 'repo_grounding')}",
            markdown_list(handoff.get("repo_grounding")),
            "",
            f"## {tr(language, 'product_decisions')}",
            markdown_list(handoff.get("frozen_product_decisions")),
            "",
            f"## {tr(language, 'domain_model')}",
            markdown_list(handoff.get("domain_model")),
            "",
            f"## {tr(language, 'data_contract')}",
            markdown_list(handoff.get("data_contract")),
            "",
            f"## {tr(language, 'ui_contract')}",
            markdown_list(handoff.get("ui_contract")),
            "",
            f"## {tr(language, 'function_contracts')}",
            markdown_list(handoff.get("function_contracts")),
            "",
            f"## {tr(language, 'file_plan')}",
            markdown_list(handoff.get("file_plan")),
            "",
            f"## {tr(language, 'dependency_chain')}",
            markdown_list(closure.get("end_to_end_chain")),
            "",
            f"## {tr(language, 'execution_phases')}",
            markdown_list(execution_manifest.get("phases")),
            "",
        ]
    )


def render_tasks(case: dict, language: str) -> str:
    execution_manifest = artifact(case, "execution_manifest", "ecl.execution_manifest")
    code_batches = artifact(case, "code_batches", "ecl.code_batches")
    handoff = artifact(case, "code_handoff", "ecl.code_handoff")
    lines = [f"# {case['title']} {tr(language, 'tasks_title')}", ""]
    render_record_section(
        lines,
        language,
        execution_manifest.get("phases"),
        "execution_phases",
        [
            ("objective", ("objective", "goal", "description")),
            ("dependencies", ("depends_on", "dependencies")),
            ("unit_membership", ("units", "implementation_units", "unit_ids")),
            ("verification_label", ("verification", "checks")),
            ("done_when", ("done_when", "exit_signals", "done_signals")),
        ],
    )
    render_record_section(
        lines,
        language,
        code_batches.get("batches"),
        "code_batches",
        [
            ("objective", ("objective", "goal", "description")),
            ("dependencies", ("depends_on", "dependencies")),
            ("unit_membership", ("units", "implementation_units", "unit_ids")),
            ("files_label", ("files", "paths")),
            ("verification_label", ("verification", "checks")),
            ("done_when", ("done_when", "done_signals", "exit_criteria")),
        ],
    )
    lines.extend([f"## {tr(language, 'implementation_units')}", ""])
    units = ensure_list(handoff.get("implementation_units"))
    if not units:
        lines.append("- [ ] No implementation units recorded yet.")
        lines.append("")
    else:
        for unit in units:
            if not isinstance(unit, dict):
                lines.append(f"- [ ] {display_item(unit)}")
                continue
            unit_id = unit.get("id", "U?")
            title = unit.get("title", "")
            heading = f"{unit_id} - {title}" if title else str(unit_id)
            lines.append(f"### {heading}")
            details = [
                ("objective", select_value(unit, "objective", "goal")),
                ("scope_label", select_value(unit, "scope")),
                ("dependencies", select_value(unit, "depends_on", "dependencies")),
                ("files_label", select_value(unit, "files")),
                ("functions_label", select_value(unit, "functions")),
                ("verification_label", select_value(unit, "verification")),
                ("done_when", select_value(unit, "done_when")),
            ]
            for label_key, value in details:
                if value is None:
                    continue
                text = inline_list(value) if isinstance(value, list) else display_item(value)
                lines.append(f"- {tr(language, label_key)}: {text}")
            lines.append("")
    lines.extend(
        [
            f"## {tr(language, 'verification')}",
            markdown_list(handoff.get("verification_commands")),
            "",
            f"## {tr(language, 'acceptance')}",
            markdown_list(handoff.get("acceptance_checks")),
            "",
        ]
    )
    return "\n".join(lines)


def render_spec(case: dict, language: str) -> str:
    requirements = stage(case, "requirements", "ecl.requirements")
    handoff = artifact(case, "code_handoff", "ecl.code_handoff")
    lines = [
        f"# {case['title']} {tr(language, 'spec_title')}",
        "",
        f"## {tr(language, 'requirements')}",
    ]
    requirement_units = ensure_list(requirements.get("requirement_units"))
    if not requirement_units:
        lines.append("- None recorded.")
    else:
        for item in requirement_units:
            if not isinstance(item, dict):
                lines.append(f"- {display_item(item)}")
                continue
            lines.extend(
                [
                    f"### {item.get('id', 'R?')}",
                    f"- Statement: {item.get('statement', '')}",
                    f"- Rationale: {item.get('rationale', '')}",
                    f"- Verification hint: {item.get('verification_hint', '')}",
                    "",
                ]
            )
    lines.extend(
        [
            f"## {tr(language, 'validation_targets')}",
            markdown_list(requirements.get("validation_targets")),
            "",
            f"## {tr(language, 'acceptance')}",
            markdown_list(handoff.get("acceptance_checks")),
            "",
        ]
    )
    return "\n".join(lines)


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content.strip() + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Render an OpenSpec-compatible pack from ECL JSON.")
    parser.add_argument("input_json", help="Path to normalized ECL JSON input")
    parser.add_argument("--bundle", required=True, help="Bundle directory where the OpenSpec folder should be created")
    args = parser.parse_args()

    input_path = Path(args.input_json).expanduser().resolve()
    case = json.loads(input_path.read_text(encoding="utf-8"))
    language = detect_language(case)
    slug = str(case.get("slug") or "change")
    bundle_dir = Path(args.bundle).expanduser().resolve()
    open_spec_root = bundle_dir / "OpenSpec"

    change_dir = open_spec_root / "changes" / slug
    spec_dir = open_spec_root / "specs" / slug

    write_text(change_dir / "proposal.md", render_proposal(case, language))
    write_text(change_dir / "design.md", render_design(case, language))
    write_text(change_dir / "tasks.md", render_tasks(case, language))
    write_text(spec_dir / "spec.md", render_spec(case, language))

    print(f"[OK] OpenSpec pack rendered: {open_spec_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
