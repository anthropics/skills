#!/usr/bin/env python3
"""
Render a normalized ECL v2 JSON file into an Obsidian note bundle.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import date
from pathlib import Path

try:
    import yaml  # type: ignore
except ImportError:  # pragma: no cover
    yaml = None

DEFAULT_VAULT_ROOT = Path(
    os.environ.get("OBSIDIAN_VAULT", str(Path.home() / "Documents/Obsidian Vault"))
).expanduser()
DEFAULT_OUTPUT_ROOT = DEFAULT_VAULT_ROOT / "Topics" / "Evolution-Constraint-Language"

CJK_RE = re.compile(r"[\u3400-\u9fff]")

DEFAULT_SCHEMA = {
    "notes": [
        {
            "id": "overview",
            "kind": "artifact",
            "filename": "00-overview.md",
            "block_key": "ecl.case",
            "template": "overview.md",
        },
        {
            "id": "constraint_ledger",
            "kind": "artifact",
            "filename": "05-constraint-ledger.md",
            "block_key": "ecl.constraint_ledger",
            "template": "constraint-ledger.md",
        },
        {
            "id": "preprocess",
            "kind": "stage",
            "letter": "A",
            "filename": "10-a-preprocess.md",
            "block_key": "ecl.preprocess",
            "template": "stage-a.md",
        },
        {
            "id": "divergence",
            "kind": "stage",
            "letter": "B",
            "filename": "20-b-divergence.md",
            "block_key": "ecl.options",
            "template": "stage-b.md",
        },
        {
            "id": "requirements",
            "kind": "stage",
            "letter": "C",
            "filename": "30-c-requirements.md",
            "block_key": "ecl.requirements",
            "template": "stage-c.md",
        },
        {
            "id": "critique",
            "kind": "stage",
            "letter": "D",
            "filename": "40-d-critique.md",
            "block_key": "ecl.conflicts",
            "template": "stage-d.md",
        },
        {
            "id": "closure",
            "kind": "stage",
            "letter": "E",
            "filename": "50-e-closure.md",
            "block_key": "ecl.dependencies",
            "template": "stage-e.md",
        },
        {
            "id": "probes",
            "kind": "stage",
            "letter": "F",
            "filename": "60-f-probes.md",
            "block_key": "ecl.probes",
            "template": "stage-f.md",
        },
        {
            "id": "red_blue",
            "kind": "stage",
            "letter": "G",
            "filename": "70-g-red-blue.md",
            "block_key": "ecl.adversarial",
            "template": "stage-g.md",
        },
        {
            "id": "review",
            "kind": "stage",
            "letter": "H",
            "filename": "80-h-review.md",
            "block_key": "ecl.review",
            "template": "stage-h.md",
        },
        {
            "id": "code_handoff",
            "kind": "artifact",
            "filename": "90-code-handoff.md",
            "block_key": "ecl.code_handoff",
            "template": "code-handoff.md",
        },
        {
            "id": "canonical_contracts",
            "kind": "artifact",
            "filename": "91-canonical-contracts.md",
            "block_key": "ecl.canonical_contracts",
            "template": "canonical-contracts.md",
        },
        {
            "id": "constraint_crosswalk",
            "kind": "artifact",
            "filename": "92-constraint-crosswalk.md",
            "block_key": "ecl.constraint_crosswalk",
            "template": "constraint-crosswalk.md",
        },
        {
            "id": "execution_manifest",
            "kind": "artifact",
            "filename": "95-execution-manifest.md",
            "block_key": "ecl.execution_manifest",
            "template": "execution-manifest.md",
        },
        {
            "id": "code_batches",
            "kind": "artifact",
            "filename": "96-code-batches.md",
            "block_key": "ecl.code_batches",
            "template": "code-batches.md",
        },
        {
            "id": "code_preflight",
            "kind": "artifact",
            "filename": "97-code-preflight.md",
            "block_key": "ecl.code_preflight",
            "template": "code-preflight.md",
        },
        {
            "id": "compile_for_code",
            "kind": "stage",
            "letter": "J",
            "filename": "98-j-compile-for-code.md",
            "block_key": "ecl.compile_for_code",
            "template": "stage-j.md",
        },
        {
            "id": "final_handoff",
            "kind": "artifact",
            "filename": "99-code-handoff.md",
            "block_key": "ecl.final_handoff",
            "template": "final-handoff.md",
        },
    ]
}

TEXT = {
    "en": {
        "summary": "Summary",
        "source_request": "Source Request",
        "final_outcome": "Final Outcome",
        "stage_status_index": "Stage Status Index",
        "paths": "Paths",
        "vault_root": "Vault root",
        "bundle_path": "Bundle path",
        "project_paths": "Project paths",
        "repo_paths": "Repo paths",
        "structured_block": "Structured Block",
        "goal": "Goal",
        "narrative": "Narrative",
        "key_points": "Key Points",
        "decisions": "Decisions",
        "open_questions": "Open Questions",
        "next_actions": "Next Actions",
        "none_recorded": "None recorded.",
        "pending": "This note has not been completed yet.",
        "blocked": "This note is blocked because the required independent agent could not be created.",
        "prev": "Prev",
        "next": "Next",
        "retained_goal": "Retained Goal",
        "confirmed_facts": "Confirmed Facts",
        "challenged_claims": "Challenged Claims",
        "frozen_constraints": "Frozen Constraints",
        "dropped_options": "Dropped Options",
        "risks": "Risks",
        "dependency_chain": "Dependency Chain",
        "verification_semantics": "Verification Semantics",
        "handoff_ref": "Handoff Reference",
        "options": "Options",
        "decision_criteria": "Decision Criteria",
        "retained_option_id": "Retained Option",
        "requirement_units": "Requirement Units",
        "interface_contracts": "Interface Contracts",
        "success_criteria": "Success Criteria",
        "validation_targets": "Validation Targets",
        "non_goals": "Non-Goals",
        "frozen_terms": "Frozen Terms",
        "critique_findings": "Critique Findings",
        "orthogonal_axes": "Orthogonal Axes",
        "conflicts": "Conflicts",
        "dropped_requirements": "Dropped Requirements",
        "resolution_decisions": "Resolution Decisions",
        "end_to_end_chain": "End-To-End Chain",
        "dependency_gaps": "Dependency Gaps",
        "completions": "Completions",
        "unresolved_dependencies": "Unresolved Dependencies",
        "probes": "Probes",
        "discarded_paths": "Discarded Paths",
        "surviving_paths": "Surviving Paths",
        "open_probe_limits": "Open Probe Limits",
        "attack_vectors": "Attack Vectors",
        "mitigations": "Mitigations",
        "residual_risks": "Residual Risks",
        "unresolved_attacks": "Unresolved Attacks",
        "verdict": "Verdict",
        "approval_conditions": "Approval Conditions",
        "blockers": "Blockers",
        "rationale": "Rationale",
        "reentry_stage_if_rejected": "Reentry Stage If Rejected",
        "code_ready": "Code Ready",
        "handoff_summary": "Handoff Summary",
        "implementation_scope": "Implementation Scope",
        "repo_targets": "Repo Targets",
        "repo_grounding": "Repo Grounding",
        "read_first": "Read First",
        "frozen_product_decisions": "Frozen Product Decisions",
        "domain_model": "Domain Model",
        "data_contract": "Data Contract",
        "ui_contract": "UI Contract",
        "function_contracts": "Function Contracts",
        "file_plan": "File Plan",
        "implementation_units": "Implementation Units",
        "verification_commands": "Verification Commands",
        "browser_checks": "Browser Checks",
        "acceptance_checks": "Acceptance Checks",
        "allowed_decisions": "Allowed Decisions",
        "forbidden_decisions": "Forbidden Decisions",
        "reentry_triggers": "Reentry Triggers",
        "reopen_stage_map": "Reopen Stage Map",
        "unresolved_gaps": "Unresolved Gaps",
        "contracts": "Contracts",
        "crosswalk_rows": "Crosswalk Rows",
        "phases": "Execution Phases",
        "scaffold_blueprint": "Scaffold Blueprint",
        "batches": "Code Batches",
        "confirmed": "Confirmed",
        "do_not_reinvent": "Do Not Reinterpret",
        "do_first": "Do First",
        "context_bundle": "Context Bundle",
        "progress_snapshot": "Progress Snapshot",
        "current_focus": "Current Focus",
        "remaining_work": "Remaining Work",
        "pause_conditions": "Pause Conditions",
        "session_notes": "Session Notes",
        "blocking_gaps": "Blocking Gaps",
        "frozen_contract_refs": "Frozen Contract References",
        "compiled_review_conditions": "Compiled Review Conditions",
        "execution_manifest_ref": "Execution Manifest Reference",
        "handoff_entry": "Handoff Entry",
        "reopen_stage_if_blocked": "Reopen Stage If Blocked",
        "direct_code_command": "Direct Code Command",
        "repo_absent_policy": "Repo Absent Policy",
        "mandatory_multi_agent_stage_blocked": "Mandatory Multi-Agent Stage Blocked",
        "next_step": "Direct Next Step",
    },
    "zh-CN": {
        "summary": "摘要",
        "source_request": "原始需求",
        "final_outcome": "最终结论",
        "stage_status_index": "阶段状态索引",
        "paths": "路径",
        "vault_root": "Vault 根目录",
        "bundle_path": "Bundle 路径",
        "project_paths": "项目路径",
        "repo_paths": "仓库路径",
        "structured_block": "结构化块",
        "goal": "目标",
        "narrative": "说明",
        "key_points": "关键信息",
        "decisions": "决策",
        "open_questions": "待确认问题",
        "next_actions": "下一步",
        "none_recorded": "暂无记录。",
        "pending": "该笔记尚未完成。",
        "blocked": "该笔记被阻塞，因为所需独立 Agent 无法创建。",
        "prev": "上一阶段",
        "next": "下一阶段",
        "retained_goal": "当前保留目标",
        "confirmed_facts": "已确认事实",
        "challenged_claims": "被质疑主张",
        "frozen_constraints": "冻结约束",
        "dropped_options": "已淘汰方案",
        "risks": "风险",
        "dependency_chain": "依赖链",
        "verification_semantics": "验证语义",
        "handoff_ref": "交接引用",
        "options": "方案卡",
        "decision_criteria": "决策标准",
        "retained_option_id": "保留方案",
        "requirement_units": "需求单元",
        "interface_contracts": "接口契约",
        "success_criteria": "成功标准",
        "validation_targets": "验证目标",
        "non_goals": "非目标",
        "frozen_terms": "冻结术语",
        "critique_findings": "挑刺发现",
        "orthogonal_axes": "正交维度",
        "conflicts": "冲突",
        "dropped_requirements": "被删除需求",
        "resolution_decisions": "裁决决定",
        "end_to_end_chain": "端到端链路",
        "dependency_gaps": "依赖缺口",
        "completions": "补全项",
        "unresolved_dependencies": "未解决依赖",
        "probes": "探测",
        "discarded_paths": "淘汰路径",
        "surviving_paths": "保留路径",
        "open_probe_limits": "探测限制",
        "attack_vectors": "攻击面",
        "mitigations": "缓解方案",
        "residual_risks": "残余风险",
        "unresolved_attacks": "未解攻击",
        "verdict": "评审结论",
        "approval_conditions": "通过条件",
        "blockers": "阻塞项",
        "rationale": "评审理由",
        "reentry_stage_if_rejected": "拒绝时重开阶段",
        "code_ready": "是否可进入代码阶段",
        "handoff_summary": "交接摘要",
        "implementation_scope": "实现范围",
        "repo_targets": "目标仓库",
        "repo_grounding": "仓库落地事实",
        "read_first": "先读这些",
        "frozen_product_decisions": "冻结产品决策",
        "domain_model": "领域模型",
        "data_contract": "数据契约",
        "ui_contract": "界面契约",
        "function_contracts": "函数契约",
        "file_plan": "文件计划",
        "implementation_units": "实现单元",
        "verification_commands": "验证命令",
        "browser_checks": "浏览器检查",
        "acceptance_checks": "验收检查",
        "allowed_decisions": "允许决定的事项",
        "forbidden_decisions": "禁止决定的事项",
        "reentry_triggers": "回流触发器",
        "reopen_stage_map": "重开阶段映射",
        "unresolved_gaps": "未解决缺口",
        "contracts": "契约",
        "crosswalk_rows": "对照项",
        "phases": "执行阶段",
        "scaffold_blueprint": "脚手架蓝图",
        "batches": "代码批次",
        "confirmed": "已确认",
        "do_not_reinvent": "禁止重新发明",
        "do_first": "应先执行",
        "context_bundle": "上下文包",
        "progress_snapshot": "进度快照",
        "current_focus": "当前焦点",
        "remaining_work": "剩余工作",
        "pause_conditions": "暂停条件",
        "session_notes": "会话记录",
        "blocking_gaps": "阻塞缺口",
        "frozen_contract_refs": "冻结契约引用",
        "compiled_review_conditions": "已编译评审条件",
        "execution_manifest_ref": "执行清单引用",
        "handoff_entry": "交接入口",
        "reopen_stage_if_blocked": "阻塞时重开阶段",
        "direct_code_command": "直接代码命令",
        "repo_absent_policy": "缺少仓库时策略",
        "mandatory_multi_agent_stage_blocked": "必需多代理阶段是否阻塞",
        "next_step": "直接下一步",
    },
}

STAGE_TITLES = {
    "en": {
        "preprocess": "Preprocess",
        "divergence": "Divergence",
        "requirements": "Requirements",
        "critique": "Critique",
        "closure": "Closure",
        "probes": "Probes",
        "red_blue": "Red-Blue",
        "review": "Review",
        "compile_for_code": "Compile For Code",
    },
    "zh-CN": {
        "preprocess": "预处理",
        "divergence": "发散",
        "requirements": "需求拆解",
        "critique": "挑刺",
        "closure": "补全",
        "probes": "探测",
        "red_blue": "红蓝对抗",
        "review": "评审",
        "compile_for_code": "编译交接",
    },
}

ARTIFACT_TITLES = {
    "en": {
        "constraint_ledger": "Constraint Ledger",
        "code_handoff": "Code Handoff",
        "canonical_contracts": "Canonical Contracts",
        "constraint_crosswalk": "Constraint Crosswalk",
        "execution_manifest": "Execution Manifest",
        "code_batches": "Code Batches",
        "code_preflight": "Code Workboard",
        "final_handoff": "Final Code Handoff",
    },
    "zh-CN": {
        "constraint_ledger": "约束账本",
        "code_handoff": "代码交接",
        "canonical_contracts": "规范契约",
        "constraint_crosswalk": "约束对照",
        "execution_manifest": "执行清单",
        "code_batches": "代码批次",
        "code_preflight": "编码工作板",
        "final_handoff": "最终代码交接",
    },
}

STAGE_GOALS = {
    "en": {
        "preprocess": "Reframe the raw request around the user's likely real goal.",
        "divergence": "Expand the solution space and fill blind spots.",
        "requirements": "Convert the retained path into concrete requirement units.",
        "critique": "Use an opposing agent to remove weak or conflicting requirements.",
        "closure": "Close the dependency chain so the retained requirements can run end-to-end.",
        "probes": "Probe the converged path with executable validation wherever possible.",
        "red_blue": "Pressure-test the retained path with attack and defense.",
        "review": "Decide whether the package is ready for coding.",
        "compile_for_code": "Compile A-H into frozen companion docs and the final code handoff.",
    },
    "zh-CN": {
        "preprocess": "围绕用户真正想要的目标重构原始诉求。",
        "divergence": "扩大发散空间并补齐用户盲区。",
        "requirements": "把保留路径拆成具体需求单元。",
        "critique": "用反对视角删除薄弱或冲突需求。",
        "closure": "补全依赖链，让保留需求形成完整端到端闭环。",
        "probes": "尽可能用可执行验证去探测收敛路径。",
        "red_blue": "通过攻击与防守压测保留路径。",
        "review": "判断当前包是否足够进入编码。",
        "compile_for_code": "把 A-H 结果编译成冻结 companion docs 和最终代码交接。",
    },
}

ARTIFACT_GOALS = {
    "en": {
        "constraint_ledger": "Preserve the shared truth source across A-H.",
        "code_handoff": "Provide the only truthful implementation entrypoint.",
        "canonical_contracts": "Freeze the retained product and system contracts in a concise form.",
        "constraint_crosswalk": "Map each frozen constraint to code locations and verification.",
        "execution_manifest": "Freeze the implementation sequence or scaffold blueprint before coding.",
        "code_batches": "Group code changes into executable batches.",
        "code_preflight": "Provide the shared execution workboard and record what coding must not reopen or reinvent.",
        "final_handoff": "Summarize code readiness, blockers, and the direct next command.",
    },
    "zh-CN": {
        "constraint_ledger": "沉淀 A-H 共用的事实、约束和验证语义。",
        "code_handoff": "提供唯一真实可执行的实现入口。",
        "canonical_contracts": "把保留的产品与系统契约压缩成简洁冻结版本。",
        "constraint_crosswalk": "把冻结约束映射到代码落点与验证方式。",
        "execution_manifest": "在编码前冻结执行顺序或 scaffold blueprint。",
        "code_batches": "把代码变更分成可执行批次。",
        "code_preflight": "提供共享执行工作板，并记录编码阶段不得重开或重造的事项。",
        "final_handoff": "汇总 code_ready、阻塞项和直接下一命令。",
    },
}

OVERVIEW_DEFAULTS = {
    "summary": {
        "en": "Bundle initialized. Update this after the A-H flow converges.",
        "zh-CN": "Bundle 已初始化。请在 A-H 收敛后回填摘要。",
    },
    "final_outcome": {
        "en": "No final outcome recorded yet.",
        "zh-CN": "尚未记录最终结论。",
    },
}


def load_schema(script_path: Path) -> list[dict]:
    schema_path = script_path.parent.parent / "schemas" / "ecl-v2" / "schema.yaml"
    if yaml is None or not schema_path.exists():
        return DEFAULT_SCHEMA["notes"]
    try:
        loaded = yaml.safe_load(schema_path.read_text(encoding="utf-8"))
    except Exception:
        return DEFAULT_SCHEMA["notes"]
    notes = loaded.get("notes") if isinstance(loaded, dict) else None
    if not isinstance(notes, list):
        return DEFAULT_SCHEMA["notes"]
    return notes


def slugify(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", value.strip().lower())
    slug = re.sub(r"-{2,}", "-", slug).strip("-")
    return slug or "untitled-case"


def normalize_language(value: str | None) -> str | None:
    if not value:
        return None
    lowered = str(value).strip().lower()
    if lowered.startswith("zh"):
        return "zh-CN"
    if lowered.startswith("en"):
        return "en"
    return str(value)


def detect_request_language(text: str) -> str:
    return "zh-CN" if CJK_RE.search(text or "") else "en"


def resolve_languages(case: dict) -> tuple[str, str]:
    request_language = normalize_language(case.get("request_language")) or detect_request_language(
        case.get("source_request", "")
    )
    output_language = normalize_language(case.get("output_language")) or request_language
    case["request_language"] = request_language
    case["output_language"] = output_language
    return request_language, output_language


def tr(language: str, key: str) -> str:
    bucket = TEXT.get(language, TEXT["en"])
    return bucket.get(key, TEXT["en"].get(key, key))


def stage_title(stage_key: str, language: str) -> str:
    return STAGE_TITLES.get(language, STAGE_TITLES["en"]).get(stage_key, stage_key)


def artifact_title(artifact_key: str, language: str) -> str:
    return ARTIFACT_TITLES.get(language, ARTIFACT_TITLES["en"]).get(artifact_key, artifact_key)


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


def unwrap_raw(raw: dict | None, block_key: str) -> dict:
    if not isinstance(raw, dict):
        return {}
    if block_key in raw and isinstance(raw[block_key], dict):
        return dict(raw[block_key])
    return dict(raw)


def normalize_case(case: dict, bundle_dir: Path) -> None:
    case["bundle_version"] = 2
    case["slug"] = case.get("slug") or slugify(case["title"])
    case["date"] = case.get("date") or date.today().isoformat()
    case["mode"] = case.get("mode") or "spec"
    case["vault_root"] = str(Path(case.get("vault_root", DEFAULT_VAULT_ROOT)).expanduser())
    case["bundle_path"] = str(bundle_dir)
    case["case_id"] = case.get("case_id") or f"{case['date']}-{case['slug']}"


def normalize_stage_payload(note: dict, raw: dict | None) -> dict:
    stage_id = note["id"]
    block_key = note["block_key"]
    value = unwrap_raw(raw, block_key)
    status = value.get("status", "pending")
    base = {
        "status": status,
        "narrative": value.get("narrative", ""),
        "key_points": ensure_list(value.get("key_points")),
        "decisions": ensure_list(value.get("decisions")),
        "open_questions": ensure_list(value.get("open_questions")),
        "next_actions": ensure_list(value.get("next_actions")),
    }
    if stage_id == "preprocess":
        block = {
            "status": status,
            "agent_mode": value.get("agent_mode", "parent"),
            "support_agent_findings": ensure_list(value.get("support_agent_findings")),
            "user_stated_request": value.get("user_stated_request", ""),
            "ambiguity_points": ensure_list(value.get("ambiguity_points")),
            "dubious_claims": ensure_list(value.get("dubious_claims")),
            "factual_gaps": ensure_list(value.get("factual_gaps")),
            "hidden_assumptions": ensure_list(value.get("hidden_assumptions")),
            "suspected_real_goals": ensure_list(value.get("suspected_real_goals")),
            "scenario_fragments": ensure_list(value.get("scenario_fragments")),
            "success_signals": ensure_list(value.get("success_signals")),
            "non_goals": ensure_list(value.get("non_goals")),
            "follow_up_questions": ensure_list(value.get("follow_up_questions")),
            "blocking_unknowns": ensure_list(value.get("blocking_unknowns")),
            "reframed_request": value.get("reframed_request", ""),
            "evidence_refs": ensure_list(value.get("evidence_refs")),
        }
    elif stage_id == "divergence":
        block = {
            "status": status,
            "options": ensure_list(value.get("options")),
            "decision_criteria": ensure_list(value.get("decision_criteria")),
            "dropped_options": ensure_list(value.get("dropped_options")),
            "retained_option_id": value.get("retained_option_id", ""),
        }
    elif stage_id == "requirements":
        block = {
            "status": status,
            "requirement_units": ensure_list(value.get("requirement_units")),
            "interface_contracts": ensure_list(value.get("interface_contracts")),
            "success_criteria": ensure_list(value.get("success_criteria")),
            "validation_targets": ensure_list(value.get("validation_targets")),
            "non_goals": ensure_list(value.get("non_goals")),
            "frozen_terms": ensure_list(value.get("frozen_terms")),
        }
    elif stage_id == "critique":
        block = {
            "status": status,
            "agent_mode": value.get("agent_mode", "pending"),
            "subagent_findings": ensure_list(value.get("subagent_findings")),
            "critique_findings": ensure_list(value.get("critique_findings")),
            "orthogonal_axes": ensure_list(value.get("orthogonal_axes")),
            "conflicts": ensure_list(value.get("conflicts")),
            "dropped_requirements": ensure_list(value.get("dropped_requirements")),
            "resolution_decisions": ensure_list(value.get("resolution_decisions")),
        }
    elif stage_id == "closure":
        block = {
            "status": status,
            "end_to_end_chain": ensure_list(value.get("end_to_end_chain")),
            "dependency_gaps": ensure_list(value.get("dependency_gaps")),
            "completions": ensure_list(value.get("completions")),
            "unresolved_dependencies": ensure_list(value.get("unresolved_dependencies")),
        }
    elif stage_id == "probes":
        block = {
            "status": status,
            "probes": ensure_list(value.get("probes")),
            "discarded_paths": ensure_list(value.get("discarded_paths")),
            "surviving_paths": ensure_list(value.get("surviving_paths")),
            "open_probe_limits": ensure_list(value.get("open_probe_limits")),
        }
    elif stage_id == "red_blue":
        block = {
            "status": status,
            "agent_mode": value.get("agent_mode", "pending"),
            "subagent_findings": ensure_list(value.get("subagent_findings")),
            "attack_vectors": ensure_list(value.get("attack_vectors")),
            "mitigations": ensure_list(value.get("mitigations")),
            "residual_risks": ensure_list(value.get("residual_risks")),
            "unresolved_attacks": ensure_list(value.get("unresolved_attacks")),
        }
    elif stage_id == "review":
        block = {
            "status": status,
            "agent_mode": value.get("agent_mode", "pending"),
            "subagent_findings": ensure_list(value.get("subagent_findings")),
            "verdict": value.get("verdict", ""),
            "approval_conditions": ensure_list(value.get("approval_conditions")),
            "blockers": ensure_list(value.get("blockers")),
            "rationale": ensure_list(value.get("rationale")),
            "reentry_stage_if_rejected": value.get("reentry_stage_if_rejected", ""),
        }
    elif stage_id == "compile_for_code":
        block = {
            "status": status,
            "agent_mode": value.get("agent_mode", "pending"),
            "subagent_findings": ensure_list(value.get("subagent_findings")),
            "code_ready": bool(value.get("code_ready", False)),
            "blocking_gaps": ensure_list(value.get("blocking_gaps")),
            "frozen_contract_refs": ensure_list(value.get("frozen_contract_refs")),
            "compiled_review_conditions": ensure_list(value.get("compiled_review_conditions")),
            "repo_targets": ensure_list(value.get("repo_targets")),
            "execution_manifest_ref": value.get("execution_manifest_ref", "95-execution-manifest.md"),
            "handoff_entry": value.get("handoff_entry", "99-code-handoff.md"),
            "reopen_stage_if_blocked": value.get("reopen_stage_if_blocked", "J"),
        }
    else:
        raise ValueError(f"Unsupported stage: {stage_id}")
    return {**base, "block": {block_key: block}}


def normalize_artifact_payload(note: dict, raw: dict | None, case: dict) -> dict:
    artifact_id = note["id"]
    block_key = note["block_key"]
    value = unwrap_raw(raw, block_key)
    status = value.get("status", "pending")
    base = {
        "status": status,
        "narrative": value.get("narrative", ""),
        "key_points": ensure_list(value.get("key_points")),
        "decisions": ensure_list(value.get("decisions")),
        "open_questions": ensure_list(value.get("open_questions")),
        "next_actions": ensure_list(value.get("next_actions")),
    }
    if artifact_id == "constraint_ledger":
        block = {
            "status": status,
            "retained_goal": value.get("retained_goal", ""),
            "confirmed_facts": ensure_list(value.get("confirmed_facts")),
            "challenged_claims": ensure_list(value.get("challenged_claims")),
            "frozen_constraints": ensure_list(value.get("frozen_constraints")),
            "dropped_options": ensure_list(value.get("dropped_options")),
            "risks": ensure_list(value.get("risks")),
            "dependency_chain": ensure_list(value.get("dependency_chain")),
            "verification_semantics": ensure_list(value.get("verification_semantics")),
            "stage_refs": ensure_list(value.get("stage_refs")),
            "handoff_ref": value.get("handoff_ref", "90-code-handoff.md"),
        }
    elif artifact_id == "code_handoff":
        repo_targets = ensure_list(value.get("repo_targets"))
        if not repo_targets and case.get("repo_paths"):
            repo_targets = ensure_list(case.get("repo_paths"))
        block = {
            "status": status,
            "code_ready": bool(value.get("code_ready", False)),
            "handoff_summary": value.get("handoff_summary", ""),
            "retained_goal": value.get("retained_goal", ""),
            "implementation_scope": ensure_list(value.get("implementation_scope")),
            "repo_targets": repo_targets,
            "repo_grounding": ensure_list(value.get("repo_grounding")),
            "read_first": ensure_list(value.get("read_first")),
            "frozen_product_decisions": ensure_list(value.get("frozen_product_decisions")),
            "domain_model": ensure_list(value.get("domain_model")),
            "data_contract": ensure_list(value.get("data_contract")),
            "ui_contract": ensure_list(value.get("ui_contract")),
            "function_contracts": ensure_list(value.get("function_contracts")),
            "file_plan": ensure_list(value.get("file_plan")),
            "implementation_units": ensure_list(value.get("implementation_units")),
            "verification_commands": ensure_list(value.get("verification_commands")),
            "browser_checks": ensure_list(value.get("browser_checks")),
            "acceptance_checks": ensure_list(value.get("acceptance_checks")),
            "allowed_decisions": ensure_list(value.get("allowed_decisions")),
            "forbidden_decisions": ensure_list(value.get("forbidden_decisions")),
            "reentry_triggers": ensure_list(value.get("reentry_triggers")),
            "reopen_stage_map": ensure_list(value.get("reopen_stage_map")),
            "unresolved_gaps": ensure_list(value.get("unresolved_gaps")),
        }
    elif artifact_id == "canonical_contracts":
        block = {
            "status": status,
            "contracts": ensure_list(value.get("contracts")),
        }
    elif artifact_id == "constraint_crosswalk":
        block = {
            "status": status,
            "crosswalk_rows": ensure_list(value.get("crosswalk_rows")),
        }
    elif artifact_id == "execution_manifest":
        block = {
            "status": status,
            "phases": ensure_list(value.get("phases")),
            "scaffold_blueprint": ensure_list(value.get("scaffold_blueprint")),
        }
    elif artifact_id == "code_batches":
        block = {
            "status": status,
            "batches": ensure_list(value.get("batches")),
        }
    elif artifact_id == "code_preflight":
        block = {
            "status": status,
            "confirmed": ensure_list(value.get("confirmed")),
            "do_not_reinvent": ensure_list(value.get("do_not_reinvent")),
            "do_first": ensure_list(value.get("do_first")),
            "context_bundle": ensure_list(value.get("context_bundle")),
            "progress_snapshot": value.get("progress_snapshot", {}),
            "current_focus": value.get("current_focus", ""),
            "remaining_work": ensure_list(value.get("remaining_work")),
            "pause_conditions": ensure_list(value.get("pause_conditions")),
            "session_notes": ensure_list(value.get("session_notes")),
        }
    elif artifact_id == "final_handoff":
        block = {
            "status": status,
            "code_ready": bool(value.get("code_ready", False)),
            "handoff_entry": value.get("handoff_entry", "90-code-handoff.md"),
            "direct_code_command": value.get("direct_code_command", ""),
            "blocking_gaps": ensure_list(value.get("blocking_gaps")),
            "repo_absent_policy": value.get("repo_absent_policy", ""),
            "mandatory_multi_agent_stage_blocked": bool(value.get("mandatory_multi_agent_stage_blocked", False)),
            "next_step": value.get("next_step", ""),
        }
    else:
        raise ValueError(f"Unsupported artifact: {artifact_id}")
    return {**base, "block": {block_key: block}}


def build_overview_content(case: dict, bundle_dir: Path, stage_notes: list[dict], artifact_notes: list[dict], language: str) -> str:
    stage_statuses = {
        note["id"]: note["payload"]["block"][note["block_key"]].get("status", "pending")
        for note in stage_notes
    }
    artifact_statuses = {
        note["id"]: note["payload"]["block"][note["block_key"]].get("status", "pending")
        for note in artifact_notes
    }
    handoff_ref = "90-code-handoff.md"
    overview_block = {
        "ecl.case": {
            "bundle_version": case["bundle_version"],
            "case_id": case["case_id"],
            "title": case["title"],
            "slug": case["slug"],
            "date": case["date"],
            "mode": case["mode"],
            "source_request": case["source_request"],
            "request_language": case["request_language"],
            "output_language": case["output_language"],
            "final_outcome": case.get("final_outcome") or OVERVIEW_DEFAULTS["final_outcome"][language],
            "vault_root": case["vault_root"],
            "bundle_path": str(bundle_dir),
            "project_paths": ensure_list(case.get("project_paths")),
            "repo_paths": ensure_list(case.get("repo_paths")),
            "stage_statuses": stage_statuses,
            "artifact_statuses": artifact_statuses,
            "handoff_ref": handoff_ref,
        }
    }
    parts = [
        frontmatter(
            {
                "title": case["title"],
                "case": case["title"],
                "stage": "overview",
                "stage_key": "overview",
                "status": "complete",
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {case['title']}",
        "",
        f"## {tr(language, 'summary')}",
        case.get("summary") or OVERVIEW_DEFAULTS["summary"][language],
        "",
        f"## {tr(language, 'source_request')}",
        case["source_request"],
        "",
        f"## {tr(language, 'final_outcome')}",
        overview_block["ecl.case"]["final_outcome"],
        "",
        f"## {tr(language, 'stage_status_index')}",
        "\n".join(f"- `{note['letter']}` / `{note['id']}`: `{stage_statuses[note['id']]}`" for note in stage_notes),
        "",
        f"## {tr(language, 'paths')}",
        f"- {tr(language, 'vault_root')}: `{case['vault_root']}`",
        f"- {tr(language, 'bundle_path')}: `{bundle_dir}`",
        f"- {tr(language, 'project_paths')}: {', '.join(f'`{path}`' for path in ensure_list(case.get('project_paths'))) or tr(language, 'none_recorded')}",
        f"- {tr(language, 'repo_paths')}: {', '.join(f'`{path}`' for path in ensure_list(case.get('repo_paths'))) or tr(language, 'none_recorded')}",
        "",
        f"## {tr(language, 'structured_block')}",
        "```json",
        json.dumps(overview_block, ensure_ascii=False, indent=2),
        "```",
        "",
    ]
    return "\n".join(parts)


def stage_navigation(stage_notes: list[dict], index: int, language: str) -> str:
    parts = ["[[00-overview]]"]
    if index > 0:
        parts.append(f"{tr(language, 'prev')}: [[{Path(stage_notes[index - 1]['filename']).stem}]]")
    if index + 1 < len(stage_notes):
        parts.append(f"{tr(language, 'next')}: [[{Path(stage_notes[index + 1]['filename']).stem}]]")
    return " | ".join(parts)


def format_section(title: str, items, language: str) -> list[str]:
    return [f"## {title}", markdown_list(items, language), ""]


def format_stage_content(case_title: str, note: dict, payload: dict, stage_notes: list[dict], index: int, language: str) -> str:
    stage_id = note["id"]
    block = payload["block"][note["block_key"]]
    parts = [
        frontmatter(
            {
                "title": f"{note['letter']}. {stage_title(stage_id, language)}",
                "case": case_title,
                "stage": note["letter"],
                "stage_key": stage_id,
                "status": block.get("status", "pending"),
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {note['letter']}. {stage_title(stage_id, language)}",
        "",
        stage_navigation(stage_notes, index, language),
        "",
        f"## {tr(language, 'goal')}",
        STAGE_GOALS.get(language, STAGE_GOALS["en"]).get(stage_id, ""),
        "",
        f"## {tr(language, 'narrative')}",
        payload["narrative"] or tr(language, "pending"),
        "",
        f"## {tr(language, 'key_points')}",
        markdown_list(payload["key_points"], language),
        "",
        f"## {tr(language, 'decisions')}",
        markdown_list(payload["decisions"], language),
        "",
        f"## {tr(language, 'open_questions')}",
        markdown_list(payload["open_questions"], language),
        "",
        f"## {tr(language, 'next_actions')}",
        markdown_list(payload["next_actions"], language),
        "",
    ]

    stage_sections = {
        "preprocess": [
            ("user_stated_request", block.get("user_stated_request")),
            ("ambiguity_points", block.get("ambiguity_points")),
            ("dubious_claims", block.get("dubious_claims")),
            ("factual_gaps", block.get("factual_gaps")),
            ("hidden_assumptions", block.get("hidden_assumptions")),
            ("suspected_real_goals", block.get("suspected_real_goals")),
            ("scenario_fragments", block.get("scenario_fragments")),
            ("success_signals", block.get("success_signals")),
            ("non_goals", block.get("non_goals")),
            ("follow_up_questions", block.get("follow_up_questions")),
            ("blocking_unknowns", block.get("blocking_unknowns")),
        ],
        "divergence": [
            ("options", block.get("options")),
            ("decision_criteria", block.get("decision_criteria")),
            ("dropped_options", block.get("dropped_options")),
            ("retained_option_id", block.get("retained_option_id")),
        ],
        "requirements": [
            ("requirement_units", block.get("requirement_units")),
            ("interface_contracts", block.get("interface_contracts")),
            ("success_criteria", block.get("success_criteria")),
            ("validation_targets", block.get("validation_targets")),
            ("non_goals", block.get("non_goals")),
            ("frozen_terms", block.get("frozen_terms")),
        ],
        "critique": [
            ("critique_findings", block.get("critique_findings")),
            ("orthogonal_axes", block.get("orthogonal_axes")),
            ("conflicts", block.get("conflicts")),
            ("dropped_requirements", block.get("dropped_requirements")),
            ("resolution_decisions", block.get("resolution_decisions")),
        ],
        "closure": [
            ("end_to_end_chain", block.get("end_to_end_chain")),
            ("dependency_gaps", block.get("dependency_gaps")),
            ("completions", block.get("completions")),
            ("unresolved_dependencies", block.get("unresolved_dependencies")),
        ],
        "probes": [
            ("probes", block.get("probes")),
            ("discarded_paths", block.get("discarded_paths")),
            ("surviving_paths", block.get("surviving_paths")),
            ("open_probe_limits", block.get("open_probe_limits")),
        ],
        "red_blue": [
            ("attack_vectors", block.get("attack_vectors")),
            ("mitigations", block.get("mitigations")),
            ("residual_risks", block.get("residual_risks")),
            ("unresolved_attacks", block.get("unresolved_attacks")),
        ],
        "review": [
            ("verdict", block.get("verdict")),
            ("approval_conditions", block.get("approval_conditions")),
            ("blockers", block.get("blockers")),
            ("rationale", block.get("rationale")),
            ("reentry_stage_if_rejected", block.get("reentry_stage_if_rejected")),
        ],
        "compile_for_code": [
            ("code_ready", block.get("code_ready")),
            ("blocking_gaps", block.get("blocking_gaps")),
            ("frozen_contract_refs", block.get("frozen_contract_refs")),
            ("compiled_review_conditions", block.get("compiled_review_conditions")),
            ("repo_targets", block.get("repo_targets")),
            ("execution_manifest_ref", block.get("execution_manifest_ref")),
            ("handoff_entry", block.get("handoff_entry")),
            ("reopen_stage_if_blocked", block.get("reopen_stage_if_blocked")),
        ],
    }

    for title_key, content in stage_sections[stage_id]:
        heading = tr(language, title_key)
        if isinstance(content, list):
            parts.extend(format_section(heading, content, language))
        else:
            parts.extend([f"## {heading}", f"- {content or tr(language, 'none_recorded')}", ""])

    parts.extend(
        [
            f"## {tr(language, 'structured_block')}",
            "```json",
            json.dumps(payload["block"], ensure_ascii=False, indent=2),
            "```",
            "",
        ]
    )
    return "\n".join(parts)


def format_artifact_content(case_title: str, note: dict, payload: dict, language: str) -> str:
    artifact_id = note["id"]
    block = payload["block"][note["block_key"]]
    narrative_fallback = tr(language, "none_recorded") if block.get("status") == "complete" else tr(language, "pending")
    parts = [
        frontmatter(
            {
                "title": artifact_title(artifact_id, language),
                "case": case_title,
                "stage": "artifact",
                "stage_key": artifact_id,
                "status": block.get("status", "pending"),
                "generated_by": "evolution-constraint-planner",
            }
        ),
        f"# {artifact_title(artifact_id, language)}",
        "",
        "[[00-overview]]",
        "",
        f"## {tr(language, 'goal')}",
        ARTIFACT_GOALS.get(language, ARTIFACT_GOALS["en"]).get(artifact_id, ""),
        "",
        f"## {tr(language, 'narrative')}",
        payload["narrative"] or narrative_fallback,
        "",
        f"## {tr(language, 'key_points')}",
        markdown_list(payload["key_points"], language),
        "",
        f"## {tr(language, 'decisions')}",
        markdown_list(payload["decisions"], language),
        "",
    ]
    if artifact_id != "code_handoff":
        parts.extend(
            [
                f"## {tr(language, 'open_questions')}",
                markdown_list(payload["open_questions"], language),
                "",
                f"## {tr(language, 'next_actions')}",
                markdown_list(payload["next_actions"], language),
                "",
            ]
        )
    else:
        parts.extend(
            [
                f"## {tr(language, 'next_actions')}",
                markdown_list(payload["next_actions"], language),
                "",
            ]
        )
    if artifact_id == "constraint_ledger":
        for title_key in [
            "retained_goal",
            "confirmed_facts",
            "challenged_claims",
            "frozen_constraints",
            "dropped_options",
            "risks",
            "dependency_chain",
            "verification_semantics",
            "handoff_ref",
        ]:
            content = block.get(title_key)
            heading = tr(language, title_key)
            if isinstance(content, list):
                parts.extend(format_section(heading, content, language))
            else:
                parts.extend([f"## {heading}", f"- {content or tr(language, 'none_recorded')}", ""])
    elif artifact_id == "code_handoff":
        for title_key in [
            "code_ready",
            "handoff_summary",
            "retained_goal",
            "implementation_scope",
            "repo_targets",
            "repo_grounding",
            "read_first",
            "frozen_product_decisions",
            "domain_model",
            "data_contract",
            "ui_contract",
            "function_contracts",
            "file_plan",
            "implementation_units",
            "verification_commands",
            "browser_checks",
            "acceptance_checks",
            "allowed_decisions",
            "forbidden_decisions",
            "reentry_triggers",
            "reopen_stage_map",
            "unresolved_gaps",
        ]:
            content = block.get(title_key)
            heading = tr(language, title_key)
            if isinstance(content, list):
                parts.extend(format_section(heading, content, language))
            else:
                value = str(content).lower() if isinstance(content, bool) else (content or tr(language, "none_recorded"))
                parts.extend([f"## {heading}", f"- {value}", ""])
    elif artifact_id == "canonical_contracts":
        parts.extend(format_section(tr(language, "contracts"), block.get("contracts"), language))
    elif artifact_id == "constraint_crosswalk":
        parts.extend(format_section(tr(language, "crosswalk_rows"), block.get("crosswalk_rows"), language))
    elif artifact_id == "execution_manifest":
        parts.extend(format_section(tr(language, "phases"), block.get("phases"), language))
        parts.extend(format_section(tr(language, "scaffold_blueprint"), block.get("scaffold_blueprint"), language))
    elif artifact_id == "code_batches":
        parts.extend(format_section(tr(language, "batches"), block.get("batches"), language))
    elif artifact_id == "code_preflight":
        parts.extend(format_section(tr(language, "confirmed"), block.get("confirmed"), language))
        parts.extend(format_section(tr(language, "do_not_reinvent"), block.get("do_not_reinvent"), language))
        parts.extend(format_section(tr(language, "do_first"), block.get("do_first"), language))
        parts.extend(format_section(tr(language, "context_bundle"), block.get("context_bundle"), language))
        content = block.get("progress_snapshot")
        heading = tr(language, "progress_snapshot")
        if isinstance(content, dict):
            rendered = json.dumps(content, ensure_ascii=False, indent=2) if content else "{}"
            parts.extend([f"## {heading}", "```json", rendered, "```", ""])
        else:
            parts.extend([f"## {heading}", f"- {content or tr(language, 'none_recorded')}", ""])
        parts.extend(format_section(tr(language, "current_focus"), block.get("current_focus"), language))
        parts.extend(format_section(tr(language, "remaining_work"), block.get("remaining_work"), language))
        parts.extend(format_section(tr(language, "pause_conditions"), block.get("pause_conditions"), language))
        parts.extend(format_section(tr(language, "session_notes"), block.get("session_notes"), language))
    elif artifact_id == "final_handoff":
        for title_key in [
            "code_ready",
            "handoff_entry",
            "direct_code_command",
            "blocking_gaps",
            "repo_absent_policy",
            "mandatory_multi_agent_stage_blocked",
            "next_step",
        ]:
            content = block.get(title_key)
            heading = tr(language, title_key)
            if isinstance(content, list):
                parts.extend(format_section(heading, content, language))
            else:
                value = str(content).lower() if isinstance(content, bool) else (content or tr(language, "none_recorded"))
                parts.extend([f"## {heading}", f"- {value}", ""])
    parts.extend(
        [
            f"## {tr(language, 'structured_block')}",
            "```json",
            json.dumps(payload["block"], ensure_ascii=False, indent=2),
            "```",
            "",
        ]
    )
    return "\n".join(parts)


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Render a normalized ECL v2 JSON file into Obsidian notes.")
    parser.add_argument("input_json", help="Path to normalized ECL JSON input")
    parser.add_argument("--output", help="Explicit output directory.")
    parser.add_argument("--force", action="store_true", help="Overwrite an existing output directory.")
    args = parser.parse_args()

    input_path = Path(args.input_json).expanduser().resolve()
    if not input_path.exists():
        print(f"[ERROR] Input JSON not found: {input_path}")
        return 1

    try:
        case = json.loads(input_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"[ERROR] Invalid JSON: {exc}")
        return 1

    if not isinstance(case, dict):
        print("[ERROR] Input JSON must contain an object at the top level.")
        return 1
    if not case.get("title"):
        print("[ERROR] Input JSON must include 'title'.")
        return 1
    if not case.get("source_request"):
        print("[ERROR] Input JSON must include 'source_request'.")
        return 1

    schema_notes = load_schema(Path(__file__).resolve())
    _, output_language = resolve_languages(case)
    output_root = Path(case.get("output_root", DEFAULT_OUTPUT_ROOT)).expanduser()
    bundle_dir = (
        Path(args.output).expanduser().resolve()
        if args.output
        else (output_root / f"{case.get('date') or date.today().isoformat()}-{case.get('slug') or slugify(case['title'])}").resolve()
    )

    if bundle_dir.exists():
        if not args.force:
            print(f"[ERROR] Output directory already exists: {bundle_dir}")
            print("        Re-run with --force to overwrite.")
            return 1
    else:
        bundle_dir.mkdir(parents=True, exist_ok=True)

    normalize_case(case, bundle_dir)

    raw_stages = case.get("stages", {})
    raw_artifacts = case.get("artifacts", {})
    stage_notes = []
    artifact_notes = []
    for note in schema_notes:
        current = dict(note)
        if note["kind"] == "stage":
            current["payload"] = normalize_stage_payload(note, raw_stages.get(note["id"]))
            stage_notes.append(current)
        elif note["kind"] == "artifact" and note["id"] != "overview":
            current["payload"] = normalize_artifact_payload(note, raw_artifacts.get(note["id"]), case)
            artifact_notes.append(current)

    write_text(
        bundle_dir / "00-overview.md",
        build_overview_content(case, bundle_dir, stage_notes, artifact_notes, output_language),
    )

    for note in artifact_notes:
        write_text(
            bundle_dir / note["filename"],
            format_artifact_content(case["title"], note, note["payload"], output_language),
        )

    for index, note in enumerate(stage_notes):
        write_text(
            bundle_dir / note["filename"],
            format_stage_content(case["title"], note, note["payload"], stage_notes, index, output_language),
        )

    print(f"[OK] Rendered bundle: {bundle_dir}")
    print("[OK] Generated files:")
    print("     00-overview.md")
    for note in artifact_notes:
        print(f"     {note['filename']}")
    for note in stage_notes:
        print(f"     {note['filename']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
