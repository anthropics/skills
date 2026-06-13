#!/usr/bin/env python3
"""
Validate a rendered ECL v2 Obsidian bundle.
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
OPEN_QUESTION_PATTERN = re.compile(
    r"(TODO|TBD|open question|开放问题|待确认|由实现者决定|implementer decides?)",
    re.IGNORECASE,
)

STAGES = [
    ("preprocess", "10-a-preprocess.md", "ecl.preprocess", "A"),
    ("divergence", "20-b-divergence.md", "ecl.options", "B"),
    ("requirements", "30-c-requirements.md", "ecl.requirements", "C"),
    ("critique", "40-d-critique.md", "ecl.conflicts", "D"),
    ("closure", "50-e-closure.md", "ecl.dependencies", "E"),
    ("probes", "60-f-probes.md", "ecl.probes", "F"),
    ("red_blue", "70-g-red-blue.md", "ecl.adversarial", "G"),
    ("review", "80-h-review.md", "ecl.review", "H"),
    ("compile_for_code", "98-j-compile-for-code.md", "ecl.compile_for_code", "J"),
]

ARTIFACTS = [
    ("constraint_ledger", "05-constraint-ledger.md", "ecl.constraint_ledger"),
    ("code_handoff", "90-code-handoff.md", "ecl.code_handoff"),
    ("canonical_contracts", "91-canonical-contracts.md", "ecl.canonical_contracts"),
    ("constraint_crosswalk", "92-constraint-crosswalk.md", "ecl.constraint_crosswalk"),
    ("execution_manifest", "95-execution-manifest.md", "ecl.execution_manifest"),
    ("code_batches", "96-code-batches.md", "ecl.code_batches"),
    ("code_preflight", "97-code-preflight.md", "ecl.code_preflight"),
    ("final_handoff", "99-code-handoff.md", "ecl.final_handoff"),
]

RUN_REQUIRED_ARTIFACTS = [
    ("code_run", "00-code-run.md", "ecl.code_run"),
    ("code_verification", "01-verification.md", "ecl.code_verification"),
]

RUN_OPTIONAL_ARTIFACTS = [
    ("reentry_request", "02-reentry.md", "ecl.reentry_request"),
    ("achieve", "03-achieve.md", "ecl.achieve"),
]

MANDATORY_AGENT_STAGES = {"critique", "red_blue", "review", "compile_for_code"}
ALLOWED_STATUSES = {"pending", "in_progress", "complete", "blocked_by_agent_unavailable", "rejected"}
ALLOWED_VERDICTS = {"approved", "approved_with_conditions", "rejected"}
ALLOWED_RUN_OUTCOMES = {
    "completed",
    "completed_with_low_impact_fixes",
    "blocked_for_reentry",
    "refused_by_gate",
}
BLOCKING_RUN_OUTCOMES = {"blocked_for_reentry", "refused_by_gate"}
ALLOWED_REENTRY_STAGES = {"A", "B", "C", "D", "E", "F", "G", "H", "J"}
ALLOWED_ACHIEVE_VERDICTS = {"achieved", "achieved_with_followups", "not_achieved"}
ALLOWED_ARCHIVE_STATUSES = {"archived", "left_open"}

REQUIRED_FIELDS = {
    "ecl.case": [
        "bundle_version",
        "case_id",
        "title",
        "slug",
        "date",
        "mode",
        "source_request",
        "request_language",
        "output_language",
        "final_outcome",
        "vault_root",
        "bundle_path",
        "project_paths",
        "repo_paths",
        "stage_statuses",
        "artifact_statuses",
        "handoff_ref",
    ],
    "ecl.constraint_ledger": [
        "status",
        "retained_goal",
        "confirmed_facts",
        "challenged_claims",
        "frozen_constraints",
        "dropped_options",
        "risks",
        "dependency_chain",
        "verification_semantics",
        "stage_refs",
        "handoff_ref",
    ],
    "ecl.preprocess": [
        "status",
        "agent_mode",
        "support_agent_findings",
        "user_stated_request",
        "ambiguity_points",
        "dubious_claims",
        "factual_gaps",
        "hidden_assumptions",
        "suspected_real_goals",
        "scenario_fragments",
        "success_signals",
        "non_goals",
        "follow_up_questions",
        "blocking_unknowns",
        "reframed_request",
        "evidence_refs",
    ],
    "ecl.options": [
        "status",
        "options",
        "decision_criteria",
        "dropped_options",
        "retained_option_id",
    ],
    "ecl.requirements": [
        "status",
        "requirement_units",
        "interface_contracts",
        "success_criteria",
        "validation_targets",
        "non_goals",
        "frozen_terms",
    ],
    "ecl.conflicts": [
        "status",
        "agent_mode",
        "subagent_findings",
        "critique_findings",
        "orthogonal_axes",
        "conflicts",
        "dropped_requirements",
        "resolution_decisions",
    ],
    "ecl.dependencies": [
        "status",
        "end_to_end_chain",
        "dependency_gaps",
        "completions",
        "unresolved_dependencies",
    ],
    "ecl.probes": [
        "status",
        "probes",
        "discarded_paths",
        "surviving_paths",
        "open_probe_limits",
    ],
    "ecl.adversarial": [
        "status",
        "agent_mode",
        "subagent_findings",
        "attack_vectors",
        "mitigations",
        "residual_risks",
        "unresolved_attacks",
    ],
    "ecl.review": [
        "status",
        "agent_mode",
        "subagent_findings",
        "verdict",
        "approval_conditions",
        "blockers",
        "rationale",
        "reentry_stage_if_rejected",
    ],
    "ecl.compile_for_code": [
        "status",
        "agent_mode",
        "subagent_findings",
        "code_ready",
        "blocking_gaps",
        "frozen_contract_refs",
        "compiled_review_conditions",
        "repo_targets",
        "execution_manifest_ref",
        "handoff_entry",
        "reopen_stage_if_blocked",
    ],
    "ecl.code_handoff": [
        "status",
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
    ],
    "ecl.canonical_contracts": [
        "status",
        "contracts",
    ],
    "ecl.constraint_crosswalk": [
        "status",
        "crosswalk_rows",
    ],
    "ecl.execution_manifest": [
        "status",
        "phases",
        "scaffold_blueprint",
    ],
    "ecl.code_batches": [
        "status",
        "batches",
    ],
    "ecl.code_preflight": [
        "status",
        "confirmed",
        "do_not_reinvent",
        "do_first",
    ],
    "ecl.final_handoff": [
        "status",
        "code_ready",
        "handoff_entry",
        "direct_code_command",
        "blocking_gaps",
        "repo_absent_policy",
        "mandatory_multi_agent_stage_blocked",
        "next_step",
    ],
    "ecl.code_run": [
        "status",
        "run_id",
        "case_id",
        "handoff_ref",
        "entry_repo",
        "selected_units",
        "changed_files",
        "outcome",
    ],
    "ecl.code_verification": [
        "status",
        "run_id",
        "commands_run",
        "results",
        "failed_checks",
        "evidence_refs",
    ],
    "ecl.reentry_request": [
        "status",
        "run_id",
        "recommended_reopen_stage",
        "reason_class",
        "blocking_evidence",
        "must_freeze_before_resume",
    ],
    "ecl.achieve": [
        "status",
        "run_id",
        "verdict",
        "archive_status",
        "archive_reason",
        "acceptance_results",
        "verification_summary",
        "residual_issues",
        "next_actions",
        "archive_refs",
        "evidence_refs",
    ],
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


def ensure_list(value):
    if value is None:
        return []
    if isinstance(value, list):
        return value
    return [value]


def is_empty(value) -> bool:
    if value is None:
        return True
    if isinstance(value, str):
        return not value.strip()
    if isinstance(value, (list, tuple, dict, set)):
        return len(value) == 0
    return False


def require_fields(label: str, block_key: str, block: dict, errors: list[str]) -> None:
    for field in REQUIRED_FIELDS.get(block_key, []):
        if field not in block:
            errors.append(f"{label}: missing field '{field}' in {block_key}")


def validate_status(block: dict, label: str, errors: list[str]) -> None:
    status = block.get("status")
    if status not in ALLOWED_STATUSES:
        errors.append(f"{label}: invalid status '{status}'")


def validate_agent_stage(stage_key: str, block: dict, errors: list[str]) -> None:
    validate_status(block, stage_key, errors)
    if stage_key not in MANDATORY_AGENT_STAGES:
        return
    if block.get("status") == "complete":
        if block.get("agent_mode") == "blocked":
            errors.append(f"{stage_key}: complete stage cannot use agent_mode=blocked")
        if is_empty(block.get("subagent_findings")):
            errors.append(f"{stage_key}: complete stage must include subagent_findings")
    if block.get("status") == "blocked_by_agent_unavailable":
        if block.get("agent_mode") != "blocked":
            errors.append(f"{stage_key}: blocked_by_agent_unavailable requires agent_mode=blocked")


def validate_preprocess(block: dict, source_request: str, errors: list[str]) -> None:
    validate_status(block, "preprocess", errors)
    if block.get("status") != "complete":
        return
    if str(block.get("user_stated_request", "")) != str(source_request or ""):
        errors.append("preprocess: user_stated_request must match overview source_request")
    for field in ["suspected_real_goals", "follow_up_questions", "blocking_unknowns"]:
        if field not in block:
            errors.append(f"preprocess: missing field '{field}'")
    if not block.get("suspected_real_goals"):
        errors.append("preprocess: suspected_real_goals must be non-empty when complete")
    if is_empty(block.get("reframed_request")):
        errors.append("preprocess: reframed_request must be non-empty when complete")


def validate_options(block: dict, errors: list[str]) -> None:
    validate_status(block, "divergence", errors)
    if block.get("status") != "complete":
        return
    options = ensure_list(block.get("options"))
    if len(options) < 3:
        errors.append("divergence: complete stage must include at least three options")
    retained = 0
    retained_id = str(block.get("retained_option_id", "")).strip()
    for item in options:
        if not isinstance(item, dict):
            errors.append("divergence: each option must be an object")
            continue
        for field in ["id", "name", "summary", "covered_blind_spots", "tradeoffs", "key_constraints", "retained"]:
            if field not in item:
                errors.append(f"divergence: each option must include {field}")
        if item.get("retained") is True:
            retained += 1
            if retained_id and item.get("id") != retained_id:
                errors.append("divergence: retained_option_id must match the retained option card")
    if retained != 1:
        errors.append("divergence: complete stage must retain exactly one option")


def validate_requirements(block: dict, errors: list[str]) -> None:
    validate_status(block, "requirements", errors)
    if block.get("status") != "complete":
        return
    units = ensure_list(block.get("requirement_units"))
    if not units:
        errors.append("requirements: requirement_units must be non-empty when complete")
    for item in units:
        if not isinstance(item, dict):
            errors.append("requirements: each requirement unit must be an object")
            continue
        for field in ["id", "category", "statement", "rationale", "verification_hint"]:
            if is_empty(item.get(field)):
                errors.append(f"requirements: each requirement unit must include {field}")


def validate_conflicts(block: dict, errors: list[str]) -> None:
    validate_agent_stage("critique", block, errors)
    if block.get("status") != "complete":
        return
    if not block.get("critique_findings"):
        errors.append("critique: critique_findings must be non-empty when complete")
    if not block.get("resolution_decisions"):
        errors.append("critique: resolution_decisions must be non-empty when complete")


def validate_dependencies(block: dict, errors: list[str]) -> None:
    validate_status(block, "closure", errors)
    if block.get("status") != "complete":
        return
    gaps = ensure_list(block.get("dependency_gaps"))
    for item in gaps:
        if not isinstance(item, dict):
            errors.append("closure: each dependency gap must be an object")
            continue
        for field in ["gap", "status", "resolved_by"]:
            if is_empty(item.get(field)):
                errors.append(f"closure: each dependency gap must include {field}")
    if block.get("unresolved_dependencies"):
        errors.append("closure: complete bundles cannot retain unresolved_dependencies")


def validate_probes(block: dict, errors: list[str]) -> None:
    validate_status(block, "probes", errors)
    if block.get("status") != "complete":
        return
    probes = ensure_list(block.get("probes"))
    if not probes:
        errors.append("probes: probes must be non-empty when complete")
    for probe in probes:
        if not isinstance(probe, dict):
            errors.append("probes: each probe must be an object")
            continue
        for field in [
            "id",
            "hypothesis",
            "method",
            "artifact_or_code",
            "expected_signal",
            "kill_criteria",
            "result_status",
            "result_summary",
            "evidence_refs",
        ]:
            if field not in probe:
                errors.append(f"probes: each probe must include {field}")
        if is_empty(probe.get("result_summary")):
            errors.append("probes: each probe must include a result_summary or inability-to-probe explanation")


def validate_adversarial(block: dict, errors: list[str]) -> None:
    validate_agent_stage("red_blue", block, errors)
    if block.get("status") != "complete":
        return
    if not block.get("attack_vectors"):
        errors.append("red_blue: attack_vectors must be non-empty when complete")
    if not block.get("mitigations") and not block.get("residual_risks"):
        errors.append("red_blue: complete stage must include mitigations or residual_risks")


def validate_review(block: dict, errors: list[str]) -> None:
    validate_agent_stage("review", block, errors)
    if block.get("status") != "complete":
        return
    verdict = block.get("verdict")
    if verdict not in ALLOWED_VERDICTS:
        errors.append("review: verdict must be approved, approved_with_conditions, or rejected")
        return
    if verdict == "approved_with_conditions" and not block.get("approval_conditions"):
        errors.append("review: approved_with_conditions requires approval_conditions")
    if verdict == "rejected" and not block.get("blockers"):
        errors.append("review: rejected requires blockers")
    if verdict == "rejected" and block.get("reentry_stage_if_rejected") not in ALLOWED_REENTRY_STAGES:
        errors.append("review: rejected requires a valid reentry_stage_if_rejected")


def validate_compile_for_code(block: dict, errors: list[str]) -> None:
    validate_agent_stage("compile_for_code", block, errors)
    if block.get("status") != "complete":
        return
    if block.get("code_ready") and is_empty(block.get("handoff_entry")):
        errors.append("compile_for_code: code_ready=true requires handoff_entry")
    if not block.get("code_ready") and is_empty(block.get("blocking_gaps")):
        errors.append("compile_for_code: code_ready=false requires blocking_gaps")


def validate_ledger(block: dict, errors: list[str]) -> None:
    validate_status(block, "constraint_ledger", errors)
    if block.get("status") != "complete":
        return
    if is_empty(block.get("retained_goal")):
        errors.append("constraint_ledger: retained_goal must be non-empty when complete")
    if is_empty(block.get("verification_semantics")):
        errors.append("constraint_ledger: verification_semantics must be non-empty when complete")


def validate_handoff(
    block: dict,
    note_path: Path,
    repo_paths: list[str],
    review_block: dict | None,
    errors: list[str],
) -> None:
    validate_status(block, "code_handoff", errors)
    content = note_path.read_text(encoding="utf-8")
    if OPEN_QUESTION_PATTERN.search(content):
        errors.append("code_handoff: must not contain TODO/TBD/open design questions")
    if block.get("status") != "complete":
        return
    code_ready = bool(block.get("code_ready"))
    if not repo_paths and code_ready:
        errors.append("code_handoff: repo_paths absent requires code_ready=false")
    if review_block and review_block.get("status") == "complete":
        if review_block.get("verdict") == "approved_with_conditions":
            for condition in ensure_list(review_block.get("approval_conditions")):
                rendered = json.dumps(block, ensure_ascii=False, sort_keys=True)
                if str(condition) not in rendered:
                    errors.append("code_handoff: every approval condition must be represented in the handoff")
        if review_block.get("verdict") == "rejected" and code_ready:
            errors.append("code_handoff: review rejected cannot produce code_ready=true")
    if not code_ready:
        return
    for field in [
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
    ]:
        if is_empty(block.get(field)):
            errors.append(f"code_handoff: code_ready=true requires non-empty {field}")
    if block.get("unresolved_gaps"):
        errors.append("code_handoff: code_ready=true requires unresolved_gaps to be empty")
    for item in ensure_list(block.get("function_contracts")):
        if not isinstance(item, dict):
            errors.append("code_handoff: each function contract must be an object")
            continue
        for field in [
            "id",
            "name",
            "kind",
            "location",
            "signature",
            "purpose",
            "inputs",
            "outputs",
            "side_effects",
            "invariants",
            "failure_modes",
        ]:
            if field not in item:
                errors.append(f"code_handoff: each function contract must include {field}")
    for item in ensure_list(block.get("file_plan")):
        if not isinstance(item, dict):
            errors.append("code_handoff: each file_plan item must be an object")
            continue
        for field in ["path", "action", "why", "depends_on"]:
            if field not in item:
                errors.append(f"code_handoff: each file_plan item must include {field}")
    for item in ensure_list(block.get("implementation_units")):
        if not isinstance(item, dict):
            errors.append("code_handoff: each implementation unit must be an object")
            continue
        for field in [
            "id",
            "title",
            "objective",
            "scope",
            "files",
            "functions",
            "depends_on",
            "verification",
            "done_when",
        ]:
            if field not in item:
                errors.append(f"code_handoff: each implementation unit must include {field}")
        for field in [
            "id",
            "title",
            "objective",
            "scope",
            "files",
            "functions",
            "verification",
            "done_when",
        ]:
            if is_empty(item.get(field)):
                errors.append(f"code_handoff: each implementation unit must have non-empty {field}")
    for item in ensure_list(block.get("reopen_stage_map")):
        if not isinstance(item, dict):
            errors.append("code_handoff: each reopen_stage_map item must be an object")
            continue
        if is_empty(item.get("trigger")):
            errors.append("code_handoff: each reopen_stage_map item must include trigger")
        if item.get("stage") not in ALLOWED_REENTRY_STAGES:
            errors.append("code_handoff: each reopen_stage_map stage must be A-J")


def validate_case_block(block: dict, errors: list[str]) -> None:
    if block.get("bundle_version") != 2:
        errors.append("case: bundle_version must be 2")
    if str(block.get("handoff_ref", "")).strip() != "90-code-handoff.md":
        errors.append("case: handoff_ref must be 90-code-handoff.md")


def validate_code_run(block: dict, case_id: str, errors: list[str]) -> None:
    validate_status(block, "code_run", errors)
    if block.get("status") != "complete":
        return
    if case_id and block.get("case_id") != case_id:
        errors.append("code_run: case_id must match overview case_id")
    if block.get("outcome") not in ALLOWED_RUN_OUTCOMES:
        errors.append("code_run: outcome must be supported")
    if block.get("outcome") != "refused_by_gate" and not block.get("selected_units"):
        errors.append("code_run: non-gate-refusal outcomes require selected_units")


def validate_code_verification(block: dict, run_id: str, errors: list[str]) -> None:
    validate_status(block, "code_verification", errors)
    if block.get("status") != "complete":
        return
    if block.get("run_id") != run_id:
        errors.append("code_verification: run_id must match code_run.run_id")


def validate_reentry_request(block: dict, run_id: str, errors: list[str]) -> None:
    validate_status(block, "reentry_request", errors)
    if block.get("status") != "complete":
        return
    if block.get("run_id") != run_id:
        errors.append("reentry_request: run_id must match code_run.run_id")
    if block.get("recommended_reopen_stage") not in ALLOWED_REENTRY_STAGES:
        errors.append("reentry_request: recommended_reopen_stage must be A-J")


def validate_achieve(block: dict, run_id: str, errors: list[str]) -> None:
    validate_status(block, "achieve", errors)
    if block.get("status") != "complete":
        return
    if block.get("run_id") != run_id:
        errors.append("achieve: run_id must match code_run.run_id")
    if block.get("verdict") not in ALLOWED_ACHIEVE_VERDICTS:
        errors.append("achieve: verdict must be achieved, achieved_with_followups, or not_achieved")
    if block.get("archive_status") not in ALLOWED_ARCHIVE_STATUSES:
        errors.append("achieve: archive_status must be archived or left_open")
    if block.get("verdict") == "not_achieved" and is_empty(block.get("residual_issues")):
        errors.append("achieve: not_achieved requires residual_issues")
    if block.get("verdict") in {"achieved", "achieved_with_followups"} and block.get("archive_status") != "archived":
        errors.append("achieve: accepted verdicts must archive the case")
    if block.get("verdict") == "not_achieved" and block.get("archive_status") != "left_open":
        errors.append("achieve: not_achieved must leave the case open")
    if block.get("archive_status") == "archived" and is_empty(block.get("archive_refs")):
        errors.append("achieve: archived cases require archive_refs")


def validate_final_handoff(block: dict, errors: list[str]) -> None:
    validate_status(block, "final_handoff", errors)
    if block.get("status") != "complete":
        return
    if block.get("code_ready") and is_empty(block.get("handoff_entry")):
        errors.append("final_handoff: code_ready=true requires handoff_entry")
    if not block.get("code_ready") and is_empty(block.get("blocking_gaps")):
        errors.append("final_handoff: code_ready=false requires blocking_gaps")


def validate_run_records(bundle_dir: Path, case_id: str, errors: list[str]) -> None:
    runs_dir = bundle_dir / "Runs"
    if not runs_dir.exists():
        return
    if not runs_dir.is_dir():
        errors.append("Runs: expected a directory when present")
        return
    for run_dir in sorted(path for path in runs_dir.iterdir() if path.is_dir()):
        parsed = {}
        for run_key, filename, block_key in RUN_REQUIRED_ARTIFACTS:
            note_path = run_dir / filename
            if not note_path.exists():
                errors.append(f"{run_dir.name}: missing {filename}")
                continue
            block = find_named_block(note_path, block_key)
            if not isinstance(block, dict):
                errors.append(f"{run_dir.name}/{filename}: structured block {block_key} must be an object")
                continue
            parsed[run_key] = block
            require_fields(f"{run_dir.name}/{run_key}", block_key, block, errors)
        optional_path = run_dir / "02-reentry.md"
        if optional_path.exists():
            block = find_named_block(optional_path, "ecl.reentry_request")
            if isinstance(block, dict):
                parsed["reentry_request"] = block
                require_fields(f"{run_dir.name}/reentry_request", "ecl.reentry_request", block, errors)
        achieve_path = run_dir / "03-achieve.md"
        if achieve_path.exists():
            block = find_named_block(achieve_path, "ecl.achieve")
            if isinstance(block, dict):
                parsed["achieve"] = block
                require_fields(f"{run_dir.name}/achieve", "ecl.achieve", block, errors)
        code_run = parsed.get("code_run")
        verification = parsed.get("code_verification")
        reentry = parsed.get("reentry_request")
        achieve = parsed.get("achieve")
        if code_run:
            validate_code_run(code_run, case_id, errors)
        if code_run and verification:
            validate_code_verification(verification, str(code_run.get("run_id", "")), errors)
        if code_run and reentry:
            validate_reentry_request(reentry, str(code_run.get("run_id", "")), errors)
        if code_run and achieve:
            validate_achieve(achieve, str(code_run.get("run_id", "")), errors)
        if not code_run:
            continue
        outcome = code_run.get("outcome")
        if outcome in BLOCKING_RUN_OUTCOMES and reentry is None:
            errors.append(f"{run_dir.name}: blocked or refused runs must include 02-reentry.md")
        if outcome not in BLOCKING_RUN_OUTCOMES and reentry is not None:
            errors.append(f"{run_dir.name}: successful runs must not include 02-reentry.md")


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate a rendered ECL v2 Obsidian bundle.")
    parser.add_argument("bundle_dir", help="Directory containing the Obsidian bundle")
    args = parser.parse_args()

    bundle_dir = Path(args.bundle_dir).expanduser().resolve()
    errors: list[str] = []

    if not bundle_dir.exists():
        print(f"[ERROR] Bundle directory not found: {bundle_dir}")
        return 1

    overview_path = bundle_dir / "00-overview.md"
    if not overview_path.exists():
        print("[ERROR] Bundle validation failed:")
        print("  - missing 00-overview.md")
        return 1

    case_block = find_named_block(overview_path, "ecl.case")
    if not isinstance(case_block, dict):
        print("[ERROR] Bundle validation failed:")
        print("  - overview: ecl.case must be an object")
        return 1
    require_fields("case", "ecl.case", case_block, errors)
    validate_case_block(case_block, errors)

    parsed_blocks: dict[str, dict] = {"case": case_block}
    stage_statuses = {}

    for artifact_key, filename, block_key in ARTIFACTS:
        note_path = bundle_dir / filename
        if not note_path.exists():
            errors.append(f"missing {filename}")
            continue
        block = find_named_block(note_path, block_key)
        if not isinstance(block, dict):
            errors.append(f"{filename}: structured block {block_key} must be an object")
            continue
        parsed_blocks[artifact_key] = block
        require_fields(artifact_key, block_key, block, errors)
        if artifact_key == "constraint_ledger":
            validate_ledger(block, errors)
        elif artifact_key == "code_handoff":
            validate_status(block, artifact_key, errors)
        elif artifact_key == "final_handoff":
            validate_final_handoff(block, errors)
        else:
            validate_status(block, artifact_key, errors)

    for stage_key, filename, block_key, _ in STAGES:
        note_path = bundle_dir / filename
        if not note_path.exists():
            errors.append(f"missing {filename}")
            continue
        block = find_named_block(note_path, block_key)
        if not isinstance(block, dict):
            errors.append(f"{filename}: structured block {block_key} must be an object")
            continue
        parsed_blocks[stage_key] = block
        require_fields(stage_key, block_key, block, errors)
        stage_statuses[stage_key] = block.get("status", "")

        if stage_key == "preprocess":
            validate_preprocess(block, case_block.get("source_request", ""), errors)
        elif stage_key == "divergence":
            validate_options(block, errors)
        elif stage_key == "requirements":
            validate_requirements(block, errors)
        elif stage_key == "critique":
            validate_conflicts(block, errors)
        elif stage_key == "closure":
            validate_dependencies(block, errors)
        elif stage_key == "probes":
            validate_probes(block, errors)
        elif stage_key == "red_blue":
            validate_adversarial(block, errors)
        elif stage_key == "review":
            validate_review(block, errors)
        elif stage_key == "compile_for_code":
            validate_compile_for_code(block, errors)

    handoff_block = parsed_blocks.get("code_handoff")
    if handoff_block:
        validate_handoff(
            handoff_block,
            bundle_dir / "90-code-handoff.md",
            ensure_list(case_block.get("repo_paths")),
            parsed_blocks.get("review"),
            errors,
        )

    validate_run_records(bundle_dir, str(case_block.get("case_id", "")), errors)

    if errors:
        print("[ERROR] Bundle validation failed:")
        for item in errors:
            print(f"  - {item}")
        return 1

    print(f"[OK] Bundle is valid: {bundle_dir}")
    for stage_key, _, _, _ in STAGES:
        print(f"  - {stage_key}: {stage_statuses.get(stage_key, 'missing')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
