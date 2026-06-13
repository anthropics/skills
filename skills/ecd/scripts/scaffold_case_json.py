#!/usr/bin/env python3
"""
Create a normalized ECL v2 case JSON scaffold from a raw request.
"""

from __future__ import annotations

import argparse
import json
import re
from datetime import date
from pathlib import Path

CJK_RE = re.compile(r"[\u3400-\u9fff]")


def detect_language(text: str) -> str:
    return "zh-CN" if CJK_RE.search(text or "") else "en"


def slugify(text: str) -> str:
    base = text.strip().lower()
    base = re.sub(r"[^a-z0-9\u3400-\u9fff]+", "-", base)
    base = re.sub(r"-{2,}", "-", base).strip("-")
    if not base:
        return "ecl-case"
    return base[:64].strip("-") or "ecl-case"


def stage_shell(user_request: str) -> dict:
    return {
        "status": "pending",
        "narrative": "",
        "key_points": [],
        "decisions": [],
        "open_questions": [],
        "next_actions": [],
        "agent_mode": "parent",
        "support_agent_findings": [],
        "subagent_findings": [],
        "user_stated_request": user_request,
        "ambiguity_points": [],
        "dubious_claims": [],
        "factual_gaps": [],
        "hidden_assumptions": [],
        "suspected_real_goals": [],
        "scenario_fragments": [],
        "success_signals": [],
        "non_goals": [],
        "follow_up_questions": [],
        "blocking_unknowns": [],
        "reframed_request": "",
        "evidence_refs": [],
    }


def build_payload(args) -> dict:
    request = args.request
    request_language = detect_language(request)
    output_language = args.output_language or request_language
    title = args.title or request.strip().splitlines()[0][:80] or "ECL Case"
    slug = args.slug or slugify(title)
    today = args.date or str(date.today())
    repo_absent_policy = (
        "如果缺少 repo_path，则继续规划，但保持 code_ready=false，并输出 scaffold blueprint。"
        if output_language == "zh-CN"
        else "If repo_path is absent, continue planning but keep code_ready=false and emit a scaffold blueprint."
    )
    preprocess = stage_shell(request)
    return {
        "bundle_version": 2,
        "title": title,
        "slug": slug,
        "date": today,
        "mode": args.mode,
        "source_request": request,
        "request_language": request_language,
        "output_language": output_language,
        "summary": "",
        "final_outcome": "",
        "project_paths": args.project_path or [],
        "repo_paths": args.repo_path or [],
        "vault_root": args.vault_root,
        "output_root": args.output_root,
        "stages": {
            "preprocess": preprocess,
            "divergence": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "options": [],
                "decision_criteria": [],
                "dropped_options": [],
                "retained_option_id": "",
            },
            "requirements": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "requirement_units": [],
                "interface_contracts": [],
                "success_criteria": [],
                "validation_targets": [],
                "non_goals": [],
                "frozen_terms": [],
            },
            "critique": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "agent_mode": "pending",
                "subagent_findings": [],
                "critique_findings": [],
                "orthogonal_axes": [],
                "conflicts": [],
                "dropped_requirements": [],
                "resolution_decisions": [],
            },
            "closure": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "end_to_end_chain": [],
                "dependency_gaps": [],
                "completions": [],
                "unresolved_dependencies": [],
            },
            "probes": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "probes": [],
                "discarded_paths": [],
                "surviving_paths": [],
                "open_probe_limits": [],
            },
            "red_blue": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "agent_mode": "pending",
                "subagent_findings": [],
                "attack_vectors": [],
                "mitigations": [],
                "residual_risks": [],
                "unresolved_attacks": [],
            },
            "review": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "agent_mode": "pending",
                "subagent_findings": [],
                "verdict": "rejected",
                "approval_conditions": [],
                "blockers": [],
                "rationale": "",
                "reentry_stage_if_rejected": "A",
            },
            "compile_for_code": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "agent_mode": "pending",
                "subagent_findings": [],
                "code_ready": False,
                "blocking_gaps": [],
                "frozen_contract_refs": [],
                "compiled_review_conditions": [],
                "repo_targets": args.repo_path or [],
                "execution_manifest_ref": "95-execution-manifest.md",
                "handoff_entry": "99-code-handoff.md",
                "reopen_stage_if_blocked": "J",
            },
        },
        "artifacts": {
            "constraint_ledger": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "retained_goal": "",
                "confirmed_facts": [],
                "challenged_claims": [],
                "frozen_constraints": [],
                "dropped_options": [],
                "risks": [],
                "dependency_chain": [],
                "verification_semantics": [],
                "stage_refs": [],
                "handoff_ref": "90-code-handoff.md",
            },
            "code_handoff": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "next_actions": [],
                "code_ready": False,
                "handoff_summary": "",
                "retained_goal": "",
                "implementation_scope": [],
                "repo_targets": args.repo_path or [],
                "repo_grounding": [],
                "read_first": [],
                "frozen_product_decisions": [],
                "domain_model": [],
                "data_contract": [],
                "ui_contract": [],
                "function_contracts": [],
                "file_plan": [],
                "implementation_units": [],
                "verification_commands": [],
                "browser_checks": [],
                "acceptance_checks": [],
                "allowed_decisions": [],
                "forbidden_decisions": [],
                "reentry_triggers": [],
                "reopen_stage_map": [],
                "unresolved_gaps": [],
            },
            "canonical_contracts": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "contracts": [],
            },
            "constraint_crosswalk": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "crosswalk_rows": [],
            },
            "execution_manifest": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "phases": [],
                "scaffold_blueprint": [],
            },
            "code_batches": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "batches": [],
            },
            "code_preflight": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "confirmed": [],
                "do_not_reinvent": [],
                "do_first": [],
                "context_bundle": [],
                "progress_snapshot": {},
                "current_focus": "",
                "remaining_work": [],
                "pause_conditions": [],
                "session_notes": [],
            },
            "final_handoff": {
                "status": "pending",
                "narrative": "",
                "key_points": [],
                "decisions": [],
                "open_questions": [],
                "next_actions": [],
                "code_ready": False,
                "handoff_entry": "90-code-handoff.md",
                "direct_code_command": "",
                "blocking_gaps": [],
                "repo_absent_policy": repo_absent_policy,
                "mandatory_multi_agent_stage_blocked": False,
                "next_step": "",
            },
        },
    }


def read_request(args) -> str:
    if args.request:
        return args.request.strip()
    return Path(args.request_file).expanduser().read_text(encoding="utf-8").strip()


def main() -> int:
    parser = argparse.ArgumentParser(description="Create a normalized ECL v2 case JSON scaffold.")
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--request", help="Raw request text")
    source.add_argument("--request-file", help="Path to a UTF-8 text file containing the raw request")
    parser.add_argument("--output-json", required=True, help="Path to the scaffold JSON file to write")
    parser.add_argument("--title", help="Case title override")
    parser.add_argument("--slug", help="Case slug override")
    parser.add_argument("--date", help="Case date override in YYYY-MM-DD format")
    parser.add_argument("--mode", default="spec", help="Mode label, defaults to spec")
    parser.add_argument("--output-language", help="Override output language")
    parser.add_argument("--project-path", action="append", default=[], help="Project path, repeatable")
    parser.add_argument("--repo-path", action="append", default=[], help="Repo path, repeatable")
    parser.add_argument("--vault-root", default="", help="Vault root path if known")
    parser.add_argument("--output-root", default="", help="Output root path if known")
    args = parser.parse_args()

    args.request = read_request(args)
    payload = build_payload(args)
    output_path = Path(args.output_json).expanduser().resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[OK] Wrote scaffold case JSON: {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
