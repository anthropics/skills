#!/usr/bin/env python3
"""
Unified CLI helpers for ECD (Evolutionary Constraint Development).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
SCAFFOLD_CASE = SCRIPT_DIR / "scaffold_case_json.py"
RENDER_BUNDLE = SCRIPT_DIR / "render_obsidian_bundle.py"
VALIDATE_BUNDLE = SCRIPT_DIR / "validate_ecl_bundle.py"
RENDER_CODE_RUN = SCRIPT_DIR / "render_code_run.py"
RENDER_OPENSPEC = SCRIPT_DIR / "render_openspec_pack.py"
RENDER_ACHIEVE = SCRIPT_DIR / "render_achieve_note.py"

FENCE_RE = re.compile(r"```([^\n`]*)\n(.*?)\n```", re.DOTALL)


def run_python(script: Path, argv: list[str]) -> int:
    env = dict(os.environ)
    env.setdefault("PYTHONPYCACHEPREFIX", str(Path(tempfile.gettempdir()) / "ecl-pycache"))
    completed = subprocess.run([sys.executable, str(script), *argv], env=env)
    return int(completed.returncode)


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


def parse_handoff_block(bundle_dir: Path) -> dict | None:
    return parse_json_fence(bundle_dir / "90-code-handoff.md", "ecl.code_handoff")


def parse_case_block(bundle_dir: Path) -> dict | None:
    return parse_json_fence(bundle_dir / "00-overview.md", "ecl.case")


def resolve_bundle_dir(case: str | None, handoff: str | None) -> Path | None:
    if handoff:
        return Path(handoff).expanduser().resolve().parent
    if case:
        return Path(case).expanduser().resolve()
    return None


def load_json(path: str) -> dict:
    return json.loads(Path(path).expanduser().read_text(encoding="utf-8"))


def latest_run_dir(bundle_dir: Path) -> Path | None:
    runs_dir = bundle_dir / "Runs"
    if not runs_dir.exists() or not runs_dir.is_dir():
        return None
    candidates = [path for path in runs_dir.iterdir() if path.is_dir()]
    if not candidates:
        return None
    return sorted(candidates)[-1]


def build_scaffold_args(args, output_json: Path) -> list[str]:
    scaffold_args: list[str] = ["--output-json", str(output_json)]
    if getattr(args, "request", None):
        scaffold_args.extend(["--request", args.request])
    else:
        scaffold_args.extend(["--request-file", str(Path(args.request_file).expanduser().resolve())])
    for flag, value in [
        ("--title", getattr(args, "title", None)),
        ("--slug", getattr(args, "slug", None)),
        ("--date", getattr(args, "date", None)),
        ("--mode", getattr(args, "mode", None)),
        ("--output-language", getattr(args, "output_language", None)),
        ("--vault-root", getattr(args, "vault_root", None)),
        ("--output-root", getattr(args, "output_root", None)),
    ]:
        if value:
            scaffold_args.extend([flag, value])
    for path in getattr(args, "project_path", []) or []:
        scaffold_args.extend(["--project-path", path])
    for path in getattr(args, "repo_path", []) or []:
        scaffold_args.extend(["--repo-path", path])
    return scaffold_args


def command_scaffold(args) -> int:
    return run_python(SCAFFOLD_CASE, build_scaffold_args(args, Path(args.output_json).expanduser().resolve()))


def render_bundle_pipeline(input_json: str, output_dir: Path, force: bool = False) -> int:
    render_args = [input_json, "--output", str(output_dir)]
    if force:
        render_args.append("--force")
    rc = run_python(RENDER_BUNDLE, render_args)
    if rc != 0:
        return rc

    rc = run_python(VALIDATE_BUNDLE, [str(output_dir)])
    if rc != 0:
        return rc

    return run_python(RENDER_OPENSPEC, [input_json, "--bundle", str(output_dir)])


def command_pre(args) -> int:
    if not args.output:
        print("[ERROR] ecl pre requires --output so the rendered bundle can be checked", file=sys.stderr)
        return 1

    output_dir = Path(args.output).expanduser().resolve()
    scaffold_path = (
        Path(args.case_json_out).expanduser().resolve()
        if args.case_json_out
        else output_dir.with_suffix(".case.json")
    )
    rc = run_python(SCAFFOLD_CASE, build_scaffold_args(args, scaffold_path))
    if rc != 0:
        return rc

    rc = render_bundle_pipeline(str(scaffold_path), output_dir, args.force)
    if rc != 0:
        return rc

    print("[OK] ecl pre initialized the Stage A approval workspace.")
    print(f"      case json: {scaffold_path}")
    print(f"      bundle: {output_dir}")
    print("      next: finish Stage A, mark preprocess complete, then run ecl plan --input-json <case.json> --output <bundle> --force")
    return 0


def command_plan(args) -> int:
    if not args.output:
        print("[ERROR] ecl plan requires --output so the rendered bundle can be checked", file=sys.stderr)
        return 1
    if not args.input_json:
        print("[ERROR] ecl plan no longer accepts raw request input. Run ecl pre first.", file=sys.stderr)
        return 1

    output_dir = Path(args.output).expanduser().resolve()
    input_path = Path(args.input_json).expanduser().resolve()
    if not input_path.exists():
        print(f"[ERROR] ecl plan input JSON does not exist: {input_path}", file=sys.stderr)
        return 1
    case_json = load_json(str(input_path))
    preprocess = ((case_json.get("stages") or {}).get("preprocess") or {})
    if str(preprocess.get("status", "")).strip() != "complete":
        print(
            "[ERROR] ecl plan requires Stage A to be complete first. "
            "Finish ecl pre, complete preprocess, and approve the result before planning.",
            file=sys.stderr,
        )
        return 1

    rc = render_bundle_pipeline(str(input_path), output_dir, args.force)
    if rc != 0:
        return rc

    handoff = parse_handoff_block(output_dir)
    if not handoff or not handoff.get("code_ready"):
        print(
            "[ERROR] ecl plan rendered a bundle, but 90-code-handoff.md is not code-ready. "
            "Refusing to report success because the next model would still have open questions.",
            file=sys.stderr,
        )
        return 1

    print(f"[OK] ecl plan finished with a validated, code-ready bundle: {output_dir}")
    print(f"[OK] OpenSpec pack rendered under: {output_dir / 'OpenSpec'}")
    return 0


def command_code(args) -> int:
    if not args.run_json:
        print("[ERROR] ecl code requires --run-json", file=sys.stderr)
        return 1

    bundle_dir = resolve_bundle_dir(args.case, args.handoff)
    if bundle_dir is None:
        print("[ERROR] ecl code requires --handoff or --case", file=sys.stderr)
        return 1

    rc = run_python(VALIDATE_BUNDLE, [str(bundle_dir)])
    if rc != 0:
        return rc

    handoff = parse_handoff_block(bundle_dir)
    if not handoff:
        print("[ERROR] ecl code could not parse ecl.code_handoff", file=sys.stderr)
        return 1
    if not handoff.get("code_ready"):
        print("[ERROR] ecl code refuses to start when code_ready=false", file=sys.stderr)
        return 1

    run_payload = load_json(args.run_json)
    repo_targets = [str(item) for item in handoff.get("repo_targets", [])]
    entry_repo = str(run_payload.get("entry_repo", "")).strip()
    if entry_repo and not Path(entry_repo).expanduser().exists():
        print(f"[ERROR] ecl code entry_repo does not exist: {entry_repo}", file=sys.stderr)
        return 1
    if not entry_repo and repo_targets:
        if not Path(repo_targets[0]).expanduser().exists():
            print(f"[ERROR] ecl code repo target does not exist: {repo_targets[0]}", file=sys.stderr)
            return 1
    valid_units = {str(item.get("id")) for item in handoff.get("implementation_units", []) if isinstance(item, dict)}
    selected_units = {str(item) for item in run_payload.get("selected_units", [])}
    if selected_units and not selected_units.issubset(valid_units):
        invalid = ", ".join(sorted(selected_units - valid_units))
        print(f"[ERROR] ecl code run-json selected_units are not in the handoff: {invalid}", file=sys.stderr)
        return 1

    rc = run_python(RENDER_CODE_RUN, [str(bundle_dir), str(Path(args.run_json).expanduser())])
    if rc != 0:
        return rc
    return run_python(VALIDATE_BUNDLE, [str(bundle_dir)])


def build_achieve_payload(handoff: dict, code_run: dict, verification: dict, language: str = "en") -> dict:
    outcome = str(code_run.get("outcome", ""))
    failed_checks = verification.get("failed_checks") or []
    residual_issues = [str(item) for item in failed_checks]
    if not (verification.get("commands_run") or []):
        residual_issues.append(
            "最近一次 /code 没有记录验证命令。" if language == "zh-CN" else "No verification commands were recorded for the latest /code run."
        )
    if not (verification.get("results") or []):
        residual_issues.append(
            "最近一次 /code 没有记录验证结果。" if language == "zh-CN" else "No verification results were recorded for the latest /code run."
        )
    if handoff.get("browser_checks") and not (verification.get("evidence_refs") or []):
        residual_issues.append(
            "handoff 要求浏览器证据，但 evidence_refs 为空。"
            if language == "zh-CN"
            else "The handoff required browser evidence, but evidence_refs is empty."
        )

    if residual_issues:
        verdict = "not_achieved"
    elif outcome == "completed_with_low_impact_fixes":
        verdict = "achieved_with_followups"
    else:
        verdict = "achieved"
    if verdict == "achieved":
        archive_status = "archived"
        archive_reason = (
            "本次运行满足冻结验收契约，作为闭环记录归档。"
            if language == "zh-CN"
            else "The run satisfied the frozen acceptance contract and is archived as the closure record."
        )
        next_actions = [
            "除非出现新的变更请求，否则无需额外动作。"
            if language == "zh-CN"
            else "No further action is required unless a new change request appears."
        ]
    elif verdict == "achieved_with_followups":
        archive_status = "archived"
        archive_reason = (
            "本次运行通过验收，仅保留低影响跟进项，当前按已交付归档。"
            if language == "zh-CN"
            else "The run passed acceptance with only low-impact followups, so it is archived with those notes attached."
        )
        next_actions = [
            "低影响跟进项如果之后值得处理，再单独开新请求。"
            if language == "zh-CN"
            else "Track any low-impact followups separately if they become worth a new request."
        ]
    else:
        archive_status = "left_open"
        archive_reason = (
            "本次结果未干净通过验收，因此 case 保持打开，等待下一次真实运行。"
            if language == "zh-CN"
            else "Acceptance did not pass cleanly, so the case remains open for another truthful run."
        )
        next_actions = [
            "先处理残留问题，再尝试重新闭环。"
            if language == "zh-CN"
            else "Keep the case open and address the residual issues before trying to close it again."
        ]

    run_id = str(code_run.get("run_id", ""))
    return {
        "status": "complete",
        "run_id": run_id,
        "goal": (
            "通过最终验收与归档判断，关闭本次 plan/code 闭环。"
            if language == "zh-CN"
            else "Close the plan/code loop by making a final acceptance-and-archive judgment."
        ),
        "narrative": (
            "基于最近一次 code 运行、验证证据和闭环规则综合生成。"
            if language == "zh-CN"
            else "Synthesized from the latest code run, verification evidence, and closure policy."
        ),
        "verdict": verdict,
        "archive_status": archive_status,
        "archive_reason": archive_reason,
        "acceptance_results": handoff.get("acceptance_checks", []),
        "verification_summary": verification.get("results", []),
        "residual_issues": residual_issues,
        "next_actions": next_actions,
        "archive_refs": [
            f"Runs/{run_id}/00-code-run.md",
            f"Runs/{run_id}/01-verification.md",
        ],
        "evidence_refs": verification.get("evidence_refs", []),
    }


def command_achieve(args) -> int:
    bundle_dir = resolve_bundle_dir(args.case, args.handoff)
    if bundle_dir is None:
        print("[ERROR] ecl achieve requires --handoff or --case", file=sys.stderr)
        return 1

    rc = run_python(VALIDATE_BUNDLE, [str(bundle_dir)])
    if rc != 0:
        return rc

    handoff = parse_handoff_block(bundle_dir)
    if not handoff or not handoff.get("code_ready"):
        print("[ERROR] ecl achieve requires a truthful code-ready handoff", file=sys.stderr)
        return 1
    case_block = parse_case_block(bundle_dir) or {}
    language = str(case_block.get("output_language") or case_block.get("request_language") or "en")

    run_dir = latest_run_dir(bundle_dir)
    if run_dir is None:
        print("[ERROR] ecl achieve requires at least one recorded /code run under Runs/", file=sys.stderr)
        return 1

    code_run = parse_json_fence(run_dir / "00-code-run.md", "ecl.code_run")
    verification = parse_json_fence(run_dir / "01-verification.md", "ecl.code_verification")
    if not code_run or not verification:
        print("[ERROR] ecl achieve could not parse the latest run record", file=sys.stderr)
        return 1
    if code_run.get("outcome") in {"blocked_for_reentry", "refused_by_gate"}:
        print(f"[ERROR] ecl achieve refuses a blocking outcome: {code_run.get('outcome')}", file=sys.stderr)
        return 1

    if args.achieve_json:
        payload_path = Path(args.achieve_json).expanduser().resolve()
    else:
        payload = build_achieve_payload(handoff, code_run, verification, language)
        temp_dir = Path(tempfile.mkdtemp(prefix="ecl-achieve-"))
        payload_path = temp_dir / "achieve.json"
        payload_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    rc = run_python(RENDER_ACHIEVE, [str(bundle_dir), str(payload_path)])
    if rc != 0:
        return rc
    rc = run_python(VALIDATE_BUNDLE, [str(bundle_dir)])
    if rc != 0:
        return rc

    payload = load_json(str(payload_path))
    payload.setdefault(
        "archive_status",
        "left_open" if payload.get("verdict") == "not_achieved" else "archived",
    )
    print(
        "[OK] ecl achieve finished with "
        f"verdict={payload.get('verdict')} archive_status={payload.get('archive_status')} "
        f"for bundle: {bundle_dir}"
    )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="ECD (Evolutionary Constraint Development) CLI helpers")
    subparsers = parser.add_subparsers(dest="command", required=True)

    scaffold = subparsers.add_parser("scaffold", help="Create a normalized case JSON scaffold from a raw request")
    scaffold_source = scaffold.add_mutually_exclusive_group(required=True)
    scaffold_source.add_argument("--request", help="Raw request text")
    scaffold_source.add_argument("--request-file", help="Path to a text file containing the raw request")
    scaffold.add_argument("--output-json", required=True, help="Output case JSON path")
    scaffold.add_argument("--title", help="Case title override")
    scaffold.add_argument("--slug", help="Case slug override")
    scaffold.add_argument("--date", help="Case date override in YYYY-MM-DD format")
    scaffold.add_argument("--mode", default="spec", help="Mode label, defaults to spec")
    scaffold.add_argument("--output-language", help="Output language override")
    scaffold.add_argument("--project-path", action="append", default=[], help="Project path, repeatable")
    scaffold.add_argument("--repo-path", action="append", default=[], help="Repo path, repeatable")
    scaffold.add_argument("--vault-root", help="Vault root path")
    scaffold.add_argument("--output-root", help="Output root path")
    scaffold.set_defaults(func=command_scaffold)

    pre = subparsers.add_parser(
        "pre",
        help="Initialize Stage A approval-gate workspace from a raw request",
    )
    pre_source = pre.add_mutually_exclusive_group(required=True)
    pre_source.add_argument("--request", help="Raw request text")
    pre_source.add_argument("--request-file", help="Path to a text file containing the raw request")
    pre.add_argument("--output", required=True, help="Output bundle directory")
    pre.add_argument("--force", action="store_true", help="Overwrite an existing output directory")
    pre.add_argument("--case-json-out", help="Where to write scaffold JSON for Stage A")
    pre.add_argument("--title", help="Case title override")
    pre.add_argument("--slug", help="Case slug override")
    pre.add_argument("--date", help="Case date override in YYYY-MM-DD format")
    pre.add_argument("--mode", default="spec", help="Mode label, defaults to spec")
    pre.add_argument("--output-language", help="Output language override")
    pre.add_argument("--project-path", action="append", default=[], help="Project path, repeatable")
    pre.add_argument("--repo-path", action="append", default=[], help="Repo path, repeatable")
    pre.add_argument("--vault-root", help="Vault root path")
    pre.add_argument("--output-root", help="Output root path")
    pre.set_defaults(func=command_pre)

    plan = subparsers.add_parser(
        "plan",
        help="Render the post-approval code-ready ECD bundle from a normalized case JSON",
    )
    plan.add_argument("--input-json", required=True, help="Path to normalized ECD JSON input with Stage A complete")
    plan.add_argument("--output", required=True, help="Output bundle directory")
    plan.add_argument("--force", action="store_true", help="Overwrite an existing output directory")
    plan.set_defaults(func=command_plan)

    code = subparsers.add_parser("code", help="Validate the handoff and append /code run evidence")
    code.add_argument("--case", help="Bundle directory path")
    code.add_argument("--handoff", help="Absolute path to 90-code-handoff.md")
    code.add_argument("--run-json", required=True, help="Path to run JSON payload")
    code.set_defaults(func=command_code)

    achieve = subparsers.add_parser(
        "achieve",
        help="Validate the latest /code run, render the acceptance verdict, and record the archive decision",
    )
    achieve.add_argument("--case", help="Bundle directory path")
    achieve.add_argument("--handoff", help="Absolute path to 90-code-handoff.md")
    achieve.add_argument("--achieve-json", help="Optional achieve payload to render into Runs/<run-id>/03-achieve.md")
    achieve.set_defaults(func=command_achieve)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
