#!/usr/bin/env python3
"""Run trigger evaluation for a skill description.

Tests whether a skill's description causes Claude to trigger (read the skill)
for a set of queries. Outputs results as JSON.
"""

import argparse
import json
import os
import queue
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from scripts.utils import parse_skill_md


def _check_installed_skill(skill_name: str, allow: bool) -> None:
    """Refuse to measure while the real skill is installed at user level.

    A claude -p session loads user-level skills regardless of its cwd, so the
    real skill sits next to the probe with the same description and a cleaner
    name, and the model picks the real one. Scores are then wrong in both
    directions: sessions that used the real skill count as misses, while the
    fallback Read-detection credits mere inspection of the probe file as a
    trigger. Park the skill (rename its SKILL.md) for the duration of the
    eval.
    """
    if allow:
        return
    config_dir = Path(os.environ.get("CLAUDE_CONFIG_DIR") or Path.home() / ".claude")
    installed = config_dir / "skills" / skill_name / "SKILL.md"
    if installed.exists():
        raise SystemExit(
            f"Error: skill '{skill_name}' is installed at {installed}.\n"
            "Park it for the eval (rename SKILL.md to SKILL.md.parked, restore "
            "afterwards), or pass --allow-installed-skill."
        )


def _rmtree_force(path: Path) -> None:
    """rmtree that clears read-only bits before retrying (git object files)."""

    def _chmod_and_retry(func, p, _exc):
        os.chmod(p, stat.S_IWRITE)
        func(p)

    try:
        shutil.rmtree(path, onexc=_chmod_and_retry)
    except OSError as e:
        print(f"Warning: could not remove isolated root {path}: {e}", file=sys.stderr)


def run_single_query(
    query: str,
    skill_name: str,
    skill_description: str,
    timeout: int,
    env_template: str | None,
    model: str | None = None,
) -> bool:
    """Run a single query and return whether the skill was triggered.

    The query runs in its own throwaway project root (a fresh temp dir,
    optionally seeded from a copy of env_template), with the probe command
    file in that root's .claude/commands/. A shared commands dir would put
    every in-flight probe in every session's sight: near-identical
    descriptions competing for one query, so a run is credited with
    probability ~1/num_workers regardless of description quality.

    Uses --include-partial-messages to detect triggering from stream events
    as they arrive. A tool call that isn't the probe is not a verdict — the
    model may run something else first (e.g. `git status`) before consulting
    the skill — so detection keeps reading and only concludes on a positive
    match, the result event, or EOF.
    """
    unique_id = uuid.uuid4().hex[:8]
    clean_name = f"{skill_name}-skill-{unique_id}"
    iso_root = Path(tempfile.mkdtemp(prefix=f"trigeval-{skill_name}-"))
    commands_dir = iso_root / ".claude" / "commands"
    command_file = commands_dir / f"{clean_name}.md"

    try:
        if env_template:
            # Seed the isolated root so workspace-context queries ("commit",
            # "format this report") keep their referent. A copy rather than
            # symlinks: symlink creation needs elevation or Developer Mode on
            # Windows (WinError 1314), so link-based seeding fails there and
            # leaves the root empty.
            shutil.copytree(env_template, iso_root, dirs_exist_ok=True)
        commands_dir.mkdir(parents=True, exist_ok=True)
        # Use YAML block scalar to avoid breaking on quotes in description
        indented_desc = "\n  ".join(skill_description.split("\n"))
        command_content = (
            f"---\n"
            f"description: |\n"
            f"  {indented_desc}\n"
            f"---\n\n"
            f"# {skill_name}\n\n"
            f"This skill handles: {skill_description}\n"
        )
        command_file.write_text(command_content, encoding="utf-8")

        # shutil.which resolves the full executable path (PATHEXT-aware on
        # Windows); a bare "claude" is not always resolvable by CreateProcess.
        cmd = [
            shutil.which("claude") or "claude",
            "-p", query,
            "--output-format", "stream-json",
            "--verbose",
            "--include-partial-messages",
        ]
        if model:
            cmd.extend(["--model", model])

        # Remove CLAUDECODE env var to allow nesting claude -p inside a
        # Claude Code session. The guard is for interactive terminal conflicts;
        # programmatic subprocess usage is safe.
        env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}

        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            cwd=iso_root,
            env=env,
        )

        start_time = time.time()
        # Track state for stream event detection
        pending_tool_name = None
        accumulated_json = ""

        # select() doesn't work on Windows pipes (only sockets), so a reader
        # thread pushes stdout lines onto a queue instead; the main loop polls
        # with a 1s timeout to keep the per-query deadline responsive.
        line_queue = queue.Queue()

        def _drain_stdout():
            try:
                for raw in iter(process.stdout.readline, b""):
                    line_queue.put(raw)
            except (OSError, ValueError):
                pass
            finally:
                line_queue.put(None)  # EOF sentinel

        threading.Thread(target=_drain_stdout, daemon=True).start()

        try:
            while time.time() - start_time < timeout:
                try:
                    raw = line_queue.get(timeout=1.0)
                except queue.Empty:
                    continue
                if raw is None:  # EOF: claude finished writing
                    break

                line = raw.decode("utf-8", errors="replace").strip()
                if not line:
                    continue

                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue

                # Early detection via stream events
                if event.get("type") == "stream_event":
                    se = event.get("event", {})
                    se_type = se.get("type", "")

                    if se_type == "content_block_start":
                        cb = se.get("content_block", {})
                        if cb.get("type") == "tool_use":
                            tool_name = cb.get("name", "")
                            if tool_name in ("Skill", "Read"):
                                pending_tool_name = tool_name
                                accumulated_json = ""
                            else:
                                # Not a verdict — reset and keep reading.
                                # The model may still consult the skill
                                # after a preliminary tool call, and exiting
                                # early here would score those runs as
                                # misses.
                                pending_tool_name = None
                                accumulated_json = ""

                    elif se_type == "content_block_delta" and pending_tool_name:
                        delta = se.get("delta", {})
                        if delta.get("type") == "input_json_delta":
                            accumulated_json += delta.get("partial_json", "")
                            if clean_name in accumulated_json:
                                return True

                    elif se_type == "content_block_stop":
                        if pending_tool_name and clean_name in accumulated_json:
                            return True
                        pending_tool_name = None
                        accumulated_json = ""

                    # message_stop only ends one assistant message; with tool
                    # use, further messages follow. No verdict on it.

                # Fallback: full assistant message
                elif event.get("type") == "assistant":
                    message = event.get("message", {})
                    for content_item in message.get("content", []):
                        if content_item.get("type") != "tool_use":
                            continue
                        tool_name = content_item.get("name", "")
                        tool_input = content_item.get("input", {})
                        if tool_name == "Skill" and clean_name in tool_input.get("skill", ""):
                            return True
                        if tool_name == "Read" and clean_name in tool_input.get("file_path", ""):
                            return True
                    # No trigger in this message; later turns may still
                    # consult the skill — keep reading.

                elif event.get("type") == "result":
                    # Whole session finished without a probe invocation.
                    return False
        finally:
            # Clean up process on any exit path (return, exception, timeout).
            # On Windows, kill the whole tree: when claude is a .cmd shim,
            # kill() only terminates cmd.exe and the node child survives,
            # holding the stdout pipe open (and the reader thread with it).
            # The tree kill is also what lets the cleanup below succeed — an
            # orphan whose cwd is the isolated root blocks its deletion.
            if process.poll() is None:
                if sys.platform == "win32":
                    subprocess.run(
                        ["taskkill", "/F", "/T", "/PID", str(process.pid)],
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                    )
                else:
                    process.kill()
                process.wait()

        return False
    finally:
        _rmtree_force(iso_root)


def run_eval(
    eval_set: list[dict],
    skill_name: str,
    description: str,
    num_workers: int,
    timeout: int,
    env_template: Path | None,
    runs_per_query: int = 1,
    trigger_threshold: float = 0.5,
    model: str | None = None,
    allow_installed_skill: bool = False,
) -> dict:
    """Run the full eval set and return results."""
    results = []

    _check_installed_skill(skill_name, allow_installed_skill)

    with ProcessPoolExecutor(max_workers=num_workers) as executor:
        future_to_info = {}
        for item in eval_set:
            for run_idx in range(runs_per_query):
                future = executor.submit(
                    run_single_query,
                    item["query"],
                    skill_name,
                    description,
                    timeout,
                    str(env_template) if env_template else None,
                    model,
                )
                future_to_info[future] = (item, run_idx)

        query_triggers: dict[str, list[bool]] = {}
        query_items: dict[str, dict] = {}
        for future in as_completed(future_to_info):
            item, _ = future_to_info[future]
            query = item["query"]
            query_items[query] = item
            if query not in query_triggers:
                query_triggers[query] = []
            try:
                query_triggers[query].append(future.result())
            except Exception as e:
                print(f"Warning: query failed: {e}", file=sys.stderr)
                query_triggers[query].append(False)

    for query, triggers in query_triggers.items():
        item = query_items[query]
        trigger_rate = sum(triggers) / len(triggers)
        should_trigger = item["should_trigger"]
        if should_trigger:
            did_pass = trigger_rate >= trigger_threshold
        else:
            did_pass = trigger_rate < trigger_threshold
        results.append({
            "query": query,
            "should_trigger": should_trigger,
            "trigger_rate": trigger_rate,
            "triggers": sum(triggers),
            "runs": len(triggers),
            "pass": did_pass,
        })

    passed = sum(1 for r in results if r["pass"])
    total = len(results)

    return {
        "skill_name": skill_name,
        "description": description,
        "results": results,
        "summary": {
            "total": total,
            "passed": passed,
            "failed": total - passed,
        },
    }


def main():
    parser = argparse.ArgumentParser(description="Run trigger evaluation for a skill description")
    parser.add_argument("--eval-set", required=True, help="Path to eval set JSON file")
    parser.add_argument("--skill-path", required=True, help="Path to skill directory")
    parser.add_argument("--description", default=None, help="Override description to test")
    parser.add_argument("--num-workers", type=int, default=10, help="Number of parallel workers")
    parser.add_argument("--timeout", type=int, default=30, help="Timeout per query in seconds")
    parser.add_argument("--runs-per-query", type=int, default=3, help="Number of runs per query")
    parser.add_argument("--trigger-threshold", type=float, default=0.5, help="Trigger rate threshold")
    parser.add_argument("--model", default=None, help="Model to use for claude -p (default: user's configured model)")
    parser.add_argument("--env-template", default=None, help="Directory copied into each query's isolated project root, for queries whose meaning depends on workspace state (git repo, files, CLAUDE.md). Copied once per run — keep it small. Default: empty root.")
    parser.add_argument("--allow-installed-skill", action="store_true", help="Skip the installed-skill check (scores are usually meaningless while the real skill is visible to eval sessions)")
    parser.add_argument("--verbose", action="store_true", help="Print progress to stderr")
    args = parser.parse_args()

    eval_set = json.loads(Path(args.eval_set).read_text(encoding="utf-8"))
    skill_path = Path(args.skill_path)

    if not (skill_path / "SKILL.md").exists():
        print(f"Error: No SKILL.md found at {skill_path}", file=sys.stderr)
        sys.exit(1)

    name, original_description, content = parse_skill_md(skill_path)
    description = args.description or original_description

    if args.verbose:
        print(f"Evaluating: {description}", file=sys.stderr)

    output = run_eval(
        eval_set=eval_set,
        skill_name=name,
        description=description,
        num_workers=args.num_workers,
        timeout=args.timeout,
        env_template=Path(args.env_template) if args.env_template else None,
        runs_per_query=args.runs_per_query,
        trigger_threshold=args.trigger_threshold,
        model=args.model,
        allow_installed_skill=args.allow_installed_skill,
    )

    if args.verbose:
        summary = output["summary"]
        print(f"Results: {summary['passed']}/{summary['total']} passed", file=sys.stderr)
        for r in output["results"]:
            status = "PASS" if r["pass"] else "FAIL"
            rate_str = f"{r['triggers']}/{r['runs']}"
            print(f"  [{status}] rate={rate_str} expected={r['should_trigger']}: {r['query'][:70]}", file=sys.stderr)

    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
