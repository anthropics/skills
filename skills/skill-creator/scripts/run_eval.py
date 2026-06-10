#!/usr/bin/env python3
"""Run trigger evaluation for a skill description.

Tests whether a skill's description causes Claude to trigger (read the skill)
for a set of queries. Outputs results as JSON.

Mechanism: the candidate description is installed once per run as a real
skill at <project_root>/.claude/skills/<name>-eval-<id>/SKILL.md, because
that is the only surface `claude -p` exposes to the model for
auto-triggering (files under .claude/commands/ appear in slash_commands but
never in the model's available_skills list, so they can never auto-trigger).
The artifact is shared by all parallel workers and removed when the run ends.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import uuid
from collections import deque
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from queue import Empty, Queue

from scripts.utils import parse_skill_md

# Bounds conversation length for queries that never trigger, so cost and
# wall-clock time stay capped without cutting off legitimate multi-turn
# runs where Claude explores (TodoWrite/Glob/Bash) before invoking the skill.
MAX_CLAUDE_TURNS = 8

# Leftover artifacts must be at least this old before the sweep removes
# them, so it never deletes the live artifact of a concurrent eval run.
STALE_ARTIFACT_MIN_AGE_SECONDS = 3600

_EVAL_SUFFIX_RE = re.compile(r"-eval-[0-9a-f]{8}$")


def find_project_root() -> Path:
    """Find the project root by walking up from cwd looking for .claude/.

    Mimics how Claude Code discovers its project root, so the eval skill
    we create ends up where claude -p will look for it.
    """
    current = Path.cwd()
    for parent in [current, *current.parents]:
        if (parent / ".claude").is_dir():
            return parent
    return current


def resolve_claude_cli() -> str:
    """Resolve the claude executable to a full path.

    On Windows, Popen(["claude", ...]) only finds claude.exe; npm installs
    provide a claude.cmd shim that raises FileNotFoundError unless resolved
    to a full path first. shutil.which handles both via PATHEXT.
    """
    resolved = shutil.which("claude")
    if not resolved:
        raise RuntimeError(
            "Could not find the `claude` CLI on PATH. Install Claude Code or "
            "add its install directory to PATH before running evals."
        )
    return resolved


def _pump_lines(stream, sink) -> None:
    """Read a binary stream line by line into sink; signal EOF with None."""
    try:
        for raw in iter(stream.readline, b""):
            sink(raw)
    finally:
        sink(None)


def _tool_use_mentions(eval_skill_name: str, tool_name: str, tool_input: dict) -> bool:
    """Whether a tool_use block is Claude consulting the eval skill."""
    if tool_name not in ("Skill", "Read"):
        return False
    return eval_skill_name in json.dumps(tool_input)


def run_single_query(
    query: str,
    eval_skill_name: str,
    timeout: int,
    project_root: str,
    model: str | None = None,
    claude_cli: str | None = None,
) -> bool:
    """Run a single query and return whether the eval skill was triggered.

    Streams `claude -p` output and returns True as soon as a Skill/Read
    tool_use referencing the eval skill appears. Other tool calls
    (TodoWrite, Glob, Bash, ...) are ignored rather than treated as
    non-triggers, since Claude often explores before consulting a skill.
    Returns False only on a terminal `result` event, process exit, or
    timeout.
    """
    cmd = [
        claude_cli or resolve_claude_cli(),
        "-p", query,
        "--output-format", "stream-json",
        "--verbose",
        "--include-partial-messages",
        "--max-turns", str(MAX_CLAUDE_TURNS),
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
        stderr=subprocess.PIPE,
        cwd=project_root,
        env=env,
    )

    # select() only works on sockets on Windows, so stream reading goes
    # through reader threads + a queue, which behaves the same everywhere.
    stdout_queue: Queue = Queue()
    stderr_tail: deque = deque(maxlen=40)
    threading.Thread(
        target=_pump_lines, args=(process.stdout, stdout_queue.put), daemon=True
    ).start()
    threading.Thread(
        target=_pump_lines,
        args=(process.stderr, lambda raw: stderr_tail.append(raw) if raw else None),
        daemon=True,
    ).start()

    def stderr_excerpt() -> str:
        return b"".join(stderr_tail).decode("utf-8", errors="replace").strip()[:500]

    deadline = time.time() + timeout
    # Track the Skill/Read block currently streaming its input, if any
    pending_tool_name = None
    accumulated_json = ""

    try:
        while True:
            if time.time() > deadline:
                print(
                    f"Warning: query timed out after {timeout}s; counting as "
                    f"not-triggered: {query[:60]}",
                    file=sys.stderr,
                )
                return False

            try:
                raw = stdout_queue.get(timeout=0.5)
            except Empty:
                continue
            if raw is None:  # EOF: process finished and output is drained
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    # stdout closed but the process lingers; the finally
                    # block kills it
                    return False
                if process.returncode != 0:
                    print(
                        f"Warning: claude -p exited with code {process.returncode} "
                        f"for query: {query[:60]}\n  stderr: {stderr_excerpt()}",
                        file=sys.stderr,
                    )
                return False

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
                        if cb.get("name", "") in ("Skill", "Read"):
                            pending_tool_name = cb.get("name", "")
                            accumulated_json = ""
                        else:
                            pending_tool_name = None

                elif se_type == "content_block_delta" and pending_tool_name:
                    delta = se.get("delta", {})
                    if delta.get("type") == "input_json_delta":
                        accumulated_json += delta.get("partial_json", "")
                        if eval_skill_name in accumulated_json:
                            return True

                elif se_type == "content_block_stop":
                    if pending_tool_name and eval_skill_name in accumulated_json:
                        return True
                    pending_tool_name = None

            # Fallback: full assistant message
            elif event.get("type") == "assistant":
                for content_item in event.get("message", {}).get("content", []):
                    if content_item.get("type") != "tool_use":
                        continue
                    if _tool_use_mentions(
                        eval_skill_name,
                        content_item.get("name", ""),
                        content_item.get("input", {}),
                    ):
                        return True

            elif event.get("type") == "result":
                return False
    finally:
        # Clean up process on any exit path (return, exception, timeout)
        if process.poll() is None:
            process.kill()
            process.wait()


def _cleanup_stale_artifacts(skills_dir: Path, skill_name: str) -> None:
    """Remove eval skills left behind by a previous crashed/killed run."""
    if not skills_dir.is_dir():
        return
    cutoff = time.time() - STALE_ARTIFACT_MIN_AGE_SECONDS
    for entry in skills_dir.glob(f"{skill_name}-eval-*"):
        if entry.is_dir() and _EVAL_SUFFIX_RE.search(entry.name):
            try:
                if entry.stat().st_mtime < cutoff:
                    shutil.rmtree(entry, ignore_errors=True)
            except OSError:
                pass


def _warn_if_shadowed(skill_name: str, project_root: Path) -> None:
    """Warn when an installed skill with the same name could absorb triggers.

    An installed copy of the skill shares its description with the eval
    candidate, so Claude may consult it instead of the artifact and deflate
    measured trigger rates. We warn rather than move user files aside.
    """
    candidates = [
        project_root / ".claude" / "skills" / skill_name,
        Path.home() / ".claude" / "skills" / skill_name,
    ]
    for installed in candidates:
        if installed.is_dir():
            print(
                f"Warning: installed skill at {installed} has the same name as "
                f"the skill under eval and may absorb triggers, deflating "
                f"results. Consider moving it aside while running evals.",
                file=sys.stderr,
            )


def create_eval_skill(
    skill_name: str, skill_description: str, project_root: Path
) -> tuple[str, Path]:
    """Install the candidate description as a real, uniquely named skill.

    Returns (eval_skill_name, skill_dir). The caller is responsible for
    removing skill_dir when the run finishes.
    """
    unique_id = uuid.uuid4().hex[:8]
    eval_skill_name = f"{skill_name}-eval-{unique_id}"
    skills_dir = project_root / ".claude" / "skills"

    _cleanup_stale_artifacts(skills_dir, skill_name)
    _warn_if_shadowed(skill_name, project_root)

    skill_dir = skills_dir / eval_skill_name
    skill_dir.mkdir(parents=True, exist_ok=True)
    # Use YAML block scalar to avoid breaking on quotes in description
    indented_desc = "\n  ".join(skill_description.split("\n"))
    skill_content = (
        f"---\n"
        f"name: {eval_skill_name}\n"
        f"description: |\n"
        f"  {indented_desc}\n"
        f"---\n\n"
        f"# {skill_name}\n\n"
        f"This skill handles: {skill_description}\n\n"
        f"(Temporary trigger-eval artifact created by skill-creator's "
        f"run_eval.py; safe to delete.)\n"
    )
    (skill_dir / "SKILL.md").write_text(skill_content)
    return eval_skill_name, skill_dir


def run_eval(
    eval_set: list[dict],
    skill_name: str,
    description: str,
    num_workers: int,
    timeout: int,
    project_root: Path,
    runs_per_query: int = 1,
    trigger_threshold: float = 0.5,
    model: str | None = None,
) -> dict:
    """Run the full eval set and return results."""
    results = []
    claude_cli = resolve_claude_cli()
    # One shared artifact per run: per-worker copies with distinct names but
    # identical descriptions made Claude pick one arbitrarily, so each
    # worker missed triggers that landed on a sibling's copy.
    eval_skill_name, skill_dir = create_eval_skill(
        skill_name, description, Path(project_root)
    )

    try:
        with ProcessPoolExecutor(max_workers=num_workers) as executor:
            future_to_info = {}
            for item in eval_set:
                for run_idx in range(runs_per_query):
                    future = executor.submit(
                        run_single_query,
                        item["query"],
                        eval_skill_name,
                        timeout,
                        str(project_root),
                        model,
                        claude_cli,
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
                    print(
                        f"Warning: query failed ({type(e).__name__}: {e}); "
                        f"counting as not-triggered: {query[:60]}",
                        file=sys.stderr,
                    )
                    query_triggers[query].append(False)
    finally:
        shutil.rmtree(skill_dir, ignore_errors=True)

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
    parser.add_argument("--verbose", action="store_true", help="Print progress to stderr")
    args = parser.parse_args()

    eval_set = json.loads(Path(args.eval_set).read_text())
    skill_path = Path(args.skill_path)

    if not (skill_path / "SKILL.md").exists():
        print(f"Error: No SKILL.md found at {skill_path}", file=sys.stderr)
        sys.exit(1)

    name, original_description, content = parse_skill_md(skill_path)
    description = args.description or original_description
    project_root = find_project_root()

    if args.verbose:
        print(f"Evaluating: {description}", file=sys.stderr)

    output = run_eval(
        eval_set=eval_set,
        skill_name=name,
        description=description,
        num_workers=args.num_workers,
        timeout=args.timeout,
        project_root=project_root,
        runs_per_query=args.runs_per_query,
        trigger_threshold=args.trigger_threshold,
        model=args.model,
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
