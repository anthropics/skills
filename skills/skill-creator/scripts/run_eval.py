#!/usr/bin/env python3
"""Run trigger evaluation for a skill description.

Tests whether a skill's description causes Claude to trigger (read the skill)
for a set of queries. Outputs results as JSON.

Mechanism: each run creates an isolated temporary project containing the
candidate description installed as a real skill at
<tmp>/.claude/skills/<name>/SKILL.md, and `claude -p` executes with that
project as its working directory. Skills are the only surface `claude -p`
exposes to the model for auto-triggering (files under .claude/commands/
appear in slash_commands but never in the model's available_skills list).
Running in a throwaway project keeps the skill's real name (no suffix),
never touches the user's project, and makes concurrent runs collision-free
by construction: every run gets its own project directory keyed by a full
UUID4. The directory is shared by the run's parallel workers and removed
when the run ends; directories left behind by killed runs are swept once
they are older than --stale-artifact-hours.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
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

# All eval projects live under this root in the OS temp directory.
EVAL_PROJECTS_ROOT = Path(tempfile.gettempdir()) / "claude-skill-evals"

# Leftover eval projects must be at least this old (hours) before the sweep
# removes them: long enough to survive a paused debugging session, short
# enough not to accumulate cruft. Override with --stale-artifact-hours.
DEFAULT_STALE_ARTIFACT_HOURS = 12.0


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
    """Whether a tool_use block is Claude consulting the eval skill.

    Field-scoped on purpose. A plain substring test (the skill name anywhere
    in the serialized input) produces false positives for short names that
    collide with common words or extensions: a skill named "pdf" would count
    a Read of "report.pdf" or a Bash command touching a .pdf as a trigger.
    Only an exact Skill invocation, or a Read of a path inside the skill's
    own directory, is a genuine consult.
    """
    if tool_name == "Skill":
        return (tool_input.get("skill") or "").strip() == eval_skill_name
    if tool_name == "Read":
        # Normalize separators so the match holds on Windows paths too.
        path = (tool_input.get("file_path") or "").replace("\\", "/")
        return f"/{eval_skill_name}/" in path
    return False


def run_single_query(
    query: str,
    eval_skill_name: str,
    timeout: int,
    eval_project_dir: str,
    model: str | None = None,
    claude_cli: str | None = None,
) -> bool:
    """Run a single query and return whether the eval skill was triggered.

    Runs `claude -p` with the isolated eval project as its working
    directory, streams its output, and returns True as soon as a Skill/Read
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
        cwd=eval_project_dir,
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
                        # Accumulate only; the input must be parsed as a whole
                        # to field-scope the match, which partial JSON can't be.
                        accumulated_json += delta.get("partial_json", "")

                elif se_type == "content_block_stop":
                    if pending_tool_name:
                        try:
                            tool_input = (
                                json.loads(accumulated_json) if accumulated_json else {}
                            )
                        except json.JSONDecodeError:
                            tool_input = {}
                        if _tool_use_mentions(
                            eval_skill_name, pending_tool_name, tool_input
                        ):
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


def _sweep_stale_eval_projects(stale_hours: float) -> None:
    """Remove eval projects left behind by previous crashed/killed runs.

    Only directories older than the threshold are removed, so the sweep
    never deletes the live project of a concurrent eval run and survives
    paused debugging sessions.
    """
    if not EVAL_PROJECTS_ROOT.is_dir():
        return
    cutoff = time.time() - stale_hours * 3600
    for entry in EVAL_PROJECTS_ROOT.iterdir():
        if entry.is_dir():
            try:
                if entry.stat().st_mtime < cutoff:
                    shutil.rmtree(entry, ignore_errors=True)
            except OSError:
                pass


def _warn_if_shadowed(skill_name: str) -> None:
    """Warn when a user-level skill with the same name also loads.

    The eval project isolates the candidate from the surrounding project,
    but user-level skills (~/.claude/skills) load in every session. An
    installed copy of the skill carries its own description, so triggers
    it attracts are decided by the wrong description and skew measurement.
    We warn rather than move user files aside.
    """
    installed = Path.home() / ".claude" / "skills" / skill_name
    if installed.is_dir():
        print(
            f"Warning: user-level skill at {installed} shares the eval "
            f"skill's name and also loads during evals; triggers it absorbs "
            f"are decided by its own description, skewing results. Consider "
            f"moving it aside while running evals.",
            file=sys.stderr,
        )


def create_eval_project(
    skill_name: str, skill_description: str, stale_hours: float
) -> Path:
    """Create an isolated throwaway project with the candidate skill.

    The skill keeps its real name — isolation comes from the project
    directory, which is keyed by a full UUID4 so concurrent runs (parallel
    CI jobs included) can never collide. Returns the project directory;
    the caller is responsible for removing it when the run finishes.
    """
    _sweep_stale_eval_projects(stale_hours)
    _warn_if_shadowed(skill_name)

    project_dir = EVAL_PROJECTS_ROOT / f"{skill_name}-{uuid.uuid4().hex}"
    skill_dir = project_dir / ".claude" / "skills" / skill_name
    skill_dir.mkdir(parents=True, exist_ok=True)
    # Use YAML block scalar to avoid breaking on quotes in description
    indented_desc = "\n  ".join(skill_description.split("\n"))
    skill_content = (
        f"---\n"
        f"name: {skill_name}\n"
        f"description: |\n"
        f"  {indented_desc}\n"
        f"---\n\n"
        f"# {skill_name}\n\n"
        f"This skill handles: {skill_description}\n\n"
        f"(Temporary trigger-eval artifact created by skill-creator's "
        f"run_eval.py; safe to delete.)\n"
    )
    (skill_dir / "SKILL.md").write_text(skill_content)
    return project_dir


def run_eval(
    eval_set: list[dict],
    skill_name: str,
    description: str,
    num_workers: int,
    timeout: int,
    project_root: Path | None = None,
    runs_per_query: int = 1,
    trigger_threshold: float = 0.5,
    model: str | None = None,
    stale_artifact_hours: float = DEFAULT_STALE_ARTIFACT_HOURS,
) -> dict:
    """Run the full eval set and return results.

    `project_root` is retained for backward compatibility but no longer
    used: evals run inside an isolated temporary project so they keep the
    skill's real name, never touch the caller's project, and cannot collide
    across concurrent runs.
    """
    del project_root  # Deprecated; see docstring.
    results = []
    claude_cli = resolve_claude_cli()
    # One shared artifact per run: per-worker copies with distinct names but
    # identical descriptions made Claude pick one arbitrarily, so each
    # worker missed triggers that landed on a sibling's copy.
    eval_project_dir = create_eval_project(
        skill_name, description, stale_artifact_hours
    )

    try:
        with ProcessPoolExecutor(max_workers=num_workers) as executor:
            future_to_info = {}
            for item in eval_set:
                for run_idx in range(runs_per_query):
                    future = executor.submit(
                        run_single_query,
                        item["query"],
                        skill_name,
                        timeout,
                        str(eval_project_dir),
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
        shutil.rmtree(eval_project_dir, ignore_errors=True)

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
    parser.add_argument(
        "--stale-artifact-hours",
        type=float,
        default=DEFAULT_STALE_ARTIFACT_HOURS,
        help="Age (hours) before leftover eval projects from crashed runs are swept",
    )
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
        stale_artifact_hours=args.stale_artifact_hours,
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
