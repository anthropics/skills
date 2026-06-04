#!/usr/bin/env python3
"""Run trigger evaluation for a skill description.

Tests whether a skill's description causes Claude to trigger (read the skill)
for a set of queries. Outputs results as JSON.
"""

import argparse
import json
import os
import select
import shutil
import subprocess
import sys
import time
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from scripts.utils import parse_skill_md


def find_project_root() -> Path:
    """Find the project root by walking up from cwd looking for .claude/.

    Only affects the `claude -p` working directory; the candidate skill is
    installed under the user skills dir, which is discovered regardless of cwd.
    """
    current = Path.cwd()
    for parent in [current, *current.parents]:
        if (parent / ".claude").is_dir():
            return parent
    return current


def run_single_query(
    query: str,
    skill_name: str,
    skill_description: str,
    timeout: int,
    project_root: str,
    model: str | None = None,
    skill_body: str = "",
) -> bool:
    """Run a single query and return whether the candidate skill triggered.

    Installs the candidate as a real skill under ~/.claude/skills/<clean_name>/
    so it surfaces to `claude -p` as a Skill-tool target exactly like a
    production install. A `.claude/commands/` file is NOT invoked via the Skill
    tool the way an installed skill is, so action-type skills — where the model
    would otherwise just do the task with Bash — never registered a trigger.

    Detection scans the whole stream and concludes a miss only at the final
    `result` event (or timeout); it does not bail on the first non-Skill tool,
    because a realistic flow is think -> peek with Bash -> invoke the skill, and
    an early Bash must not be scored a miss. Concurrent workers each install an
    identically-described candidate under a distinct uuid, so a query's process
    may invoke a sibling's copy; matching the shared `<skill_name>-skill-`
    prefix (not the exact uuid) keeps that from reading as a miss, since each
    `claude -p` stream is already attributed to one query.
    """
    unique_id = uuid.uuid4().hex[:8]
    clean_name = f"{skill_name}-skill-{unique_id}"
    trigger_marker = f"{skill_name}-skill-"
    skill_dir = Path.home() / ".claude" / "skills" / clean_name
    skill_md = skill_dir / "SKILL.md"

    try:
        skill_dir.mkdir(parents=True, exist_ok=True)
        # YAML block scalar so quotes/newlines in the description can't break the
        # frontmatter. The real body is carried through so the post-trigger flow
        # matches production; the trigger decision is made from name+description.
        indented_desc = "\n  ".join(skill_description.split("\n"))
        body = skill_body.strip() or f"This skill handles: {skill_description}"
        skill_md.write_text(
            f"---\n"
            f"name: {clean_name}\n"
            f"description: |\n"
            f"  {indented_desc}\n"
            f"---\n\n"
            f"{body}\n"
        )

        cmd = [
            "claude",
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
            cwd=project_root,
            env=env,
        )

        start_time = time.time()
        buffer = ""
        pending_tool_name = None
        accumulated_json = ""

        try:
            while time.time() - start_time < timeout:
                exited = process.poll() is not None
                if exited:
                    remaining = process.stdout.read()
                    if remaining:
                        buffer += remaining.decode("utf-8", errors="replace")
                else:
                    ready, _, _ = select.select([process.stdout], [], [], 1.0)
                    if not ready:
                        continue
                    chunk = os.read(process.stdout.fileno(), 8192)
                    if not chunk:
                        exited = True
                    else:
                        buffer += chunk.decode("utf-8", errors="replace")

                while "\n" in buffer:
                    line, buffer = buffer.split("\n", 1)
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        event = json.loads(line)
                    except json.JSONDecodeError:
                        continue

                    if event.get("type") == "stream_event":
                        se = event.get("event", {})
                        se_type = se.get("type", "")
                        if se_type == "content_block_start":
                            cb = se.get("content_block", {})
                            if cb.get("type") == "tool_use":
                                # Watch Skill/Read inputs; ignore any other tool
                                # (an early Bash peek must not score a miss).
                                if cb.get("name", "") in ("Skill", "Read"):
                                    pending_tool_name = cb.get("name", "")
                                    accumulated_json = ""
                                else:
                                    pending_tool_name = None
                        elif se_type == "content_block_delta" and pending_tool_name:
                            delta = se.get("delta", {})
                            if delta.get("type") == "input_json_delta":
                                accumulated_json += delta.get("partial_json", "")
                                if trigger_marker in accumulated_json:
                                    return True
                        elif se_type == "content_block_stop":
                            if pending_tool_name and trigger_marker in accumulated_json:
                                return True
                            pending_tool_name = None

                    # Fallback: full assistant message — scan every tool_use,
                    # not just the first, so a skill call after other tools counts.
                    elif event.get("type") == "assistant":
                        for ci in event.get("message", {}).get("content", []):
                            if ci.get("type") != "tool_use":
                                continue
                            ti = ci.get("input", {})
                            if ci.get("name") == "Skill" and trigger_marker in ti.get("skill", ""):
                                return True
                            if ci.get("name") == "Read" and trigger_marker in ti.get("file_path", ""):
                                return True

                    elif event.get("type") == "result":
                        return False

                if exited:
                    break
        finally:
            # Clean up process on any exit path (return, exception, timeout)
            if process.poll() is None:
                process.kill()
                process.wait()

        return False
    finally:
        shutil.rmtree(skill_dir, ignore_errors=True)


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
    skill_body: str = "",
) -> dict:
    """Run the full eval set and return results."""
    results = []

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
                    str(project_root),
                    model,
                    skill_body,
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
        skill_body=content,
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
