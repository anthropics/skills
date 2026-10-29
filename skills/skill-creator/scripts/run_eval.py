#!/usr/bin/env python3
"""Run trigger evaluation for a skill description.

Tests whether a skill's description causes Claude to trigger (read the skill)
for a set of queries. Outputs results as JSON.
"""

import argparse
import json
import os
import queue
import subprocess
import sys
import threading
import time
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from scripts.utils import parse_skill_md


def find_project_root() -> Path:
    """Find the project root by walking up from cwd looking for .claude/.

    Mimics how Claude Code discovers its project root, so the command file
    we create ends up where claude -p will look for it.
    """
    current = Path.cwd()
    for parent in [current, *current.parents]:
        if (parent / ".claude").is_dir():
            return parent
    return current


class TriggerDetector:
    """Incremental state machine over `claude -p --output-format stream-json` lines.

    Kept separate from process handling so it can be exercised against recorded
    transcripts without spawning Claude.
    """

    def __init__(self, clean_name: str, scan_full_turn: bool = False):
        self.clean_name = clean_name
        self.scan_full_turn = scan_full_turn
        self.pending_tool_name = None
        self.accumulated_json = ""
        self.triggered = False

    def feed(self, line: str) -> bool | None:
        """Consume one line. Returns the verdict once known, else None."""
        line = line.strip()
        if not line:
            return None

        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            return None

        if event.get("type") == "stream_event":
            se = event.get("event", {})
            se_type = se.get("type", "")

            if se_type == "content_block_start":
                cb = se.get("content_block", {})
                if cb.get("type") == "tool_use":
                    tool_name = cb.get("name", "")
                    if tool_name in ("Skill", "Read"):
                        self.pending_tool_name = tool_name
                        self.accumulated_json = ""
                    elif not self.scan_full_turn:
                        return False
                    else:
                        self.pending_tool_name = None
                        self.accumulated_json = ""

            elif se_type == "content_block_delta" and self.pending_tool_name:
                delta = se.get("delta", {})
                if delta.get("type") == "input_json_delta":
                    self.accumulated_json += delta.get("partial_json", "")
                    if self.clean_name in self.accumulated_json:
                        return True

            elif se_type in ("content_block_stop", "message_stop"):
                if self.pending_tool_name:
                    matched = self.clean_name in self.accumulated_json
                    if matched or not self.scan_full_turn:
                        return matched
                    self.pending_tool_name = None
                    self.accumulated_json = ""
                elif se_type == "message_stop" and not self.scan_full_turn:
                    return False

        elif event.get("type") == "assistant":
            message = event.get("message", {})
            for content_item in message.get("content", []):
                if content_item.get("type") != "tool_use":
                    continue
                tool_name = content_item.get("name", "")
                tool_input = content_item.get("input", {})
                if tool_name == "Skill" and self.clean_name in tool_input.get("skill", ""):
                    self.triggered = True
                elif tool_name == "Read" and self.clean_name in tool_input.get("file_path", ""):
                    self.triggered = True
                if self.triggered or not self.scan_full_turn:
                    return self.triggered

        elif event.get("type") == "result":
            return self.triggered

        return None


def detect_trigger(lines, clean_name: str, scan_full_turn: bool = False) -> bool:
    """Run TriggerDetector over an iterable of lines and return the verdict."""
    detector = TriggerDetector(clean_name, scan_full_turn=scan_full_turn)
    for line in lines:
        verdict = detector.feed(line)
        if verdict is not None:
            return verdict
    return detector.triggered


def iter_process_lines(stream, deadline_check, poll_interval: float = 1.0):
    """Yield decoded lines from `stream` as they arrive.

    A reader thread feeds a queue so the main loop can still honour a timeout.
    `select` is not usable here: on Windows it accepts sockets only, and calling
    it on a pipe raises OSError, which the caller records as a non-trigger, so
    every query is silently scored as a miss.
    """
    chunks: queue.Queue = queue.Queue()

    def pump():
        try:
            while True:
                data = stream.read1(8192)
                if not data:
                    break
                chunks.put(data)
        except (ValueError, OSError):
            pass
        finally:
            chunks.put(None)

    threading.Thread(target=pump, daemon=True).start()

    buffer = ""
    while deadline_check():
        try:
            chunk = chunks.get(timeout=poll_interval)
        except queue.Empty:
            continue
        if chunk is None:
            break
        buffer += chunk.decode("utf-8", errors="replace")
        while "\n" in buffer:
            line, buffer = buffer.split("\n", 1)
            yield line
    if buffer:
        yield buffer


def resolve_probe_name(skill_name: str, unique_id: str, use_installed: bool) -> str:
    """Name the eval looks for inside the Skill tool call.

    When the skill under test is not installed, a uniquely-named copy is written
    into .claude/commands/ and that name is what Claude invokes. When the skill
    IS already installed, Claude invokes the real skill instead, the unique probe
    name never appears, and matching on it reports a false miss for every query.
    """
    return skill_name if use_installed else f"{skill_name}-skill-{unique_id}"


def run_single_query(
    query: str,
    skill_name: str,
    skill_description: str,
    timeout: int,
    project_root: str,
    model: str | None = None,
    use_installed: bool = False,
    scan_full_turn: bool = False,
) -> bool:
    """Run a single query and return whether the skill was triggered.

    Unless `use_installed` is set, creates a command file in .claude/commands/ so
    the description under test appears in the available_skills list. Uses
    --include-partial-messages to detect triggering early from stream events
    rather than waiting for the full assistant message.
    """
    unique_id = uuid.uuid4().hex[:8]
    clean_name = resolve_probe_name(skill_name, unique_id, use_installed)
    project_commands_dir = Path(project_root) / ".claude" / "commands"
    command_file = project_commands_dir / f"{clean_name}.md"

    try:
        if not use_installed:
            project_commands_dir.mkdir(parents=True, exist_ok=True)
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
        try:
            lines = iter_process_lines(
                process.stdout, lambda: time.time() - start_time < timeout
            )
            return detect_trigger(lines, clean_name, scan_full_turn=scan_full_turn)
        finally:
            # Clean up process on any exit path (return, exception, timeout)
            if process.poll() is None:
                process.kill()
                process.wait()
    finally:
        if not use_installed and command_file.exists():
            command_file.unlink()


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
    use_installed: bool = False,
    scan_full_turn: bool = False,
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
                    use_installed,
                    scan_full_turn,
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
    parser.add_argument(
        "--scan-full-turn",
        action="store_true",
        help="Keep looking for the Skill call until the turn ends, instead of "
             "giving up at the first tool call that is not Skill or Read. Detects "
             "skills that Claude reaches for after an initial inspection step. "
             "Slower, because each query runs to completion instead of exiting "
             "as soon as the first tool block resolves.",
    )
    parser.add_argument(
        "--use-installed",
        action="store_true",
        help="Match the skill by its real name instead of writing a uniquely-named "
             "probe copy. Use when the skill under test is already installed, since "
             "Claude invokes the real skill and the probe name never appears.",
    )
    args = parser.parse_args()

    if args.use_installed and args.description:
        parser.error(
            "--description cannot be combined with --use-installed: the override is "
            "injected through the probe copy, so with --use-installed the installed "
            "skill supplies the description and the override is silently ignored."
        )

    eval_set = json.loads(Path(args.eval_set).read_text(encoding="utf-8"))
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
        use_installed=args.use_installed,
        scan_full_turn=args.scan_full_turn,
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
