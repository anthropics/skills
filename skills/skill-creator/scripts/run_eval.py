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
import tempfile
import time
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import contextmanager
from pathlib import Path

from scripts.utils import parse_skill_md

DEFAULT_TIMEOUT = 120

# Triggering is an opening move: Claude orients itself (a pwd, an ls) for a
# turn or two, then consults the skill. A probe that hasn't reached for it
# within this many assistant turns is a miss; letting it continue means every
# non-triggering run executes the entire queried task.
MAX_PROBE_TURNS = 4

class SkillAlreadyRegistered(RuntimeError):
    """The skill under test is registered outside the probe root.

    The probe registers a uuid-suffixed decoy and counts invocations of that
    exact name. An installed copy carrying the same description answers the
    same queries under the real name, wins the tie, and every genuine trigger
    scores as a miss -- the 100% precision / 0% recall signature. The probe
    root only isolates project scope; a user-level install or a plugin still
    reaches the probe, so the run is aborted rather than scored.
    """


FIXTURE_HELP = (
    "Directory copied in as each probe's sandbox (default: a bare temp dir). "
    "Point it at a fixture that makes the queries answerable when the skill "
    "needs context, e.g. a throwaway git repo. The original stays untouched."
)


@contextmanager
def probe_root(fixture: Path | None = None):
    """Yield a private project root for one probe run, removed on exit.

    The probe works by registering a throwaway command whose description is the
    one under test, then checking whether Claude invokes that exact command. Two
    things break that, and a private root per probe removes both.

    A root that already registers the real skill loses the race:
    Claude reaches for the real name and the probe scores its own trigger as a
    miss. And probes that share a root see each other's commands, which are
    identical but for the uuid, so a worker can watch for one copy while Claude
    invokes another.

    Args:
        fixture: Directory to copy, for skills whose queries need context to be
            answerable (a git repo, a project tree). Copied rather than used in
            place so parallel probes cannot collide and the original stays
            untouched. Any .claude/skills or .claude/commands the fixture
            carries is stripped from the copy, so the decoy stays the only
            registered skill. When omitted the probe gets a bare directory.

    Yields:
        Path to a temporary directory containing .claude/commands/.
    """
    root = Path(tempfile.mkdtemp(prefix="skill-eval-"))
    try:
        if fixture is not None:
            shutil.copytree(fixture, root, symlinks=True, dirs_exist_ok=True)
            # A fixture carrying its own .claude/skills or .claude/commands
            # would re-register real skills inside the probe root, and the
            # real name outcompetes the decoy: the exact false-miss failure
            # this isolation exists to prevent.
            for leaked in (root / ".claude" / "skills", root / ".claude" / "commands"):
                if leaked.is_symlink():
                    leaked.unlink()
                elif leaked.is_dir():
                    shutil.rmtree(leaked)
        (root / ".claude" / "commands").mkdir(parents=True, exist_ok=True)
        yield root
    finally:
        shutil.rmtree(root, ignore_errors=True)


def run_single_query(
    query: str,
    skill_name: str,
    skill_description: str,
    timeout: int,
    fixture: Path | None = None,
    model: str | None = None,
) -> bool:
    """Run a single query and return whether the skill was triggered.

    Creates a command file in .claude/commands/ so it appears in Claude's
    available_skills list, then runs `claude -p` with the raw query.
    Uses --include-partial-messages to detect triggering early from
    stream events (content_block_start) rather than waiting for the
    full assistant message, which only arrives after tool execution.

    A trigger counts wherever it appears in the run, not only as the opening
    move. On many runs Claude orients itself first (a `pwd`, an `ls`) and
    consults the skill on the next turn, so scoring only the first tool call
    turns that ordering into a coin flip and reports a description as broken
    when it is not. The run ends early on the first matching Skill or Read
    call, before the skill body executes, and stops at MAX_PROBE_TURNS
    assistant turns so a run that was never going to trigger doesn't execute
    the whole task.
    """
    unique_id = uuid.uuid4().hex[:8]
    clean_name = f"{skill_name}-skill-{unique_id}"

    def is_trigger(tool_name: str | None, input_text: str) -> bool:
        return tool_name in ("Skill", "Read") and clean_name in input_text

    def assert_decoy_is_alone(init_event: dict) -> None:
        registered = set(init_event.get("skills") or [])
        registered.update(init_event.get("slash_commands") or [])
        if skill_name in registered:
            raise SkillAlreadyRegistered(
                f"{skill_name!r} is registered outside the probe root (a "
                f"user-level ~/.claude/skills entry or a plugin). It answers "
                f"the queries under its real name, so every trigger would be "
                f"scored as a miss. Remove or rename that copy for the eval."
            )

    with probe_root(fixture) as project_root:
        command_file = project_root / ".claude" / "commands" / f"{clean_name}.md"
        # Use YAML block scalar to avoid breaking on quotes in description
        indented_desc = "\n  ".join(skill_description.split("\n"))
        command_file.write_text(
            f"---\n"
            f"description: |\n"
            f"  {indented_desc}\n"
            f"---\n\n"
            f"# {skill_name}\n\n"
            f"This skill handles: {skill_description}\n"
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

        # Without an explicit stdin the CLI waits several seconds on every
        # probe for piped input that never arrives.
        process = subprocess.Popen(
            cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            cwd=project_root,
            env=env,
        )

        start_time = time.time()
        buffer = ""
        turns = 0
        # Track state for stream event detection
        pending_tool_name = None
        accumulated_json = ""

        try:
            while time.time() - start_time < timeout:
                if process.poll() is not None:
                    remaining = process.stdout.read()
                    if remaining:
                        buffer += remaining.decode("utf-8", errors="replace")
                    break

                ready, _, _ = select.select([process.stdout], [], [], 1.0)
                if not ready:
                    continue

                chunk = os.read(process.stdout.fileno(), 8192)
                if not chunk:
                    break
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

                    if event.get("type") == "system" and event.get("subtype") == "init":
                        assert_decoy_is_alone(event)

                    # Early detection via stream events
                    elif event.get("type") == "stream_event":
                        se = event.get("event", {})
                        se_type = se.get("type", "")

                        if se_type == "content_block_start":
                            cb = se.get("content_block", {})
                            pending_tool_name = (
                                cb.get("name", "") if cb.get("type") == "tool_use" else None
                            )
                            accumulated_json = ""

                        elif se_type == "content_block_delta":
                            delta = se.get("delta", {})
                            if delta.get("type") == "input_json_delta":
                                accumulated_json += delta.get("partial_json", "")
                                if is_trigger(pending_tool_name, accumulated_json):
                                    return True

                        elif se_type == "message_stop":
                            turns += 1
                            if turns >= MAX_PROBE_TURNS:
                                return False

                    # Fallback: full assistant message
                    elif event.get("type") == "assistant":
                        message = event.get("message", {})
                        for content_item in message.get("content", []):
                            if content_item.get("type") != "tool_use":
                                continue
                            if is_trigger(
                                content_item.get("name", ""),
                                json.dumps(content_item.get("input", {})),
                            ):
                                return True

                    elif event.get("type") == "result":
                        return False
        finally:
            # Clean up process on any exit path (return, exception, timeout)
            if process.poll() is None:
                process.kill()
                process.wait()

        return False


def run_eval(
    eval_set: list[dict],
    skill_name: str,
    description: str,
    num_workers: int,
    timeout: int,
    fixture: Path | None = None,
    runs_per_query: int = 1,
    trigger_threshold: float = 0.5,
    model: str | None = None,
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
                    fixture,
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
            except SkillAlreadyRegistered:
                # Scoring this as a failed probe would report the silent 0%
                # this check exists to catch.
                raise
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
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, help="Timeout per query in seconds")
    parser.add_argument("--fixture", default=None, help=FIXTURE_HELP)
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
    fixture = Path(args.fixture) if args.fixture else None
    if fixture and not fixture.is_dir():
        # copytree failures inside the pool are caught per probe and scored
        # False, so a typo'd path would report a plausible 0/N instead of
        # failing loudly here.
        print(f"Error: fixture directory not found: {fixture}", file=sys.stderr)
        sys.exit(1)

    if args.verbose:
        print(f"Fixture: {fixture or 'none (bare temp dir per probe)'}", file=sys.stderr)
        print(f"Evaluating: {description}", file=sys.stderr)

    try:
        output = run_eval(
            eval_set=eval_set,
            skill_name=name,
            description=description,
            num_workers=args.num_workers,
            timeout=args.timeout,
            fixture=fixture,
            runs_per_query=args.runs_per_query,
            trigger_threshold=args.trigger_threshold,
            model=args.model,
        )
    except SkillAlreadyRegistered as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

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
