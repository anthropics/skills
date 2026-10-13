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
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import contextmanager, suppress
from pathlib import Path

from scripts.utils import parse_skill_md

DEFAULT_TIMEOUT = 120
MAX_PROBE_TURNS = 4
PROBE_TOOLS = ("Skill", "Read", "Glob", "Grep")
PROBE_SETTING_SOURCES = "project,local"


class SkillAlreadyRegistered(RuntimeError):
    """The skill's name is registered in the probe environment.

    The probe registers a uuid-suffixed decoy and counts invocations of that
    exact name. A skill registered under the real name competes for the same
    queries, and every trigger it wins scores as a miss -- the 100% precision
    / 0% recall signature. Probes load no user settings, so user-level skills
    and user-enabled plugins never reach them; what remains is a built-in
    skill or command, or a managed-policy install, so the run is aborted
    rather than scored.
    """


FIXTURE_HELP = (
    "Directory copied in as each probe's sandbox (default: a bare temp dir). "
    "Point it at a fixture that makes the queries answerable when the skill "
    "needs context, e.g. a throwaway git repo. The original stays untouched, "
    "except through symlinks inside it, which are copied as links."
)


def fixture_dir(value: str) -> Path:
    """Argparse type for --fixture: an existing directory."""
    path = Path(value)
    if not path.is_dir():
        raise argparse.ArgumentTypeError(f"fixture directory not found: {path}")
    return path


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
            untouched. The fixture's .claude/skills and .claude/commands are
            not copied, so it cannot register a competing copy of the skill;
            a .claude that is a symlink or a file is not copied either. Other
            symlinks are copied as links, so a probe writing through one
            reaches its target. When omitted the probe gets a bare directory.

    Yields:
        Path to a temporary directory containing .claude/commands/.
    """
    with tempfile.TemporaryDirectory(prefix="skill-eval-", ignore_cleanup_errors=True) as tmp:
        root = Path(tmp)
        if fixture is not None:
            fixture_claude = fixture / ".claude"

            def skip_registrations(directory: str, names: list[str]) -> set[str]:
                current = Path(directory)
                if current == fixture and (fixture_claude.is_symlink() or fixture_claude.is_file()):
                    return {".claude"}
                if current == fixture_claude:
                    return {"skills", "commands"}
                return set()

            shutil.copytree(
                fixture, root, symlinks=True, dirs_exist_ok=True, ignore=skip_registrations
            )
        (root / ".claude" / "commands").mkdir(parents=True, exist_ok=True)
        yield root


def _claude_command(query: str, model: str | None) -> list[str]:
    """Build the `claude -p` command every probe runs.

    Probes load project and local settings only, so the user's skills,
    plugins, permission mode, and allow rules stay out, and they get only
    the tools needed to orient and to trigger, none of which can change
    anything. MCP servers are left out for the same reason.
    """
    cmd = [
        "claude",
        "-p", query,
        "--output-format", "stream-json",
        "--verbose",
        "--include-partial-messages",
        "--setting-sources", PROBE_SETTING_SOURCES,
        "--strict-mcp-config",
        "--tools", *PROBE_TOOLS,
    ]
    if model:
        cmd.extend(["--model", model])
    return cmd


def _start_claude(cmd: list[str], cwd: Path) -> subprocess.Popen:
    # Remove CLAUDECODE env var to allow nesting claude -p inside a
    # Claude Code session. The guard is for interactive terminal conflicts;
    # programmatic subprocess usage is safe.
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    return subprocess.Popen(
        cmd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        cwd=cwd,
        env=env,
        start_new_session=True,
    )


def _stop_claude(process: subprocess.Popen) -> None:
    with suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def _events(process: subprocess.Popen, timeout: int):
    """Yield parsed stream-json events until EOF or timeout."""
    start_time = time.time()
    buffer = ""
    exited = False
    while not exited and time.time() - start_time < timeout:
        ready, _, _ = select.select([process.stdout], [], [], 1.0)
        if not ready:
            continue
        chunk = os.read(process.stdout.fileno(), 8192)
        exited = not chunk
        buffer += chunk.decode("utf-8", errors="replace")

        while "\n" in buffer:
            line, buffer = buffer.split("\n", 1)
            line = line.strip()
            if not line:
                continue
            try:
                yield json.loads(line)
            except json.JSONDecodeError:
                continue


def assert_not_registered(skill_name: str, timeout: int, model: str | None = None) -> None:
    """Raise SkillAlreadyRegistered if skill_name is visible to a probe.

    Starts one probe session without a decoy and reads its init event, which
    lists every registered skill and command, plugin ones as
    '<plugin>:<name>'. The session is stopped as soon as that event arrives.
    """
    with probe_root() as root:
        process = _start_claude(_claude_command("ok", model), root)
        try:
            init = next(
                (
                    event for event in _events(process, timeout)
                    if event.get("type") == "system" and event.get("subtype") == "init"
                ),
                None,
            )
        finally:
            _stop_claude(process)
    if init is None:
        raise RuntimeError("claude -p produced no init event; is the CLI installed and logged in?")
    names = [*(init.get("skills") or []), *(init.get("slash_commands") or [])]
    if skill_name in {name.rsplit(":", 1)[-1] for name in names}:
        raise SkillAlreadyRegistered(
            f"{skill_name!r} is registered even with user settings excluded, "
            f"so it is a built-in skill or command or a managed-policy "
            f"install. It competes with the decoy under the real name and "
            f"every trigger it wins would be scored as a miss. Rename the "
            f"skill under test to evaluate it."
        )


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

    A Skill call on the decoy counts wherever it appears in the run, not only
    as the opening move: Claude often orients itself first (a Glob) and
    consults the skill on the next turn, and scoring only the first tool call
    turns that ordering into a coin flip. A Read of the decoy file counts only
    as the first tool call; after any other call it may just be Claude
    opening a file it found while exploring the sandbox. The run ends early
    on a trigger, before the skill body executes, and stops at
    MAX_PROBE_TURNS assistant turns.
    """
    unique_id = uuid.uuid4().hex[:8]
    clean_name = f"{skill_name}-skill-{unique_id}"

    def can_trigger(tool_name: str | None, prior_calls: int) -> bool:
        return tool_name == "Skill" or (tool_name == "Read" and prior_calls == 0)

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

        process = _start_claude(_claude_command(query, model), project_root)
        turns = 0
        # Track state for stream event detection
        stream_calls = 0
        message_calls = 0
        pending_trigger = False
        accumulated_json = ""

        try:
            for event in _events(process, timeout):
                # Early detection via stream events
                if event.get("type") == "stream_event":
                    se = event.get("event", {})
                    se_type = se.get("type", "")

                    if se_type == "content_block_start":
                        cb = se.get("content_block", {})
                        pending_trigger = False
                        if cb.get("type") == "tool_use":
                            pending_trigger = can_trigger(cb.get("name"), stream_calls)
                            stream_calls += 1
                        accumulated_json = ""

                    elif se_type == "content_block_delta" and pending_trigger:
                        delta = se.get("delta", {})
                        if delta.get("type") == "input_json_delta":
                            accumulated_json += delta.get("partial_json", "")
                            if clean_name in accumulated_json:
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
                        triggers = can_trigger(content_item.get("name"), message_calls)
                        message_calls += 1
                        if triggers and clean_name in json.dumps(content_item.get("input", {})):
                            return True

                elif event.get("type") == "result":
                    return False
        finally:
            _stop_claude(process)

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
    assert_not_registered(skill_name, timeout, model)
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
    parser.add_argument("--fixture", type=fixture_dir, default=None, help=FIXTURE_HELP)
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
    if args.verbose:
        print(f"Fixture: {args.fixture or 'none (bare temp dir per probe)'}", file=sys.stderr)
        print(f"Evaluating: {description}", file=sys.stderr)

    try:
        output = run_eval(
            eval_set=eval_set,
            skill_name=name,
            description=description,
            num_workers=args.num_workers,
            timeout=args.timeout,
            fixture=args.fixture,
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
