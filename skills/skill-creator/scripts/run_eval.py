#!/usr/bin/env python3
"""Run trigger evaluation for a skill description.

Tests whether a skill's description causes Claude to trigger (read the skill)
for a set of queries. Outputs results as JSON.

Mechanism: atomically swaps the candidate description into the real
~/.claude/skills/<name>/SKILL.md frontmatter, runs `claude -p <query>` for
each test query, watches the stream for a Skill tool invocation matching
the real skill name, then restores the original SKILL.md. Tests the
production skill-router path with no mocks.
"""

import argparse
import atexit
import json
import os
import re
import select
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

try:
    import fcntl  # POSIX only — used for cross-process flock on SKILL.md
    _HAS_FCNTL = True
except ImportError:
    _HAS_FCNTL = False  # Windows: in-process lock only

from scripts.utils import parse_skill_md


def find_project_root() -> Path:
    """Find the project root by walking up from cwd looking for .claude/."""
    current = Path.cwd()
    for parent in [current, *current.parents]:
        if (parent / ".claude").is_dir():
            return parent
    return current


_FRONTMATTER_RE = re.compile(r"^---\n(.*?)\n---\n", re.DOTALL)


def _replace_description_in_frontmatter(content: str, new_description: str) -> str:
    """Replace description field in YAML frontmatter with a block scalar.

    Handles all four YAML description forms (single-line, quoted, |, >, |-, >-)
    by removing the existing description (and any continuation block) and
    inserting `description: |-` followed by indented body. Preserves
    every other frontmatter field and the post-frontmatter content.
    """
    match = _FRONTMATTER_RE.match(content)
    if not match:
        raise ValueError("SKILL.md missing frontmatter (no opening ---\\n...---\\n block)")

    fm_body = match.group(1)
    rest = content[match.end():]

    lines = fm_body.split("\n")
    out_lines: list[str] = []
    i = 0
    inserted = False
    while i < len(lines):
        line = lines[i]
        if line.startswith("description:"):
            value = line[len("description:"):].strip()
            i += 1
            if value in (">", "|", ">-", "|-"):
                while i < len(lines) and (lines[i].startswith("  ") or lines[i].startswith("\t") or lines[i].strip() == ""):
                    i += 1
            indented = "\n".join("  " + bl for bl in new_description.split("\n"))
            out_lines.append(f"description: |-\n{indented}")
            inserted = True
            continue
        out_lines.append(line)
        i += 1

    if not inserted:
        indented = "\n".join("  " + bl for bl in new_description.split("\n"))
        out_lines.append(f"description: |-\n{indented}")

    new_fm = "\n".join(out_lines)
    return f"---\n{new_fm}\n---\n{rest}"


def _atomic_write(path: Path, content: str) -> None:
    """Write file atomically via tmp+rename in the same directory."""
    tmp = path.with_suffix(path.suffix + ".swap-tmp")
    tmp.write_text(content)
    tmp.replace(path)


_active_swaps: dict[str, str] = {}
_lock_handles: dict[str, "object"] = {}  # path -> open file handle holding flock
_swap_lock = threading.Lock()


def _acquire_flock(skill_md: Path):
    """Acquire an exclusive cross-process lock on a sidecar `.swap-lock` file.

    Returns the open file handle (must stay open while the lock is held).
    Blocks until the lock is available — concurrent invocations against the
    same SKILL.md serialise here instead of racing on the file.

    On non-POSIX (no fcntl) returns None and falls back to in-process locking
    only — cross-process safety is best-effort.
    """
    if not _HAS_FCNTL:
        return None
    lock_path = skill_md.with_suffix(".md.swap-lock")
    f = open(lock_path, "w")  # noqa: SIM115 — caller owns lifecycle
    try:
        fcntl.flock(f.fileno(), fcntl.LOCK_EX)
    except Exception:
        f.close()
        raise
    return f


def _release_flock(handle) -> None:
    if handle is None:
        return
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    finally:
        try:
            handle.close()
        except Exception:
            pass


def _restore_all_active_swaps() -> None:
    """atexit/signal handler — restore every SKILL.md still in swap state."""
    with _swap_lock:
        items = list(_active_swaps.items())
        handles = list(_lock_handles.items())
        _active_swaps.clear()
        _lock_handles.clear()
    for skill_md_str, original in items:
        try:
            _atomic_write(Path(skill_md_str), original)
            backup = Path(skill_md_str).with_suffix(".md.swap-backup")
            backup.unlink(missing_ok=True)
        except Exception as e:
            print(f"WARN: failed to restore {skill_md_str}: {e}", file=sys.stderr)
    for _path, h in handles:
        _release_flock(h)


atexit.register(_restore_all_active_swaps)


def _signal_handler(signum, frame):
    _restore_all_active_swaps()
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)


for _sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    try:
        signal.signal(_sig, _signal_handler)
    except (OSError, ValueError):
        pass


def swap_skill_description(skill_path: Path, new_description: str) -> str:
    """Replace description in real SKILL.md atomically. Return original full content.

    Acquires an exclusive cross-process flock on `<skill>/SKILL.md.swap-lock`
    before mutating, so concurrent runs against the same skill serialise
    cleanly instead of racing. The lock is held until `restore_skill_md`
    is called.

    Writes a sibling `.md.swap-backup` first as crash-safety: if the Python
    process dies between swap and restore, the user can manually restore
    from the backup file.
    """
    skill_md = skill_path / "SKILL.md"
    handle = _acquire_flock(skill_md)
    try:
        original = skill_md.read_text()
        new_content = _replace_description_in_frontmatter(original, new_description)

        backup = skill_md.with_suffix(".md.swap-backup")
        backup.write_text(original)

        _atomic_write(skill_md, new_content)

        with _swap_lock:
            _active_swaps[str(skill_md)] = original
            if handle is not None:
                _lock_handles[str(skill_md)] = handle
    except Exception:
        _release_flock(handle)
        raise
    return original


def restore_skill_md(skill_path: Path, original: str) -> None:
    """Restore SKILL.md, remove the swap backup file, release the flock."""
    skill_md = skill_path / "SKILL.md"
    _atomic_write(skill_md, original)
    backup = skill_md.with_suffix(".md.swap-backup")
    backup.unlink(missing_ok=True)
    with _swap_lock:
        _active_swaps.pop(str(skill_md), None)
        handle = _lock_handles.pop(str(skill_md), None)
    _release_flock(handle)


def run_single_query(
    query: str,
    skill_name: str,
    timeout: int,
    project_root: str,
    model: str | None = None,
) -> bool:
    """Run a single query against the real skill-router and report whether
    the named skill was invoked.

    Spawns `claude -p <query> --output-format stream-json --include-partial-messages`,
    watches the NDJSON stream for a `tool_use` block where:
      - tool name is "Skill" and `input.skill == skill_name`, OR
      - tool name is "Read" and the path contains `/skills/<skill_name>/SKILL.md`
    Returns on first decision (early exit on first tool_use block) or on
    `message_stop` / `result` event.

    Caller must have already swapped the candidate description into
    ~/.claude/skills/<skill_name>/SKILL.md. This function does not touch
    SKILL.md — it only observes router behaviour.
    """
    cmd = [
        "claude",
        "-p", query,
        "--output-format", "stream-json",
        "--verbose",
        "--include-partial-messages",
    ]
    if model:
        cmd.extend(["--model", model])

    env = os.environ.copy()
    env["BROWSER"] = "false"
    env["PLAYWRIGHT_SKIP_BROWSER_DOWNLOAD"] = "1"

    process = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        cwd=project_root,
        env=env,
    )

    triggered = False
    start_time = time.time()
    buffer = ""
    pending_tool_name: str | None = None
    accumulated_json = ""

    skill_md_marker = f"/skills/{skill_name}/SKILL.md"

    def matches(tool_name: str, raw_input: str) -> bool:
        if tool_name == "Skill":
            try:
                parsed = json.loads(raw_input) if raw_input else {}
                return parsed.get("skill") == skill_name
            except json.JSONDecodeError:
                return f'"skill":"{skill_name}"' in raw_input or f'"skill": "{skill_name}"' in raw_input
        if tool_name == "Read":
            return skill_md_marker in raw_input
        return False

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
                                inline_input = cb.get("input")
                                if inline_input:
                                    if matches(tool_name, json.dumps(inline_input)):
                                        return True
                            else:
                                return False

                    elif se_type == "content_block_delta" and pending_tool_name:
                        delta = se.get("delta", {})
                        if delta.get("type") == "input_json_delta":
                            accumulated_json += delta.get("partial_json", "")
                            if matches(pending_tool_name, accumulated_json):
                                return True

                    elif se_type in ("content_block_stop", "message_stop"):
                        if pending_tool_name:
                            return matches(pending_tool_name, accumulated_json)
                        if se_type == "message_stop":
                            return False

                elif event.get("type") == "assistant":
                    message = event.get("message", {})
                    for content_item in message.get("content", []):
                        if content_item.get("type") != "tool_use":
                            continue
                        tool_name = content_item.get("name", "")
                        tool_input = content_item.get("input", {})
                        if tool_name == "Skill" and tool_input.get("skill") == skill_name:
                            triggered = True
                        elif tool_name == "Read" and skill_md_marker in tool_input.get("file_path", ""):
                            triggered = True
                        return triggered

                elif event.get("type") == "result":
                    return triggered
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()

    return triggered


def run_eval(
    eval_set: list[dict],
    skill_name: str,
    description: str,
    num_workers: int,
    timeout: int,
    project_root: Path,
    skill_path: Path,
    runs_per_query: int = 1,
    trigger_threshold: float = 0.5,
    model: str | None = None,
) -> dict:
    """Run the full eval set with a single description swap.

    Swaps the candidate description into the real SKILL.md ONCE, runs all
    parallel workers against the swapped skill, then restores. Description
    is stable for the entire iteration so parallel workers are safe.
    """
    original_content = swap_skill_description(skill_path, description)

    try:
        results: list[dict] = []

        with ProcessPoolExecutor(max_workers=num_workers) as executor:
            future_to_info: dict = {}
            for item in eval_set:
                for run_idx in range(runs_per_query):
                    future = executor.submit(
                        run_single_query,
                        item["query"],
                        skill_name,
                        timeout,
                        str(project_root),
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
                except Exception as exc:
                    print(f"Warning: query failed: {exc}", file=sys.stderr)
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
    finally:
        restore_skill_md(skill_path, original_content)


def main():
    parser = argparse.ArgumentParser(description="Run trigger evaluation for a skill description")
    parser.add_argument("--eval-set", required=True, help="Path to eval set JSON file")
    parser.add_argument("--skill-path", required=True, help="Path to skill directory")
    parser.add_argument("--description", default=None, help="Override description to test")
    parser.add_argument("--num-workers", type=int, default=4, help="Number of parallel workers")
    parser.add_argument("--timeout", type=int, default=30, help="Timeout per query in seconds")
    parser.add_argument("--runs-per-query", type=int, default=3, help="Number of runs per query")
    parser.add_argument("--trigger-threshold", type=float, default=0.5, help="Trigger rate threshold")
    parser.add_argument("--model", default=None, help="Model to use for claude -p (default: user's configured model)")
    parser.add_argument("--verbose", action="store_true", help="Print progress to stderr")
    args = parser.parse_args()

    eval_set = json.loads(Path(args.eval_set).read_text())
    skill_path = Path(args.skill_path).resolve()

    if not (skill_path / "SKILL.md").exists():
        print(f"Error: No SKILL.md found at {skill_path}", file=sys.stderr)
        sys.exit(1)

    name, original_description, _ = parse_skill_md(skill_path)
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
        skill_path=skill_path,
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
