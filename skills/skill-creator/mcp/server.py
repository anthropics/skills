"""skill_eval_mcp — MCP server exposing skill-creator's Phase 3 trigger
evaluation pipeline to LLMs.

Tools (all `skill_eval_*` service-prefixed):
  - skill_eval_list_skills            : enumerate installed skills
  - skill_eval_get_skill              : description + candidate eval sets
  - skill_eval_run_trigger_eval       : sync, single description against an eval set
  - skill_eval_start_optimization     : async, returns run_id
  - skill_eval_get_run_status         : poll a run by id
  - skill_eval_list_runs              : list active + recent runs
  - skill_eval_apply_best_description : write winning description back to SKILL.md
  - skill_eval_stop_run               : cooperative stop

Transport: stdio (local Claude Code integration). No auth — inherits the
parent CC session's OAuth when `claude -p` subprocesses are spawned by
the underlying `run_loop` / `run_eval`.
"""

from __future__ import annotations

import json
import sys
import threading
import time
import uuid
from pathlib import Path
from typing import Optional

from mcp.server.fastmcp import FastMCP
from pydantic import BaseModel, ConfigDict, Field

# Make scripts.* importable from skill-creator/
SKILL_CREATOR_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SKILL_CREATOR_DIR))

from scripts.run_eval import (  # noqa: E402
    _atomic_write,
    _replace_description_in_frontmatter,
    find_project_root,
    run_eval as _run_eval,
)
from scripts.run_loop import run_loop as _run_loop  # noqa: E402
from scripts.utils import parse_skill_md  # noqa: E402

SKILLS_DIR = Path.home() / ".claude" / "skills"

mcp = FastMCP("skill_eval_mcp")

_runs: dict[str, dict] = {}
_runs_lock = threading.Lock()


# ---------- Pydantic input models ----------

class _StrictModel(BaseModel):
    model_config = ConfigDict(
        str_strip_whitespace=True,
        validate_assignment=True,
        extra="forbid",
    )


class ListSkillsInput(_StrictModel):
    """No parameters."""


class GetSkillInput(_StrictModel):
    name: str = Field(
        ...,
        min_length=1,
        max_length=200,
        description="Skill directory name under ~/.claude/skills/, e.g. 'medusa-pro'",
    )


class RunTriggerInput(_StrictModel):
    skill_path: str = Field(..., description="Absolute path to skill directory containing SKILL.md")
    eval_set_path: str = Field(..., description="Absolute path to JSON eval set (list of {query, should_trigger})")
    description: Optional[str] = Field(
        default=None,
        description="Override description to test. If omitted, uses existing SKILL.md description.",
    )
    model: str = Field(default="claude-sonnet-4-6", description="Claude model id (e.g. claude-sonnet-4-6, claude-haiku-4-5).")
    num_workers: int = Field(default=1, ge=1, le=8, description="Parallel `claude -p` workers per iteration.")
    runs_per_query: int = Field(default=1, ge=1, le=5, description="How many times to run each query for stability.")
    timeout: int = Field(default=60, ge=15, le=300, description="Per-query subprocess timeout in seconds.")
    trigger_threshold: float = Field(default=0.5, ge=0.0, le=1.0, description="Pass threshold on trigger rate.")


class StartOptimizationInput(RunTriggerInput):
    max_iterations: int = Field(default=3, ge=1, le=10, description="Max improvement iterations.")
    holdout: float = Field(default=0.4, ge=0.0, le=0.7, description="Test/train holdout fraction (stratified). 0 disables.")


class RunIdInput(_StrictModel):
    run_id: str = Field(..., min_length=1, description="Run identifier returned by skill_eval_start_optimization.")


# ---------- helpers ----------

def _enumerate_skills() -> list[dict]:
    if not SKILLS_DIR.is_dir():
        return []
    out = []
    for p in sorted(SKILLS_DIR.iterdir()):
        if not p.exists():
            continue
        try:
            real = p.resolve()
        except OSError:
            continue
        if not (real / "SKILL.md").is_file():
            continue
        try:
            name, desc, _ = parse_skill_md(real)
        except Exception:
            continue
        out.append({
            "name": name,
            "link_path": str(p),
            "real_path": str(real),
            "description_preview": desc[:160],
            "description_len": len(desc),
        })
    return out


def _discover_candidates(skill_real: Path, name: str) -> list[dict]:
    candidates: list[dict] = []
    seen: set[str] = set()
    roots = [
        skill_real / "evals",
        skill_real / "resources",
        skill_real.parent / f"{name}-workspace",
    ]
    for root in roots:
        if not root.is_dir():
            continue
        for f in root.rglob("*.json"):
            if str(f) in seen:
                continue
            try:
                data = json.loads(f.read_text())
            except Exception:
                continue
            if not isinstance(data, list) or not data or not isinstance(data[0], dict):
                continue
            if "should_trigger" not in data[0] or "query" not in data[0]:
                continue
            should_count = sum(1 for q in data if q.get("should_trigger"))
            candidates.append({
                "path": str(f),
                "size": len(data),
                "should_trigger": should_count,
                "should_not_trigger": len(data) - should_count,
            })
            seen.add(str(f))
    candidates.sort(key=lambda c: c["size"], reverse=True)
    return candidates


def _summarize(results: list[dict]) -> dict:
    """Compute precision / recall / accuracy from per-query results."""
    tp = fp = tn = fn = 0
    for r in results:
        runs = r.get("runs", 0)
        triggers = r.get("triggers", 0)
        if r.get("should_trigger"):
            tp += triggers
            fn += runs - triggers
        else:
            fp += triggers
            tn += runs - triggers
    total = tp + fp + tn + fn
    return {
        "tp": tp, "fp": fp, "tn": tn, "fn": fn,
        "precision": tp / (tp + fp) if (tp + fp) else 1.0,
        "recall": tp / (tp + fn) if (tp + fn) else 1.0,
        "accuracy": (tp + tn) / total if total else 0.0,
    }


def _err(msg: str) -> dict:
    return {"isError": True, "error": msg}


# ---------- Tools ----------

@mcp.tool(
    name="skill_eval_list_skills",
    annotations={
        "title": "List installed skills",
        "readOnlyHint": True,
        "destructiveHint": False,
        "idempotentHint": True,
        "openWorldHint": False,
    },
)
async def skill_eval_list_skills(params: ListSkillsInput) -> str:
    """Enumerate every skill under ~/.claude/skills/ that has a valid SKILL.md.

    Returns:
        JSON object with `count` and `skills` array. Each skill has `name`,
        `link_path`, `real_path`, `description_preview` (first 160 chars),
        and `description_len`.

    Use when: agent needs to know which skills are evaluable on this machine,
    or needs to fuzzy-match a name the user mentioned.
    """
    skills = _enumerate_skills()
    return json.dumps({"count": len(skills), "skills": skills}, indent=2)


@mcp.tool(
    name="skill_eval_get_skill",
    annotations={
        "title": "Get skill metadata",
        "readOnlyHint": True,
        "destructiveHint": False,
        "idempotentHint": True,
        "openWorldHint": False,
    },
)
async def skill_eval_get_skill(params: GetSkillInput) -> str:
    """Get a skill's full description and auto-discovered candidate eval sets.

    Args:
        name (str): Skill name as it appears under ~/.claude/skills/.

    Returns:
        JSON object with `name`, `description`, `skill_path`, and
        `eval_candidates`. Each candidate has `path`, `size`,
        `should_trigger` count, `should_not_trigger` count.

    Eval set discovery looks under <skill>/evals/, <skill>/resources/,
    and the sibling <skill>-workspace/ directory for JSON files matching
    [{query, should_trigger}, ...].

    Use when: agent needs the canonical description before testing a
    proposed rewrite, or needs to discover existing eval sets to reuse.
    """
    p = SKILLS_DIR / params.name
    if not (p / "SKILL.md").exists():
        return json.dumps(_err(f"no skill named '{params.name}' found at {p}"))
    real = p.resolve()
    name, desc, _ = parse_skill_md(real)
    return json.dumps({
        "name": name,
        "description": desc,
        "skill_path": str(real),
        "eval_candidates": _discover_candidates(real, name),
    }, indent=2)


@mcp.tool(
    name="skill_eval_run_trigger_eval",
    annotations={
        "title": "Run trigger eval (single shot, no improvement loop)",
        "readOnlyHint": False,
        "destructiveHint": False,
        "idempotentHint": False,
        "openWorldHint": True,
    },
)
async def skill_eval_run_trigger_eval(params: RunTriggerInput) -> str:
    """Run a single trigger evaluation pass. Synchronous — blocks until complete.

    Mechanism: temporarily writes the candidate description into the real
    ~/.claude/skills/<name>/SKILL.md, runs `claude -p` subprocesses for
    every query in the eval set, observes which queries cause the skill
    to load, then restores the original SKILL.md.

    Args:
        skill_path (str): absolute path to skill dir
        eval_set_path (str): JSON file [{query, should_trigger}, ...]
        description (str, optional): override description; default = current
        model (str): claude model id, default claude-sonnet-4-6
        num_workers (int): 1-8 parallel workers, default 1
        runs_per_query (int): repeat each query for stability, default 1
        timeout (int): per-subprocess seconds, default 60
        trigger_threshold (float): pass threshold, default 0.5

    Returns:
        JSON: precision, recall, accuracy, per-query results, total elapsed.

    Use when: validate ONE description without the iterative rewrite loop.
    For full optimization use skill_eval_start_optimization.

    Notes: temporarily edits SKILL.md and relies on try/finally + signal
    handlers to restore. If the host process dies hard mid-run, a
    `.md.swap-backup` sibling file holds the pre-swap content.
    """
    skill_path = Path(params.skill_path).resolve()
    if not (skill_path / "SKILL.md").exists():
        return json.dumps(_err(f"no SKILL.md at {skill_path}"))
    eval_set_path = Path(params.eval_set_path).resolve()
    if not eval_set_path.is_file():
        return json.dumps(_err(f"eval set not found: {eval_set_path}"))
    try:
        eval_set = json.loads(eval_set_path.read_text())
    except Exception as exc:
        return json.dumps(_err(f"bad eval set JSON: {exc}"))
    if not isinstance(eval_set, list) or not eval_set:
        return json.dumps(_err("eval set must be a non-empty list"))

    name, original_desc, _ = parse_skill_md(skill_path)
    description = params.description or original_desc
    project_root = find_project_root()

    t0 = time.time()
    try:
        result = _run_eval(
            eval_set=eval_set,
            skill_name=name,
            description=description,
            num_workers=params.num_workers,
            timeout=params.timeout,
            project_root=project_root,
            skill_path=skill_path,
            runs_per_query=params.runs_per_query,
            trigger_threshold=params.trigger_threshold,
            model=params.model,
        )
    except Exception as exc:
        return json.dumps(_err(f"{type(exc).__name__}: {exc}"))
    elapsed = time.time() - t0

    metrics = _summarize(result["results"])
    return json.dumps({
        "skill_name": name,
        "description_used": description,
        "summary": result["summary"],
        "metrics": metrics,
        "results": result["results"],
        "elapsed_s": round(elapsed, 1),
    }, indent=2)


@mcp.tool(
    name="skill_eval_start_optimization",
    annotations={
        "title": "Start description optimization loop (async)",
        "readOnlyHint": False,
        "destructiveHint": False,
        "idempotentHint": False,
        "openWorldHint": True,
    },
)
async def skill_eval_start_optimization(params: StartOptimizationInput) -> str:
    """Kick off the full eval+improve loop in a background thread, return immediately.

    The loop alternates: run eval -> if any train queries failed, ask
    Claude (via `claude -p`) to rewrite the description -> run eval again.
    Up to `max_iterations`. Stratified train/test split prevents overfit.

    Args:
        skill_path (str): absolute path to skill dir
        eval_set_path (str): JSON file [{query, should_trigger}, ...]
        description (str, optional): starting description; default = current
        model (str): default claude-sonnet-4-6
        num_workers, runs_per_query, timeout, trigger_threshold: as above
        max_iterations (int): default 3
        holdout (float): default 0.4 - fraction held out as test set

    Returns:
        JSON: {run_id, started_at}. Poll with skill_eval_get_run_status.

    Use when: user wants automated optimization, not just a single
    measurement. Long-running (~30s x eval_size x max_iterations).
    """
    skill_path = Path(params.skill_path).resolve()
    if not (skill_path / "SKILL.md").exists():
        return json.dumps(_err(f"no SKILL.md at {skill_path}"))
    eval_set_path = Path(params.eval_set_path).resolve()
    if not eval_set_path.is_file():
        return json.dumps(_err(f"eval set not found: {eval_set_path}"))
    try:
        eval_set = json.loads(eval_set_path.read_text())
    except Exception as exc:
        return json.dumps(_err(f"bad eval set JSON: {exc}"))

    run_id = uuid.uuid4().hex[:8]
    stop_event = threading.Event()
    state: dict = {
        "run_id": run_id,
        "status": "running",
        "started_at": time.time(),
        "params": params.model_dump(),
        "history": [],
        "stop_event": stop_event,
        "result": None,
        "error": None,
    }
    with _runs_lock:
        _runs[run_id] = state

    def progress_cb(evt: dict) -> None:
        e = evt.get("event")
        if e == "iteration_done":
            with _runs_lock:
                state["history"].append(evt["entry"])
        elif e == "loop_done":
            with _runs_lock:
                state["status"] = "complete"
                state["result"] = evt["result"]
                state["finished_at"] = time.time()
        elif e == "error":
            with _runs_lock:
                state["status"] = "error"
                state["error"] = evt.get("error")
                state["finished_at"] = time.time()

    def thread_body() -> None:
        try:
            result = _run_loop(
                eval_set=eval_set,
                skill_path=skill_path,
                description_override=params.description,
                num_workers=params.num_workers,
                timeout=params.timeout,
                max_iterations=params.max_iterations,
                runs_per_query=params.runs_per_query,
                trigger_threshold=params.trigger_threshold,
                holdout=params.holdout,
                model=params.model,
                verbose=False,
                progress_callback=progress_cb,
                stop_signal=stop_event,
            )
            progress_cb({"event": "loop_done", "result": result})
        except Exception as exc:
            progress_cb({"event": "error", "error": f"{type(exc).__name__}: {exc}"})

    t = threading.Thread(target=thread_body, daemon=True)
    state["thread"] = t
    t.start()
    return json.dumps({"run_id": run_id, "started_at": state["started_at"]}, indent=2)


@mcp.tool(
    name="skill_eval_get_run_status",
    annotations={
        "title": "Get optimization run status",
        "readOnlyHint": True,
        "destructiveHint": False,
        "idempotentHint": True,
        "openWorldHint": False,
    },
)
async def skill_eval_get_run_status(params: RunIdInput) -> str:
    """Snapshot a run by id. Returns history (all completed iterations) and
    final result if `status == complete`.

    Args:
        run_id (str): id from skill_eval_start_optimization

    Returns:
        JSON: {run_id, status, params, history, result, error, started_at,
        finished_at, iterations_run}.

    Use when: polling a long-running optimization for completion. Status
    moves through: running -> complete | error | stopped.
    """
    with _runs_lock:
        s = _runs.get(params.run_id)
    if not s:
        return json.dumps(_err(f"no run with id {params.run_id}"))
    return json.dumps({
        "run_id": params.run_id,
        "status": s["status"],
        "params": s["params"],
        "history": s["history"],
        "result": s.get("result"),
        "error": s.get("error"),
        "started_at": s["started_at"],
        "finished_at": s.get("finished_at"),
        "iterations_run": len(s["history"]),
    }, indent=2, default=str)


@mcp.tool(
    name="skill_eval_list_runs",
    annotations={
        "title": "List recent runs",
        "readOnlyHint": True,
        "destructiveHint": False,
        "idempotentHint": True,
        "openWorldHint": False,
    },
)
async def skill_eval_list_runs(params: ListSkillsInput) -> str:
    """Return all runs known to this server, newest first.

    Returns:
        JSON array of {run_id, status, started_at, finished_at,
        iterations_run, skill_path}.
    """
    with _runs_lock:
        items = list(_runs.items())
    out = []
    for rid, s in items:
        out.append({
            "run_id": rid,
            "status": s["status"],
            "started_at": s["started_at"],
            "finished_at": s.get("finished_at"),
            "iterations_run": len(s["history"]),
            "skill_path": s["params"].get("skill_path"),
        })
    out.sort(key=lambda r: r["started_at"], reverse=True)
    return json.dumps(out, indent=2)


@mcp.tool(
    name="skill_eval_apply_best_description",
    annotations={
        "title": "Apply winning description to SKILL.md",
        "readOnlyHint": False,
        "destructiveHint": True,
        "idempotentHint": True,
        "openWorldHint": False,
    },
)
async def skill_eval_apply_best_description(params: RunIdInput) -> str:
    """Write the run's best_description into the real SKILL.md.

    Creates a sibling `.md.apply-backup` snapshot of the current SKILL.md
    before overwriting. Atomic: tmp+rename. Frontmatter description field
    is replaced via the same logic run_eval uses for swap+restore, so all
    other frontmatter fields and the entire body are preserved.

    Args:
        run_id (str): completed run with a `result.best_description`

    Returns:
        JSON: {ok, applied_description, skill_md, backup}.

    Use when: optimization completed and the agent has confirmed the
    user wants to keep the winning description. Reverse via:
        cp <backup> <skill_md>
    """
    with _runs_lock:
        s = _runs.get(params.run_id)
    if not s:
        return json.dumps(_err(f"no run with id {params.run_id}"))
    result = s.get("result")
    if not result:
        return json.dumps(_err(f"run {params.run_id} has no result yet (status={s['status']})"))

    skill_path = Path(s["params"]["skill_path"])
    skill_md = skill_path / "SKILL.md"
    if not skill_md.exists():
        return json.dumps(_err(f"SKILL.md missing at {skill_md}"))

    backup = skill_md.with_suffix(".md.apply-backup")
    backup.write_text(skill_md.read_text())

    src = skill_md.read_text()
    new = _replace_description_in_frontmatter(src, result["best_description"])
    _atomic_write(skill_md, new)

    return json.dumps({
        "ok": True,
        "applied_description": result["best_description"],
        "skill_md": str(skill_md),
        "backup": str(backup),
    }, indent=2)


@mcp.tool(
    name="skill_eval_stop_run",
    annotations={
        "title": "Stop an in-progress optimization",
        "readOnlyHint": False,
        "destructiveHint": False,
        "idempotentHint": True,
        "openWorldHint": False,
    },
)
async def skill_eval_stop_run(params: RunIdInput) -> str:
    """Cooperatively stop an active run. Stops at the next iteration
    boundary - does not interrupt an in-flight subprocess.

    Args:
        run_id (str)

    Returns:
        JSON: {ok}
    """
    with _runs_lock:
        s = _runs.get(params.run_id)
    if not s:
        return json.dumps(_err(f"no run with id {params.run_id}"))
    s["stop_event"].set()
    return json.dumps({"ok": True}, indent=2)


def main() -> None:
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
