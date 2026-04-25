"""Interactive Phase-3 trigger optimization dashboard.

FastAPI + Server-Sent Events. Replaces the static auto-refresh HTML
report with a live web dashboard. Hosts on http://eval.local once
proxied through `portless`.

Endpoints:
  GET  /                          → dashboard UI
  GET  /api/skills                → list installed skills
  GET  /api/skills/<name>         → skill metadata + candidate eval sets
  POST /api/runs                  → start optimization run, returns run_id
  GET  /api/runs                  → list active + recent runs
  GET  /api/runs/<id>             → run snapshot
  GET  /api/runs/<id>/stream      → SSE stream of iteration events
  POST /api/runs/<id>/stop        → cooperative stop
  POST /api/runs/<id>/apply       → write best description back to SKILL.md
"""

from __future__ import annotations

import asyncio
import json
import os
import queue
import sys
import threading
import time
import uuid
from pathlib import Path

from fastapi import FastAPI, Request
from fastapi.responses import (
    FileResponse,
    JSONResponse,
    StreamingResponse,
)
from fastapi.staticfiles import StaticFiles

# Make scripts/* importable
SKILL_CREATOR_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SKILL_CREATOR_DIR))

from scripts.run_eval import (  # noqa: E402
    _atomic_write,
    _replace_description_in_frontmatter,
    find_project_root,
)
from scripts.run_loop import run_loop  # noqa: E402
from scripts.utils import parse_skill_md  # noqa: E402

SKILLS_DIR = Path.home() / ".claude" / "skills"
HERE = Path(__file__).resolve().parent

# When SKILL_FILTER is set, the dashboard restricts itself to that one skill.
# Used by start-for-skill.sh to give each parallel run its own portless
# subdomain (eval-<skill>.localhost) and a single-skill UI.
SKILL_FILTER = os.environ.get("SKILL_FILTER", "").strip() or None

app = FastAPI(title="skill-creator eval server")

_runs: dict[str, dict] = {}
_runs_lock = threading.Lock()


def _record_event(state: dict, evt: dict) -> None:
    """Append event to state.history when meaningful, then fan out to subscribers."""
    e = evt.get("event")
    if e == "iteration_done" and "entry" in evt:
        with _runs_lock:
            state["history"].append(evt["entry"])
    elif e == "loop_done":
        with _runs_lock:
            state["status"] = "complete"
            state["result"] = evt.get("result")
            state["finished_at"] = time.time()
    elif e == "error":
        with _runs_lock:
            state["status"] = "error"
            state["error"] = evt.get("error")
            state["finished_at"] = time.time()

    with _runs_lock:
        subs = list(state["subscribers"])
    for q in subs:
        try:
            q.put_nowait(evt)
        except queue.Full:
            pass


@app.get("/")
def index():
    return FileResponse(HERE / "static" / "index.html")


@app.get("/api/health")
def health():
    return {
        "ok": True,
        "skills_dir": str(SKILLS_DIR),
        "skills_exist": SKILLS_DIR.is_dir(),
        "skill_filter": SKILL_FILTER,
    }


@app.get("/api/skills")
def list_skills():
    """Enumerate ~/.claude/skills/<name>/SKILL.md entries.

    If SKILL_FILTER env var is set (typically by start-for-skill.sh),
    the listing is restricted to just that one skill so the dashboard
    is scoped to a single skill per portless subdomain.
    """
    if not SKILLS_DIR.is_dir():
        return []
    out = []
    for p in sorted(SKILLS_DIR.iterdir()):
        if SKILL_FILTER and p.name != SKILL_FILTER:
            continue
        if not p.is_dir() and not p.is_symlink():
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


@app.get("/api/skills/{name}")
def get_skill(name: str):
    p = SKILLS_DIR / name
    if not (p / "SKILL.md").exists():
        return JSONResponse({"error": "not found"}, status_code=404)
    real = p.resolve()
    n, desc, _ = parse_skill_md(real)

    # Auto-discover candidate eval sets:
    # - <skill>/evals/*.json
    # - <skill>/resources/*eval*.json
    # - <skill>-workspace/*.json (sibling workspace)
    candidates: list[dict] = []
    seen: set[str] = set()
    search_roots = [
        real / "evals",
        real / "resources",
        real.parent / f"{n}-workspace",
    ]
    for root in search_roots:
        if not root.is_dir():
            continue
        for f in root.rglob("*.json"):
            if str(f) in seen:
                continue
            try:
                data = json.loads(f.read_text())
            except Exception:
                continue
            if not isinstance(data, list) or not data:
                continue
            if not isinstance(data[0], dict) or "should_trigger" not in data[0]:
                continue
            should_count = sum(1 for q in data if q.get("should_trigger"))
            candidates.append({
                "path": str(f),
                "name": str(f.relative_to(root.parent)) if f.is_relative_to(root.parent) else str(f),
                "size": len(data),
                "should_trigger": should_count,
                "should_not_trigger": len(data) - should_count,
            })
            seen.add(str(f))
    candidates.sort(key=lambda c: c["size"], reverse=True)

    return {
        "name": n,
        "description": desc,
        "skill_path": str(real),
        "eval_candidates": candidates,
    }


@app.post("/api/runs")
async def create_run(req: Request):
    body = await req.json()
    skill_path = Path(body["skill_path"]).resolve()
    eval_set_path = Path(body["eval_set_path"]).resolve()
    if not (skill_path / "SKILL.md").exists():
        return JSONResponse({"error": f"no SKILL.md at {skill_path}"}, status_code=400)
    if not eval_set_path.is_file():
        return JSONResponse({"error": f"eval set not found at {eval_set_path}"}, status_code=400)

    try:
        eval_set = json.loads(eval_set_path.read_text())
    except Exception as exc:
        return JSONResponse({"error": f"bad eval set JSON: {exc}"}, status_code=400)

    if not isinstance(eval_set, list) or not eval_set:
        return JSONResponse({"error": "eval set must be a non-empty list"}, status_code=400)

    run_id = uuid.uuid4().hex[:8]
    stop_event = threading.Event()

    state: dict = {
        "run_id": run_id,
        "status": "running",
        "params": {
            "skill_path": str(skill_path),
            "eval_set_path": str(eval_set_path),
            "eval_size": len(eval_set),
            "model": body.get("model", "claude-sonnet-4-6"),
            "num_workers": int(body.get("num_workers", 1)),
            "timeout": int(body.get("timeout", 60)),
            "max_iterations": int(body.get("max_iterations", 5)),
            "runs_per_query": int(body.get("runs_per_query", 1)),
            "trigger_threshold": float(body.get("trigger_threshold", 0.5)),
            "holdout": float(body.get("holdout", 0.4)),
            "description_override": body.get("description") or None,
        },
        "history": [],
        "subscribers": [],
        "stop_event": stop_event,
        "result": None,
        "started_at": time.time(),
    }
    with _runs_lock:
        _runs[run_id] = state

    def progress_cb(evt: dict) -> None:
        evt = {"run_id": run_id, "ts": time.time(), **evt}
        _record_event(state, evt)

    def thread_body() -> None:
        try:
            result = run_loop(
                eval_set=eval_set,
                skill_path=skill_path,
                description_override=state["params"]["description_override"],
                num_workers=state["params"]["num_workers"],
                timeout=state["params"]["timeout"],
                max_iterations=state["params"]["max_iterations"],
                runs_per_query=state["params"]["runs_per_query"],
                trigger_threshold=state["params"]["trigger_threshold"],
                holdout=state["params"]["holdout"],
                model=state["params"]["model"],
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
    return {"run_id": run_id}


@app.get("/api/runs")
def list_runs():
    with _runs_lock:
        out = []
        for rid, s in _runs.items():
            out.append({
                "run_id": rid,
                "status": s["status"],
                "started_at": s["started_at"],
                "finished_at": s.get("finished_at"),
                "params": s["params"],
                "iterations_run": len(s["history"]),
            })
    return sorted(out, key=lambda r: r["started_at"], reverse=True)


@app.get("/api/runs/{run_id}")
def get_run(run_id: str):
    with _runs_lock:
        s = _runs.get(run_id)
    if not s:
        return JSONResponse({"error": "no such run"}, status_code=404)
    return {
        "run_id": run_id,
        "status": s["status"],
        "started_at": s["started_at"],
        "finished_at": s.get("finished_at"),
        "params": s["params"],
        "history": s["history"],
        "result": s.get("result"),
        "error": s.get("error"),
    }


@app.get("/api/runs/{run_id}/stream")
async def stream(run_id: str, req: Request):
    with _runs_lock:
        state = _runs.get(run_id)
    if not state:
        return JSONResponse({"error": "no such run"}, status_code=404)

    q: queue.Queue = queue.Queue(maxsize=500)
    with _runs_lock:
        state["subscribers"].append(q)

    snapshot = {
        "event": "snapshot",
        "run_id": run_id,
        "status": state["status"],
        "params": state["params"],
        "history": list(state["history"]),
        "result": state.get("result"),
        "error": state.get("error"),
    }

    async def gen():
        yield f"data: {json.dumps(snapshot)}\n\n"
        try:
            while True:
                if await req.is_disconnected():
                    return
                try:
                    evt = await asyncio.get_event_loop().run_in_executor(
                        None, lambda: q.get(timeout=15)
                    )
                except queue.Empty:
                    yield ": keepalive\n\n"
                    continue
                yield f"data: {json.dumps(evt)}\n\n"
                if evt.get("event") in ("loop_done", "error"):
                    return
        finally:
            with _runs_lock:
                try:
                    state["subscribers"].remove(q)
                except ValueError:
                    pass

    return StreamingResponse(gen(), media_type="text/event-stream")


@app.post("/api/runs/{run_id}/stop")
def stop_run(run_id: str):
    with _runs_lock:
        state = _runs.get(run_id)
    if not state:
        return JSONResponse({"error": "no such run"}, status_code=404)
    state["stop_event"].set()
    return {"ok": True}


@app.post("/api/runs/{run_id}/apply")
async def apply_best(run_id: str):
    with _runs_lock:
        state = _runs.get(run_id)
    if not state:
        return JSONResponse({"error": "no such run"}, status_code=404)
    result = state.get("result")
    if not result:
        return JSONResponse({"error": "run has no result yet"}, status_code=400)

    skill_path = Path(state["params"]["skill_path"])
    skill_md = skill_path / "SKILL.md"
    if not skill_md.exists():
        return JSONResponse({"error": f"SKILL.md missing at {skill_md}"}, status_code=400)

    backup = skill_md.with_suffix(".md.apply-backup")
    backup.write_text(skill_md.read_text())

    src = skill_md.read_text()
    new = _replace_description_in_frontmatter(src, result["best_description"])
    _atomic_write(skill_md, new)

    return {
        "ok": True,
        "applied_description": result["best_description"],
        "skill_md": str(skill_md),
        "backup": str(backup),
    }


app.mount("/static", StaticFiles(directory=HERE / "static"), name="static")


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8765, log_level="info")
