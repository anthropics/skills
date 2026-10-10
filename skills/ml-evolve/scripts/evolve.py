#!/usr/bin/env python3
"""Claude Code-driven OpenEvolve loop for general ML algorithm optimization.

The script keeps the algorithmic parts of OpenEvolve-like evolution in code:
population bookkeeping, islands, archive, exploitation/exploration parent
selection, diversity accounting, local evaluation, and run history.

Claude Code (or any external agent) is the LLM mutation engine: `select` writes
a mutation request and a working candidate file; the agent edits the candidate;
then `submit` (or `param-batch`) evaluates it on a user-supplied evaluator.

Task-agnostic design:

- The user provides a *project directory* with:
    initial_program.py   - seed candidate (with an EVOLVE block)
    evaluator.py         - reads candidate path argv, prints JSON metrics to
                           stdout. Must include a numeric "score" key
                           (overridable via EVAL_SCORE_KEY).
- This script never injects domain-specific config into candidates. It only
  copies the candidate file, runs the evaluator, parses JSON, and records
  metrics.
- Stage names are free-form labels passed to the evaluator via EVAL_STAGE.
- Optuna TPE parameter search is supported when a candidate declares
  PARAM_SEARCH_SPACE (a dict of dotted-path search specs).
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import math
import os
import random
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any


LOCAL_HOME = Path.home()
PROJECT_DIR = Path(os.environ.get("EVOLVE_PROJECT_DIR", str(Path.cwd()))).expanduser().resolve()
EVOLVE_PYTHON = os.environ.get("EVOLVE_PYTHON", "python3")
EVAL_SCORE_KEY = os.environ.get("EVAL_SCORE_KEY", "score")
EVAL_TIMEOUT = int(os.environ.get("EVAL_TIMEOUT", "0") or "0")  # 0 disables timeout

LOCAL_ROOT = Path(
    os.environ.get("EVOLVE_ROOT", str(LOCAL_HOME / ".claude" / "openevolve-runs"))
).expanduser()
DEFAULT_RUN = os.environ.get("EVOLVE_RUN", "default")

STAGES = [s.strip() for s in os.environ.get(
    "EVOLVE_STAGES", "smoke,small,medium,full,final"
).split(",") if s.strip()]


def _islands(n: int) -> dict[int, dict[str, str]]:
    return {
        i: {
            "family": f"branch_{i}",
            "description": "Generic island container; the plan agent defines this branch in research_plan.md.",
        }
        for i in range(n)
    }


ISLANDS = _islands(8)

PLAN_FILE = "research_plan.md"
PLAN_REQUEST_FILE = "plan_agent_request.md"


# ---------------------------------------------------------------------------
# Process / IO helpers
# ---------------------------------------------------------------------------

def run_local_bash(script: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", "-s"], input=script, text=True, capture_output=True, check=check
    )


def run_dir(name: str) -> Path:
    return LOCAL_ROOT / name


def candidates_dir(name: str) -> Path:
    return run_dir(name) / "candidates"


def state_path(name: str) -> Path:
    return run_dir(name) / "state.json"


def history_path(name: str) -> Path:
    return run_dir(name) / "history.jsonl"


def research_plan_path(name: str) -> Path:
    return run_dir(name) / PLAN_FILE


def plan_request_path(name: str) -> Path:
    return run_dir(name) / PLAN_REQUEST_FILE


def mutation_request_path(name: str) -> Path:
    return run_dir(name) / "mutation_request.md"


def load_state(name: str) -> dict[str, Any]:
    p = state_path(name)
    if not p.exists():
        raise SystemExit(f"Run not initialized: {name}. Run init first.")
    return json.loads(p.read_text(encoding="utf-8"))


def save_state(name: str, state: dict[str, Any]) -> None:
    run_dir(name).mkdir(parents=True, exist_ok=True)
    state_path(name).write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def append_history(name: str, row: dict[str, Any]) -> None:
    with history_path(name).open("a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def read_history(name: str) -> list[dict[str, Any]]:
    p = history_path(name)
    if not p.exists():
        return []
    return [json.loads(line) for line in p.read_text(encoding="utf-8").splitlines() if line.strip()]


def read_research_plan(name: str) -> str:
    p = research_plan_path(name)
    if not p.exists():
        return ""
    return p.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# Candidate inspection
# ---------------------------------------------------------------------------

def code_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def snapshot_candidate(name: str, candidate: Path, generation: int, label: str = "gen") -> Path:
    h = code_hash(candidate)
    safe_label = re.sub(r"[^A-Za-z0-9_.-]+", "_", label).strip("_") or "gen"
    out = candidates_dir(name) / f"{safe_label}{generation:04d}_{h}.py"
    candidates_dir(name).mkdir(parents=True, exist_ok=True)
    if candidate.resolve() != out.resolve():
        shutil.copyfile(candidate, out)
    return out


def _literal_assignment(path: Path, name: str) -> Any:
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                if any(isinstance(t, ast.Name) and t.id == name for t in node.targets):
                    return ast.literal_eval(node.value)
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == name:
                return ast.literal_eval(node.value)
    except Exception:
        return None
    return None


def extract_config(path: Path) -> dict[str, Any]:
    """Best-effort static extraction of `build_candidate()` return dict.

    Optional convention: candidates that don't define `build_candidate()` simply
    yield an empty config dict. Used for novelty scoring and param overrides;
    never required for evaluation.
    """
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name == "build_candidate":
                for child in ast.walk(node):
                    if isinstance(child, ast.Return):
                        return ast.literal_eval(child.value)
    except Exception:
        return {}
    return {}


def flatten_config(value: Any, prefix: str = "") -> dict[str, str]:
    out: dict[str, str] = {}
    if isinstance(value, dict):
        for k, v in sorted(value.items()):
            out.update(flatten_config(v, f"{prefix}.{k}" if prefix else str(k)))
    elif isinstance(value, list):
        out[prefix] = ",".join(map(str, value))
    else:
        out[prefix] = str(value)
    return out


def novelty(candidate_cfg: dict[str, Any], population: list[dict[str, Any]]) -> float:
    if not population:
        return 1.0
    flat = flatten_config(candidate_cfg)
    distances = []
    for row in population:
        other = flatten_config(row.get("config", {}))
        keys = set(flat) | set(other)
        if not keys:
            continue
        distances.append(sum(flat.get(k) != other.get(k) for k in keys) / len(keys))
    return float(sum(distances) / len(distances)) if distances else 1.0


# ---------------------------------------------------------------------------
# Scoring / selection
# ---------------------------------------------------------------------------

def score_of(row: dict[str, Any]) -> float:
    try:
        metrics = row.get("metrics", {})
        return float(metrics.get(EVAL_SCORE_KEY, metrics.get("score", -999.0)))
    except Exception:
        return -999.0


def is_valid_parent(row: dict[str, Any]) -> bool:
    metrics = row.get("metrics", {})
    if score_of(row) <= -998:
        return False
    if metrics.get("invalid", 0.0):
        return False
    return bool(metrics)


def latest_tpe_saturation_for_island(state: dict[str, Any], island: int) -> dict[str, Any] | None:
    """Return the most recent saturation snapshot recorded for this island, if any."""
    sat = state.get("tpe_saturation") or {}
    candidates = [v for v in sat.values() if int(v.get("island", -1)) == int(island)]
    if not candidates:
        return None
    return max(candidates, key=lambda v: float(v.get("timestamp", 0.0)))


def branch_health(state: dict[str, Any], rows: list[dict[str, Any]], island: int) -> dict[str, Any]:
    all_pool = sorted(
        [r for r in rows if int(r.get("island", 0)) == island],
        key=lambda r: int(r.get("generation", 0)),
        reverse=True,
    )
    pool = [r for r in all_pool if is_valid_parent(r)]
    recent_all = all_pool[:6]
    recent_valid = [r for r in recent_all if is_valid_parent(r)]
    best = max([score_of(r) for r in pool], default=-999.0)
    recent_best = max([score_of(r) for r in recent_valid], default=-999.0)
    stale = len(pool) >= 6 and recent_best <= best + 1e-9
    invalid_rate = 0.0 if not recent_all else 1.0 - len(recent_valid) / max(len(recent_all), 1)
    sat = latest_tpe_saturation_for_island(state, island)
    tpe_saturated = bool(sat and sat.get("saturated"))
    return {
        "island": island,
        "evaluated": len(all_pool),
        "valid_evaluated": len(pool),
        "recent_evaluated": len(recent_all),
        "recent_valid": len(recent_valid),
        "recent_invalid_rate": invalid_rate,
        "best_score": best,
        "recent_best_score": recent_best,
        "tpe_saturated": tpe_saturated,
        "tpe_slope": (sat or {}).get("slope"),
        "tpe_trials": (sat or {}).get("trials"),
        "needs_new_branch": bool(stale or invalid_rate >= 0.5 or tpe_saturated),
    }


def island_rows(state: dict[str, Any], rows: list[dict[str, Any]], island: int | None = None) -> list[dict[str, Any]]:
    if island is None:
        island = int(state.get("next_island", 0)) % int(state["config"]["num_islands"])
    return [r for r in rows if int(r.get("island", 0)) == island and is_valid_parent(r)]


def select_parent(state: dict[str, Any], rows: list[dict[str, Any]]) -> tuple[dict[str, Any], str, int]:
    cfg = state["config"]
    n_islands = int(cfg["num_islands"])
    island = int(state.get("next_island", 0)) % n_islands
    state["next_island"] = (island + 1) % n_islands
    valid_rows = [r for r in rows if is_valid_parent(r)]
    pool = island_rows(state, rows, island) or valid_rows
    if not pool:
        raise SystemExit("No candidates available. Run init first.")
    rng = random.Random(int(state.get("seed", 42)) + int(state.get("generation", 0)))
    exploit = rng.random() < float(cfg["exploitation_ratio"])
    if exploit:
        ranked = sorted(pool, key=score_of, reverse=True)
        elite_n = max(1, int(math.ceil(len(ranked) * float(cfg["elite_selection_ratio"]))))
        parent = rng.choice(ranked[:elite_n])
        mode = "exploit_elite"
    else:
        ranked = sorted(pool, key=lambda r: float(r.get("novelty", 0.0)), reverse=True)
        parent = rng.choice(ranked[: max(1, min(len(ranked), 5))])
        mode = "explore_diverse"
    return parent, mode, island


# ---------------------------------------------------------------------------
# Evaluator
# ---------------------------------------------------------------------------

def parse_json_object(text: str) -> dict[str, Any]:
    """Extract the last balanced JSON object in `text`."""
    text = text.rstrip()
    depth = 0
    end = len(text)
    for i in range(len(text) - 1, -1, -1):
        c = text[i]
        if c == "}":
            depth += 1
        elif c == "{":
            depth -= 1
            if depth == 0:
                try:
                    return json.loads(text[i:end])
                except Exception:
                    end = i
                    depth = 0
                    continue
    match = re.search(r"\{.*\}", text, flags=re.S)
    if not match:
        raise ValueError(f"No JSON object found in evaluator output:\n{text[-2000:]}")
    return json.loads(match.group(0))


def project_evaluator_path() -> Path:
    p = PROJECT_DIR / "evaluator.py"
    if not p.exists():
        raise SystemExit(
            f"Missing evaluator: {p}. Set EVOLVE_PROJECT_DIR to a directory containing evaluator.py."
        )
    return p


def project_initial_program() -> Path | None:
    p = PROJECT_DIR / "initial_program.py"
    return p if p.exists() else None


def evaluate_candidate(
    run_name: str,
    candidate: Path,
    stage: str,
    extra_env: dict[str, str] | None = None,
) -> dict[str, Any]:
    """Run `evaluator.py <candidate>` locally and parse a JSON metrics object."""
    evaluator = project_evaluator_path()
    env = dict(os.environ)
    env.update({
        "EVAL_STAGE": stage,
        "EVOLVE_STAGE": stage,
        "EVOLVE_RUN": run_name,
        "EVOLVE_RUN_DIR": str(run_dir(run_name)),
        "EVOLVE_PROJECT_DIR": str(PROJECT_DIR),
        "PYTHONUNBUFFERED": "1",
    })
    if extra_env:
        env.update(extra_env)
    cmd = [EVOLVE_PYTHON, str(evaluator), str(candidate)]
    try:
        cp = subprocess.run(
            cmd, cwd=str(PROJECT_DIR), env=env, text=True, capture_output=True,
            check=False, timeout=EVAL_TIMEOUT if EVAL_TIMEOUT > 0 else None,
        )
    except subprocess.TimeoutExpired as exc:
        return {EVAL_SCORE_KEY: -999.0, "invalid": 1.0, "error": f"evaluator timed out after {EVAL_TIMEOUT}s: {exc}"}
    text = (cp.stdout or "") + "\n" + (cp.stderr or "")
    if cp.returncode != 0:
        return {EVAL_SCORE_KEY: -999.0, "invalid": 1.0, "error": text[-4000:]}
    try:
        metrics = parse_json_object(text)
    except Exception as exc:
        return {EVAL_SCORE_KEY: -999.0, "invalid": 1.0, "error": f"{exc}\n{text[-4000:]}"}
    metrics.setdefault("stage", stage)
    if EVAL_SCORE_KEY not in metrics and "score" not in metrics:
        metrics[EVAL_SCORE_KEY] = -999.0
        metrics["invalid"] = 1.0
        metrics["error"] = f"evaluator metrics missing '{EVAL_SCORE_KEY}' key"
    return metrics


# ---------------------------------------------------------------------------
# Init / select / submit
# ---------------------------------------------------------------------------

def cmd_torch_smoke(args: argparse.Namespace) -> int:
    """Optional helper: verify the local Python can run a CUDA torch step."""
    script = f"""
{shlex.quote(EVOLVE_PYTHON)} - <<'PY'
import json
try:
    import torch
    out = {{"torch_version": getattr(torch, "__version__", "unknown"), "cuda_available": bool(torch.cuda.is_available()), "ok": False}}
    if torch.cuda.is_available():
        device = torch.device("cuda")
        props = torch.cuda.get_device_properties(0)
        out["device_name"] = props.name
        out["compute_capability"] = f"{{props.major}}.{{props.minor}}"
        x = torch.randn(1024, 32, device=device)
        y = torch.randn(1024, 1, device=device)
        layer = torch.nn.Linear(32, 1).to(device)
        opt = torch.optim.AdamW(layer.parameters(), lr=1e-3)
        opt.zero_grad(set_to_none=True)
        loss = torch.nn.functional.smooth_l1_loss(layer(x), y)
        loss.backward(); opt.step(); torch.cuda.synchronize()
        out["loss"] = float(loss.detach().cpu()); out["ok"] = True
except Exception as exc:
    out = {{"ok": False, "error": repr(exc)}}
print(json.dumps(out, indent=2))
PY
"""
    cp = run_local_bash(script, check=False)
    text = (cp.stdout or "") + "\n" + (cp.stderr or "")
    print(text.strip())
    try:
        payload = parse_json_object(text)
    except Exception:
        return 1
    return 0 if payload.get("ok") else 2


def cmd_init(args: argparse.Namespace) -> int:
    name = args.run
    rd = run_dir(name)
    candidates_dir(name).mkdir(parents=True, exist_ok=True)

    src: Path | None = None
    if args.initial:
        cand = Path(args.initial).expanduser().resolve()
        if cand.exists():
            src = cand
    if src is None:
        src = project_initial_program()
    if src is None:
        for p in [
            Path(__file__).resolve().parent.parent / "templates" / "example_minimal" / "initial_program.py",
            Path(__file__).resolve().parent.parent / "templates" / "quant_ml_alpha" / "initial_program.py",
        ]:
            if p.exists():
                src = p
                break
    if src is None:
        print(f"Missing initial_program.py. Place one in {PROJECT_DIR} or pass --initial.", file=sys.stderr)
        return 2

    initial = candidates_dir(name) / "gen0000_initial.py"
    if not initial.exists() or args.force:
        initial.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")

    state = {
        "run": name,
        "created_at": time.time(),
        "generation": 0,
        "next_island": 0,
        "seed": args.seed,
        "project_dir": str(PROJECT_DIR),
        "config": {
            "population_size": args.population_size,
            "archive_size": args.archive_size,
            "num_islands": args.num_islands,
            "elite_selection_ratio": args.elite_selection_ratio,
            "exploitation_ratio": args.exploitation_ratio,
        },
        "working_candidate": str(candidates_dir(name) / "next_candidate.py"),
    }
    save_state(name, state)
    metrics = evaluate_candidate(name, initial, args.stage)
    row = make_row(state, initial, metrics, parent_id=None, mode="seed", island=0)
    append_history(name, row)
    write_plan_request(name, state, [row], force=args.force)
    write_leaderboard(name)
    print(json.dumps({
        "initialized": str(rd),
        "stage": args.stage,
        "seed_metrics": metrics,
        "plan_request": str(plan_request_path(name)),
        "research_plan": str(research_plan_path(name)),
    }, indent=2, ensure_ascii=False))
    return 0


def make_row(
    state: dict[str, Any],
    path: Path,
    metrics: dict[str, Any],
    parent_id: str | None,
    mode: str,
    island: int,
) -> dict[str, Any]:
    cfg = extract_config(path)
    rows = read_history(state["run"])
    island_meta = ISLANDS.get(island, {})
    return {
        "id": f"g{int(state.get('generation', 0)):04d}_{code_hash(path)}",
        "time": time.time(),
        "generation": int(state.get("generation", 0)),
        "island": island,
        "island_family": island_meta.get("family", "unknown"),
        "parent_id": parent_id,
        "selection_mode": mode,
        "path": str(path),
        "hash": code_hash(path),
        "metrics": metrics,
        "config": cfg,
        "novelty": novelty(cfg, rows),
    }


def _leaderboard_snapshot(rows: list[dict[str, Any]], top_n: int = 10) -> list[dict[str, Any]]:
    valid = [r for r in rows if is_valid_parent(r)]
    ranked = sorted(valid, key=score_of, reverse=True)[:top_n]
    out: list[dict[str, Any]] = []
    for r in ranked:
        out.append({
            "id": r.get("id"),
            "island": r.get("island"),
            "generation": r.get("generation"),
            "score": score_of(r),
            "novelty": r.get("novelty"),
            "mode": r.get("mode"),
        })
    return out


def _per_island_top(rows: list[dict[str, Any]], n_islands: int, top_n: int = 3) -> dict[int, list[dict[str, Any]]]:
    result: dict[int, list[dict[str, Any]]] = {}
    for island in range(n_islands):
        pool = [r for r in rows if is_valid_parent(r) and int(r.get("island", 0)) == island]
        ranked = sorted(pool, key=score_of, reverse=True)[:top_n]
        result[island] = [{
            "id": r.get("id"),
            "generation": r.get("generation"),
            "score": score_of(r),
            "novelty": r.get("novelty"),
        } for r in ranked]
    return result


def write_plan_request(
    name: str,
    state: dict[str, Any],
    rows: list[dict[str, Any]],
    force: bool = False,
    mode: str = "initial",
) -> Path:
    request = plan_request_path(name)
    plan = research_plan_path(name)
    if mode not in {"initial", "replan"}:
        raise SystemExit(f"unknown plan mode: {mode}")
    if request.exists() and not force and mode == "initial":
        return request
    num_islands = int(state["config"]["num_islands"])
    island_summaries = [branch_health(state, rows, island) for island in range(num_islands)]

    if mode == "replan":
        existing_plan = ""
        if plan.exists():
            existing_plan = plan.read_text(encoding="utf-8")
        leaderboard = _leaderboard_snapshot(rows, top_n=10)
        per_island = _per_island_top(rows, num_islands, top_n=3)
        generation = int(state.get("generation", 0))
        last_replan = int(state.get("last_replan_generation", 0))
        request.write_text(
            f"""# Plan Agent Request (REPLAN)

Run: `{name}`
Generation: `{generation}`
Generations since last (re)plan: `{generation - last_replan}`
Project: `{PROJECT_DIR}`

## Mission

The search has accumulated enough evidence to revisit the research plan.
**Critically review every island** against the accumulated leaderboard and
branch health, then update `research_plan.md` so the next round of mutation
spends budget where it pays off.

For each island, pick exactly one of:

- **KEEP** — the branch is still improving (positive slope, recent best gains,
  TPE not saturated). Sharpen the hypothesis if helpful, but do not change the
  branch concept.
- **REFRESH** — the branch concept has plateaued or saturated, but the island
  slot is worth keeping. Replace the branch concept with a materially different
  direction motivated by what was learned (e.g. swap loss family, swap
  architecture style, swap sampling regime).
- **RETIRE & REPLACE** — the branch has been proven ineffective (consistently
  invalid, recent best far below leaderboard top, TPE saturated with negative
  slope, or a structural dead end). Retire it entirely and introduce a
  **new branch** in its slot with a different algorithmic hypothesis.

Aim to retire at least one island if any island's best score sits below
50% of the global best, or `needs_new_branch` is true and `tpe_saturated`
is true. Do not retire an island purely because it has fewer evaluations
than others.

## Required Research Before Writing the Revised Plan

Ground every kept/refreshed/replaced branch in current external evidence — do
not rely on memory or generic priors. Run multiple `WebSearch` / `WebFetch`
queries targeting sources such as:

- **Chinese internet & AI company tech blogs and papers**: ByteDance / Seed,
  Alibaba (DAMO, Taobao Tech, Ant Group, Alimama), Tencent (WeChat AI, Tencent
  AI Lab, Hunyuan), Baidu (PaddlePaddle, ERNIE), Meituan Tech, JD Tech,
  Kuaishou, Xiaohongshu, DeepSeek, Moonshot, Zhipu, MiniMax, 01.AI, Qwen, etc.
  (英文站点和中文技术博客、arXiv、知乎专栏、机器之心解读都算)。
- **US internet & AI company tech blogs and papers**: Google / DeepMind,
  OpenAI, Anthropic, Meta AI / FAIR, Microsoft Research, NVIDIA, Netflix
  Tech, Uber Engineering, Airbnb Engineering, LinkedIn Engineering, Pinterest
  Engineering, Apple ML, Amazon Science, xAI, Cohere, Mistral, Databricks /
  Mosaic, HuggingFace, Together AI, etc.
- **Top-tier conferences / preprints**: NeurIPS, ICML, ICLR, KDD, CVPR, ACL,
  EMNLP, WSDM, RecSys, SIGIR, arXiv recent (latest 12 months prioritised).
- **Kaggle Master / Grandmaster competition writeups and solution
  notebooks** on closely-related tasks (winner + top-10 solutions, public
  discussion threads, official solution videos / slides).

Prefer **recent** material (last 12–24 months) and reproducible recipes over
marketing posts. For any RETIRE & REPLACE decision, the replacement branch
must cite at least 2–3 independent sources supporting its direction.

## Decision Inputs

### Leaderboard top 10

```json
{json.dumps(leaderboard, indent=2, ensure_ascii=False)}
```

### Per-island top 3

```json
{json.dumps(per_island, indent=2, ensure_ascii=False)}
```

### Branch health

```json
{json.dumps(island_summaries, indent=2, ensure_ascii=False)}
```

### Current `research_plan.md`

```markdown
{existing_plan[:12000] if existing_plan else "(no existing plan — treat this as an initial plan instead)"}
```

## Output

Rewrite `{plan}` in place so it still has exactly **{num_islands}** branches
(one per island slot). Add a new top-level section
`## Replan Decisions (gen {generation})` summarizing per-island
KEEP/REFRESH/RETIRE&REPLACE decisions with one-line reasons and any retired
hypotheses — this preserves history for future replans.

Do not modify the evaluator or any code outside `research_plan.md` during
replan. The next `select` will pick up the new plan automatically.
""",
            encoding="utf-8",
        )
        return request

    request.write_text(
        f"""# Plan Agent Request

Run: `{name}`
Generation: `{state.get('generation', 0)}`
Project: `{PROJECT_DIR}`

## Mission

Before normal candidate mutation, perform a research-style planning pass. Use
web search plus your own reasoning to define exactly **{num_islands} replaceable
research branches** for this ML algorithm optimization problem.

The script provides island containers only; you decide what each branch should
be based on the problem statement, current evidence, history and budget.

Each branch should specify:

1. Algorithm hypothesis and why it should work for this task.
2. Model families or method classes that may be explored without
   over-constraining the island.
3. Data/feature pipeline direction, with care to avoid leakage.
4. Parameter-search strategy, low-cost proxy experiment, promotion criteria,
   and resource budget.
5. Training/objective/regularization/sampling/optimization direction.
6. Failure modes, kill criteria, and refresh trigger.

## Requirements

- Read the problem statement and evaluator interface in the project directory
  before writing branches.
- Base the plan on current public technical writing, papers, and reproducible
  recipes from leading labs, companies, and Kaggle Master/Grandmaster solutions
  applicable to the task at hand.
- **Initial branches must lean on industry-standard, battle-tested methods**
  rather than speculative or exotic research. For the first round, prefer
  algorithms that have been deployed at scale in production at major internet
  companies, won (or placed top-3 in) recent Kaggle competitions on similar
  task shapes, or are the de-facto reference baselines in widely-cited
  survey/benchmark papers. Save more speculative directions for later
  branch-refresh cycles once at least one branch has established a solid
  baseline.
- Keep branch descriptions broad enough that later mutation agents can invent
  new algorithm structures, processing pipelines, or training loops.
- Include citations or short source notes in `research_plan.md`.
- Keep evaluator rules fixed: do not alter the evaluator from a mutation; only
  edit the candidate program.
- Optimize the single primary score reported by the evaluator (key:
  `{EVAL_SCORE_KEY}`). Use other metrics diagnostically.

## Required Research Before Writing the Plan

Ground every branch in current external evidence — do not rely on memory or
generic priors. Run multiple `WebSearch` / `WebFetch` queries targeting
sources such as:

- **Chinese internet & AI company tech blogs and papers**: ByteDance / Seed,
  Alibaba (DAMO, Taobao Tech, Ant Group, Alimama), Tencent (WeChat AI, Tencent
  AI Lab, Hunyuan), Baidu (PaddlePaddle, ERNIE), Meituan Tech, JD Tech,
  Kuaishou, Xiaohongshu, DeepSeek, Moonshot, Zhipu, MiniMax, 01.AI, Qwen, etc.
  (英文站点和中文技术博客、arXiv、知乎专栏、机器之心解读都算)。
- **US internet & AI company tech blogs and papers**: Google / DeepMind,
  OpenAI, Anthropic, Meta AI / FAIR, Microsoft Research, NVIDIA, Netflix
  Tech, Uber Engineering, Airbnb Engineering, LinkedIn Engineering, Pinterest
  Engineering, Apple ML, Amazon Science, xAI, Cohere, Mistral, Databricks /
  Mosaic, HuggingFace, Together AI, etc.
- **Top-tier conferences / preprints**: NeurIPS, ICML, ICLR, KDD, CVPR, ACL,
  EMNLP, WSDM, RecSys, SIGIR, arXiv recent (latest 12 months prioritised).
- **Kaggle Master / Grandmaster competition writeups and solution
  notebooks** on closely-related tasks (winner + top-10 solutions, public
  discussion threads, official solution videos / slides).

Prefer **recent** material (last 12–24 months) and reproducible recipes over
marketing posts. Cross-check at least 2–3 independent sources before
committing a branch direction; cite them inline in `research_plan.md` under
`## Evidence Sources` so the choice is auditable.

## Current Island Health

```json
{json.dumps(island_summaries, indent=2, ensure_ascii=False)}
```

## Output File

Write the final plan to:

`{plan}`

Use the following structure (one section per branch, plus shared sections):

```markdown
# Research Plan

## Problem Summary
...
## Branch 0: ...
## Branch 1: ...
...
## Evidence Sources
...
## Branch Refresh Rules
...
```
""",
        encoding="utf-8",
    )
    if not plan.exists() or force:
        plan.write_text(
            f"""# Research Plan

This file is intentionally a scaffold. A plan agent should replace it after web
research and reasoning. The script provides {num_islands} generic island containers.

## Problem Summary

Describe the task, dataset (if any), metric (`{EVAL_SCORE_KEY}`), constraints,
and runtime budget for one evaluation.

## Branches

Fill in one section per island, e.g. `## Branch 0: <name>`.

## Evidence Sources

Notes/citations for the directions chosen above.

## Branch Refresh Rules

When to retire and replace an island branch.
""",
            encoding="utf-8",
        )
    return request


def cmd_select(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = read_history(args.run)
    parent, mode, island = select_parent(state, rows)
    plan_text = read_research_plan(args.run).strip()
    health = branch_health(state, rows, island)
    state["generation"] = int(state.get("generation", 0)) + 1
    state["pending_parent_id"] = parent["id"]
    state["pending_selection_mode"] = mode
    state["pending_island"] = island
    save_state(args.run, state)

    parent_path = Path(parent["path"])
    working = Path(state["working_candidate"])
    script_path = Path(__file__).expanduser().resolve()
    if parent_path.resolve() != working.resolve():
        shutil.copyfile(parent_path, working)

    request = run_dir(args.run) / "mutation_request.md"
    stage_label = getattr(args, "stage", "small")
    loop_runtime = state.get("loop_runtime") or {}
    prev_tpe = latest_tpe_saturation_for_island(state, island)
    in_loop = bool(loop_runtime)
    param_trials = int(loop_runtime.get("param_trials_per_architecture", 0) or 0)
    tpe_startup = int(loop_runtime.get("tpe_startup_trials", 0) or 0)
    will_run_tpe = param_trials > 1

    # Precompute trailing usage snippet (kept out of the f-string so the
    # source is compatible with Python 3.11, which disallows backslashes
    # inside f-string expression parts).
    if in_loop:
        trailing_block = (
            "After editing, the loop will continue automatically. "
            "If you are running this step manually outside the loop, use:\n\n"
            "```bash\n"
            f"python3 {script_path} --run {args.run} param-batch --stage {stage_label} "
            f"--trials {max(param_trials, 12)}\n"
            f"python3 {script_path} --run {args.run} submit --stage {stage_label}\n"
            "```\n"
        )
    else:
        trailing_block = (
            "After editing, run one of:\n\n"
            "```bash\n"
            f"python3 {script_path} --run {args.run} submit --stage {stage_label}\n"
            f"python3 {script_path} --run {args.run} param-batch --stage {stage_label} --trials 12\n"
            "```\n"
        )

    if will_run_tpe:
        param_batch_clause = (
            f"automatically run Optuna TPE on your architecture for {param_trials} "
            f"trials (startup_trials={tpe_startup}) at stage `{stage_label}`."
        )
        trials_hint = f"{param_trials}"
        startup_hint = f"{tpe_startup}"
    else:
        param_batch_clause = (
            f"run a single `submit` evaluation at stage `{stage_label}` "
            "(no TPE batch in this iteration)."
        )
        trials_hint = "<= 6"
        startup_hint = "0"
    request.write_text(
        f"""# Mutation Request

Run: `{args.run}`
Generation: `{state['generation']}`
Island: `{island}`
Research branch container: `{ISLANDS.get(island, {}).get('family', 'unknown')}`
Selection mode: `{mode}`
Parent: `{parent['id']}`
Parent score: `{score_of(parent):.6f}`
Branch health: `{json.dumps(health, ensure_ascii=False)}`
Loop runtime: `{json.dumps(loop_runtime, ensure_ascii=False) if loop_runtime else 'standalone (no run-loop context)'}`

## Your Task

Edit only the EVOLVE block in:

`{working}`

Improve the primary evaluator score (key: `{EVAL_SCORE_KEY}`). The candidate is
open-ended: you may edit configuration and implement or replace the algorithm
inside the EVOLVE block. The evaluator and any data-splitting / eval-protocol
logic are fixed and must not be modified for a regular mutation.

Prefer changes that:

- improve the primary score on the active stage (`{stage_label}`);
- preserve any leakage / split / fairness assumptions enforced by the evaluator;
- draw on current best practice from research literature and competitions
  applicable to this task, as captured in `research_plan.md`;
- prefer deeper structural changes (algorithm, training loop, sampling,
  objective, regularization, architecture) when parameter tweaks are unlikely
  to help further;
- keep the configuration simple and meaningful.

## Required Research Before Editing

Before writing any code, perform a **thorough web search pass** and ground the
mutation in current external evidence. Do not rely on memory or on
`research_plan.md` alone — the plan can be stale or incomplete. Specifically:

- Run multiple `WebSearch` / `WebFetch` queries targeting sources such as:
  - **Chinese internet & AI company tech blogs and papers**: ByteDance / Seed,
    Alibaba (DAMO, Taobao Tech, Ant Group, Alimama), Tencent (WeChat AI, Tencent
    AI Lab, Hunyuan), Baidu (PaddlePaddle, ERNIE), Meituan Tech, JD Tech,
    Kuaishou, Xiaohongshu, DeepSeek, Moonshot, Zhipu, MiniMax, 01.AI, Qwen, etc.
    (英文站点和中文技术博客、arXiv、知乎专栏、机器之心解读都算)。
  - **US internet & AI company tech blogs and papers**: Google / DeepMind,
    OpenAI, Anthropic, Meta AI / FAIR, Microsoft Research, NVIDIA, Netflix
    Tech, Uber Engineering, Airbnb Engineering, LinkedIn Engineering, Pinterest
    Engineering, Apple ML, Amazon Science, xAI, Cohere, Mistral, Databricks /
    Mosaic, HuggingFace, Together AI, etc.
  - **Top-tier conferences / preprints**: NeurIPS, ICML, ICLR, KDD, CVPR, ACL,
    EMNLP, WSDM, RecSys, SIGIR, arXiv recent (latest 12 months prioritised).
  - **Kaggle Master / Grandmaster competition writeups and solution
    notebooks** on closely-related tasks (winner + top-10 solutions, public
    discussion threads, official solution videos / slides).
- Prefer **recent** material (last 12–24 months) and reproducible recipes over
  marketing posts.
- Cross-check at least 2–3 independent sources before committing to a
  structural idea; cite them inline in your reasoning so the choice is
  auditable.
- If the search surfaces an idea that contradicts or supersedes the current
  `research_plan.md` branch for this island, say so explicitly and either (a)
  adapt within the branch, or (b) if `needs_new_branch` is true, propose a new
  branch grounded in the new evidence and update `research_plan.md`.
- Do not copy code verbatim from any source; reimplement inside the EVOLVE
  block, adapted to this evaluator's interface and constraints.

Skipping the search pass is not acceptable for a regular mutation — the goal
is for every candidate to reflect the current external state of the art, not
just local hill-climbing.

If `needs_new_branch` is true in branch health, propose and implement a
materially new branch concept for this island, and update `research_plan.md`
afterward if it should replace the old branch.

Do not edit evaluator code for a candidate mutation.

## Research Plan

Use the current plan if present. If it is only a placeholder, run the `plan`
step before continuing.

```markdown
{plan_text[:8000] if plan_text else "No research_plan.md found. Run the plan command first."}
```

## Parent Metrics

```json
{json.dumps(parent.get('metrics', {}), indent=2, ensure_ascii=False)}
```

## Param Search Contract (must follow)

After this mutation, the loop will {param_batch_clause}

You are responsible for the **structural** changes; TPE handles parameter sweeps. To make that division work:

- The candidate file **must** declare a module-level `PARAM_SEARCH_SPACE` dict. Each key is a dotted path into the dict returned by `build_candidate()`; values describe the search range. Examples:
  - `{{"type": "float", "low": 1e-5, "high": 1e-2, "log": True}}`
  - `{{"type": "int", "low": 2, "high": 8}}`
  - `{{"choices": ["adamw", "lion", "sgd"]}}`
- After your structural changes, **rewrite `PARAM_SEARCH_SPACE` so every dotted path resolves against the new `build_candidate()` config**. Stale keys from earlier architectures are silently ignored by `apply_param_overrides` and waste TPE trials — do not leave them.
- Keep the dimensionality compatible with the available trial budget ({trials_hint} trials, {startup_hint} startup): roughly **<= trials / 3** dimensions for coarse search, fewer if interactions matter. Prefer a small, well-chosen set of high-leverage knobs over many.
- If your new architecture genuinely has no useful tunable parameters, set `PARAM_SEARCH_SPACE = {{}}` and the loop will fall back to a single `submit` for this iteration instead of running TPE.
- Optional: define `apply_search_params(config, params)` to map sampled params into the config with custom logic; otherwise dotted-path overrides are used.

## Previous TPE Batch on This Island

```json
{json.dumps(prev_tpe, indent=2, ensure_ascii=False) if prev_tpe else "No prior TPE batch recorded for this island yet."}
```

Use this to judge whether the previous architecture's parameter space was saturated:

- High `trials` with `slope <= 0` and `saturated: true` → the prior structure is tapped out; prefer a **materially new** structural direction this iteration (do not just retune the same skeleton).
- Positive `slope` with few `trials` → the prior structure may still have headroom; you may iterate within the same architectural family while broadening or refocusing `PARAM_SEARCH_SPACE`.
- `best_params` shows where TPE converged. Treat values pegged at the edges of their search range as a hint to **extend the range** (or change the parametrization) in the new `PARAM_SEARCH_SPACE`.

{trailing_block}""",
        encoding="utf-8",
    )
    print(json.dumps({"working_candidate": str(working), "mutation_request": str(request), "parent": parent}, indent=2, ensure_ascii=False))
    return 0


# ---------------------------------------------------------------------------
# Optuna TPE parameter batches
# ---------------------------------------------------------------------------

def load_param_search_space(path: Path) -> dict[str, Any]:
    raw = _literal_assignment(path, "PARAM_SEARCH_SPACE")
    if isinstance(raw, dict) and raw:
        return {str(k): v for k, v in raw.items()}
    return {}


def _suggest_from_space(trial: Any, name: str, spec: Any) -> Any:
    if isinstance(spec, (list, tuple)):
        return trial.suggest_categorical(name, list(spec))
    if not isinstance(spec, dict):
        return trial.suggest_categorical(name, [spec])
    if "choices" in spec:
        return trial.suggest_categorical(name, list(spec["choices"]))
    typ = str(spec.get("type", "float")).lower()
    low = spec.get("low")
    high = spec.get("high")
    if typ in {"int", "integer"}:
        return trial.suggest_int(name, int(low), int(high), step=int(spec.get("step", 1)), log=bool(spec.get("log", False)))
    if typ in {"categorical", "choice"}:
        return trial.suggest_categorical(name, list(spec.get("values", [])))
    return trial.suggest_float(name, float(low), float(high), step=spec.get("step"), log=bool(spec.get("log", False)))


def suggest_param_values(trial: Any, space: dict[str, Any]) -> dict[str, Any]:
    return {name: _suggest_from_space(trial, name, spec) for name, spec in sorted(space.items())}


def apply_param_overrides(cfg: dict[str, Any], params: dict[str, Any]) -> dict[str, Any]:
    for dotted, value in params.items():
        cur: Any = cfg
        parts = str(dotted).split(".")
        for part in parts[:-1]:
            if not isinstance(cur, dict):
                break
            cur = cur.setdefault(part, {})
        if isinstance(cur, dict):
            cur[parts[-1]] = value
    return cfg


def write_param_variant(architecture: Path, out: Path, params: dict[str, Any], trial_number: int) -> None:
    """Append a deterministic config override block to a candidate file.

    Convention: the candidate may expose `build_candidate()` returning a dict
    and (optionally) `apply_search_params(config, params)` for custom mapping.
    If neither exists, the appended block is a harmless no-op.
    """
    payload = repr(params)
    injection = """

# PARAM-BATCH-TRIAL-START
_PARAM_SEARCH_PARAMS = __PARAM_PAYLOAD__
_PARAM_SEARCH_TRIAL = __TRIAL_NUMBER__

def _param_batch_deep_set(cfg, dotted, value):
    cur = cfg
    parts = str(dotted).split(".")
    for part in parts[:-1]:
        if not isinstance(cur, dict):
            return cfg
        cur = cur.setdefault(part, {})
    if isinstance(cur, dict):
        cur[parts[-1]] = value
    return cfg

try:
    _BASE_BUILD_CANDIDATE = build_candidate  # type: ignore[name-defined]
    def build_candidate():  # type: ignore[no-redef]
        cfg = _BASE_BUILD_CANDIDATE()
        if not isinstance(cfg, dict):
            return cfg
        if "apply_search_params" in globals():
            cfg = apply_search_params(cfg, dict(_PARAM_SEARCH_PARAMS))
        else:
            for key, value in _PARAM_SEARCH_PARAMS.items():
                cfg = _param_batch_deep_set(cfg, key, value)
        cfg.setdefault("_meta", {})["param_search_trial"] = _PARAM_SEARCH_TRIAL
        cfg.setdefault("_meta", {})["param_search_params"] = dict(_PARAM_SEARCH_PARAMS)
        return cfg
    def get_candidate_config():  # type: ignore[no-redef]
        return build_candidate()
except NameError:
    pass
# PARAM-BATCH-TRIAL-END
""".replace("__PARAM_PAYLOAD__", payload).replace("__TRIAL_NUMBER__", str(trial_number))
    out.parent.mkdir(parents=True, exist_ok=True)
    src = architecture.read_text(encoding="utf-8")
    # Strip any pre-existing PARAM-BATCH-TRIAL injection blocks; otherwise the
    # `_BASE_BUILD_CANDIDATE = build_candidate` reassignment self-references
    # the previous redef and recurses on call.
    src = re.sub(
        r"\n*# PARAM-BATCH-TRIAL-START.*?# PARAM-BATCH-TRIAL-END\n?",
        "\n",
        src,
        flags=re.DOTALL,
    )
    out.write_text(src + injection, encoding="utf-8")


def cmd_generate(args: argparse.Namespace) -> int:
    """Deterministic fallback: overlay random params from PARAM_SEARCH_SPACE."""
    state = load_state(args.run)
    working = Path(state["working_candidate"])
    if not working.exists():
        raise SystemExit("Run `select` before `generate`.")
    space = load_param_search_space(working)
    if not space:
        print(json.dumps({
            "generated": False,
            "reason": "no PARAM_SEARCH_SPACE in current candidate; nothing to randomize",
            "working_candidate": str(working),
        }, indent=2))
        return 0
    seed = int(state.get("seed", 42)) + int(state.get("generation", 0))
    rng = random.Random(seed)
    params: dict[str, Any] = {}
    for name, spec in sorted(space.items()):
        if isinstance(spec, (list, tuple)):
            params[name] = rng.choice(list(spec)); continue
        if not isinstance(spec, dict):
            params[name] = spec; continue
        if "choices" in spec:
            params[name] = rng.choice(list(spec["choices"])); continue
        typ = str(spec.get("type", "float")).lower()
        if typ in {"int", "integer"}:
            params[name] = rng.randint(int(spec["low"]), int(spec["high"]))
        elif typ in {"categorical", "choice"}:
            params[name] = rng.choice(list(spec.get("values", [])))
        else:
            low, high = float(spec["low"]), float(spec["high"])
            if bool(spec.get("log", False)) and low > 0 and high > 0:
                params[name] = math.exp(rng.uniform(math.log(low), math.log(high)))
            else:
                params[name] = rng.uniform(low, high)
    write_param_variant(working, working, params, trial_number=seed)
    print(json.dumps({"generated": True, "working_candidate": str(working), "params": params}, indent=2))
    return 0


def cmd_submit(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = read_history(args.run)
    pending_parent_id = state.get("pending_parent_id")
    parent = next((r for r in rows if r.get("id") == pending_parent_id), None)
    if parent is None:
        parent = rows[-1] if rows else {"id": None, "island": 0}
    mode = str(state.get("pending_selection_mode") or "submit")
    island = int(state.get("pending_island", parent.get("island", 0)))
    if args.parentless:
        parent = {"id": None, "island": island}
        mode = "parentless_submit"
    candidate = Path(args.file or state["working_candidate"])
    if not candidate.exists():
        raise SystemExit(f"Missing candidate file: {candidate}")
    snapshot = snapshot_candidate(args.run, candidate, int(state.get("generation", 0)))
    metrics = evaluate_candidate(args.run, snapshot, args.stage)
    row = make_row(state, snapshot, metrics, parent_id=parent.get("id"), mode=mode, island=island)
    append_history(args.run, row)
    state.pop("pending_parent_id", None)
    state.pop("pending_selection_mode", None)
    state.pop("pending_island", None)
    save_state(args.run, state)
    write_leaderboard(args.run)
    enforce_population_limits(args.run)
    print(json.dumps({
        "submitted": row["id"],
        "stage": args.stage,
        "metrics": metrics,
        "leaderboard": str(run_dir(args.run) / "leaderboard.md"),
    }, indent=2, ensure_ascii=False))
    return 0


def cmd_param_batch(args: argparse.Namespace) -> int:
    """Run Optuna TPE parameter trials under one fixed agent-designed architecture."""
    if args.trials <= 0:
        raise SystemExit("--trials must be positive")
    try:
        import optuna  # type: ignore
    except Exception as exc:
        raise SystemExit("Optuna is required for param-batch. Install it: pip install optuna") from exc

    state = load_state(args.run)
    rows = read_history(args.run)
    best = _best_row(args.run)
    pending_parent_id = state.get("pending_parent_id")
    parent = next((r for r in rows if r.get("id") == pending_parent_id), None) or best or (rows[-1] if rows else {"id": None, "island": 0})
    island = int(state.get("pending_island", parent.get("island", 0)))
    if args.parentless:
        parent = {"id": None, "island": island}
    architecture = Path(args.file or state["working_candidate"])
    if not architecture.exists():
        raise SystemExit(f"Missing architecture candidate file: {architecture}")

    space = load_param_search_space(architecture)
    if not space:
        print(json.dumps({
            "param_batch_skipped": True,
            "reason": "PARAM_SEARCH_SPACE missing or empty; falling back to single submit",
            "architecture": str(architecture),
        }, ensure_ascii=False))
        return cmd_submit(argparse.Namespace(
            run=args.run, file=None, stage=args.stage, parentless=bool(args.parentless),
        ))

    seed = int(args.seed if args.seed is not None else state.get("seed", 42))
    generation = int(state.get("generation", 0))
    arch_hash = code_hash(architecture)
    base_cfg = extract_config(architecture)
    sampler = optuna.samplers.TPESampler(seed=seed, n_startup_trials=max(1, int(args.startup_trials)))
    study = optuna.create_study(direction="maximize", sampler=sampler, study_name=f"{args.run}-g{generation}-{arch_hash}")
    trial_dir = candidates_dir(args.run) / "param_trials"
    completed: list[dict[str, Any]] = []
    completed_lock = threading.Lock()
    parallel_workers = max(1, int(getattr(args, "parallel_workers", 1) or 1))

    def objective(trial: Any) -> float:
        params = suggest_param_values(trial, space)
        variant = trial_dir / f"g{generation:04d}_{arch_hash}_t{trial.number:03d}.py"
        write_param_variant(architecture, variant, params, trial.number)
        metrics = evaluate_candidate(args.run, variant, args.stage)
        metrics["param_trial"] = float(trial.number)
        metrics["param_batch_generation"] = float(generation)
        metrics["param_space_size"] = float(len(space))
        row = make_row(state, variant, metrics, parent_id=parent.get("id"), mode="tpe_param_trial", island=island)
        if base_cfg:
            cfg = json.loads(json.dumps(base_cfg, ensure_ascii=False))
            row["config"] = apply_param_overrides(cfg, params)
        else:
            row["config"] = {"param_search_params": params}
        row["param_search"] = {
            "sampler": "optuna_tpe",
            "trial": trial.number,
            "architecture_hash": arch_hash,
            "params": params,
        }
        with completed_lock:
            append_history(args.run, row)
            completed.append({"trial": trial.number, "score": score_of(row), "id": row["id"], "params": params})
            write_leaderboard(args.run)
        return score_of(row)

    study.optimize(objective, n_trials=args.trials, n_jobs=parallel_workers)
    state.pop("pending_parent_id", None)
    state.pop("pending_selection_mode", None)
    state.pop("pending_island", None)

    trial_scores = [float(c["score"]) for c in sorted(completed, key=lambda c: int(c["trial"]))]
    n_done = len(trial_scores)
    if n_done >= 2:
        half = max(1, n_done // 2)
        early_best = max(trial_scores[:half])
        late_best = max(trial_scores[half:])
        slope = late_best - early_best
    else:
        early_best = late_best = trial_scores[0] if trial_scores else float("-inf")
        slope = 0.0
    saturated = n_done >= 6 and slope <= 1e-6
    sat_entry = {
        "architecture_hash": arch_hash,
        "island": int(island),
        "generation": int(generation),
        "trials": int(n_done),
        "best_score": float(study.best_trial.value) if completed else float("-inf"),
        "best_params": dict(study.best_trial.params) if completed else {},
        "early_best": float(early_best),
        "late_best": float(late_best),
        "slope": float(slope),
        "saturated": bool(saturated),
        "stage": str(args.stage),
        "timestamp": time.time(),
    }
    sat = state.setdefault("tpe_saturation", {})
    sat[arch_hash] = sat_entry
    if len(sat) > 64:
        keep = dict(sorted(sat.items(), key=lambda kv: kv[1].get("timestamp", 0.0))[-64:])
        state["tpe_saturation"] = keep
    save_state(args.run, state)
    enforce_population_limits(args.run)
    best_trial = study.best_trial
    payload = {
        "run": args.run,
        "architecture": str(architecture),
        "architecture_hash": arch_hash,
        "stage": args.stage,
        "trials": args.trials,
        "parallel_workers": parallel_workers,
        "best_trial": best_trial.number,
        "best_score": best_trial.value,
        "best_params": best_trial.params,
        "completed": completed,
        "leaderboard": str(run_dir(args.run) / "leaderboard.md"),
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


# ---------------------------------------------------------------------------
# Bookkeeping / leaderboard / status / promote
# ---------------------------------------------------------------------------

def enforce_population_limits(name: str) -> None:
    state = load_state(name)
    cfg = state["config"]
    rows = read_history(name)
    pop_size = int(cfg["population_size"])
    if len(rows) <= pop_size:
        return
    ranked = sorted(rows, key=score_of, reverse=True)
    active_ids = {r["id"] for r in ranked[:pop_size]}
    archive_ids = {r["id"] for r in ranked[: int(cfg["archive_size"])]}
    state["active_population_ids"] = sorted(active_ids)
    state["archive_ids"] = sorted(archive_ids)
    save_state(name, state)


def _interesting_metric_keys(rows: list[dict[str, Any]], max_extras: int = 4) -> list[str]:
    counts: dict[str, int] = {}
    for r in rows[:50]:
        for k, v in (r.get("metrics") or {}).items():
            if k in {EVAL_SCORE_KEY, "score", "stage", "invalid", "error"}:
                continue
            try:
                float(v)
            except (TypeError, ValueError):
                continue
            counts[k] = counts.get(k, 0) + 1
    return [k for k, _ in sorted(counts.items(), key=lambda kv: -kv[1])[:max_extras]]


def write_leaderboard(name: str) -> None:
    rows = sorted(read_history(name), key=score_of, reverse=True)
    extras = _interesting_metric_keys(rows)
    header = ["rank", "id", "island", "family", "score", *extras, "novelty", "mode"]
    sep = ["---:", "---", "---:", "---", "---:", *(["---:"] * len(extras)), "---:", "---"]
    lines = [
        f"# OpenEvolve Leaderboard ({name})",
        "",
        "| " + " | ".join(header) + " |",
        "|" + "|".join(sep) + "|",
    ]
    for i, row in enumerate(rows[:30], 1):
        m = row.get("metrics", {})
        extra_vals = []
        for k in extras:
            v = m.get(k, "")
            try:
                extra_vals.append(f"{float(v):.4f}")
            except (TypeError, ValueError):
                extra_vals.append(str(v))
        cells = [
            str(i),
            f"`{row['id']}`",
            str(int(row.get("island", 0))),
            str(row.get("island_family", "")),
            f"{score_of(row):.6f}",
            *extra_vals,
            f"{float(row.get('novelty', 0.0) or 0.0):.3f}",
            str(row.get("selection_mode", "")),
        ]
        lines.append("| " + " | ".join(cells) + " |")
    (run_dir(name) / "leaderboard.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def cmd_status(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = sorted(read_history(args.run), key=score_of, reverse=True)
    write_leaderboard(args.run)
    payload = {
        "run": args.run,
        "project_dir": state.get("project_dir", str(PROJECT_DIR)),
        "generation": state.get("generation", 0),
        "candidates": len(rows),
        "best": rows[0] if rows else None,
        "leaderboard": str(run_dir(args.run) / "leaderboard.md"),
        "working_candidate": state.get("working_candidate"),
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


def cmd_promote(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = [
        r for r in read_history(args.run)
        if is_valid_parent(r) and str(r.get("metrics", {}).get("stage", "")) == args.from_stage
    ]
    candidates: list[dict[str, Any]] = []
    if args.top_k is not None:
        candidates = sorted([r for r in rows if Path(r.get("path", "")).exists()], key=score_of, reverse=True)[: args.top_k]
    else:
        for island in range(int(state["config"]["num_islands"])):
            pool = [r for r in rows if int(r.get("island", 0)) == island and Path(r.get("path", "")).exists()]
            candidates.extend(sorted(pool, key=score_of, reverse=True)[: args.top_k_per_island])

    promoted = []
    workers = max(1, int(args.parallel_workers))

    def evaluate_parent(parent: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
        metrics = evaluate_candidate(args.run, Path(parent["path"]), args.to_stage)
        return parent, metrics

    if workers == 1 or len(candidates) <= 1:
        results = [evaluate_parent(parent) for parent in candidates]
    else:
        results = []
        with ThreadPoolExecutor(max_workers=min(workers, len(candidates))) as pool:
            futures = [pool.submit(evaluate_parent, parent) for parent in candidates]
            for future in as_completed(futures):
                results.append(future.result())

    for parent, metrics in results:
        island = int(parent.get("island", 0))
        row = make_row(state, Path(parent["path"]), metrics, parent_id=parent.get("id"), mode=f"promote_{args.from_stage}_to_{args.to_stage}", island=island)
        append_history(args.run, row)
        promoted.append({"parent": parent.get("id"), "promoted": row["id"], "island": island, "metrics": metrics})
    write_leaderboard(args.run)
    print(json.dumps({"promoted": promoted, "parallel_workers": workers, "leaderboard": str(run_dir(args.run) / "leaderboard.md")}, indent=2, ensure_ascii=False))
    return 0


def cmd_report(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = [
        r for r in read_history(args.run)
        if is_valid_parent(r) and str(r.get("metrics", {}).get("stage", "")) == args.stage
    ]
    payload = {"run": args.run, "stage": args.stage, "by_island": []}
    num_islands = int(state["config"]["num_islands"])
    for island in range(num_islands):
        meta = ISLANDS.get(island, {"family": f"branch_{island}"})
        pool = sorted([r for r in rows if int(r.get("island", 0)) == island], key=score_of, reverse=True)
        best = pool[0] if pool else None
        payload["by_island"].append({
            "island": island,
            "family": meta["family"],
            "evaluated": len(pool),
            "best_id": best.get("id") if best else None,
            "best_path": best.get("path") if best else None,
            "best_score": score_of(best) if best else None,
            "best_metrics": best.get("metrics", {}) if best else {},
        })
    out = run_dir(args.run) / "island_report.json"
    out.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({**payload, "report": str(out)}, indent=2, ensure_ascii=False))
    return 0


def cmd_plan(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = read_history(args.run)
    request = write_plan_request(args.run, state, rows, force=args.force)
    payload = {
        "plan_request": str(request),
        "research_plan": str(research_plan_path(args.run)),
        "message": "Have a plan agent use web search and reasoning, then replace research_plan.md with one branch per island.",
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


def cmd_replan(args: argparse.Namespace) -> int:
    state = load_state(args.run)
    rows = read_history(args.run)
    request = write_plan_request(args.run, state, rows, force=True, mode="replan")
    state.setdefault("replan_history", []).append({
        "generation": int(state.get("generation", 0)),
        "timestamp": time.time(),
        "trigger": getattr(args, "trigger", "manual"),
    })
    state["last_replan_generation"] = int(state.get("generation", 0))
    save_state(args.run, state)
    payload = {
        "plan_request": str(request),
        "research_plan": str(research_plan_path(args.run)),
        "message": "Have the plan agent review per-island leaderboard + branch_health, "
                   "decide KEEP/REFRESH/RETIRE&REPLACE per island, and rewrite research_plan.md. "
                   "The next `select` will use the updated plan.",
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


def _best_row(name: str) -> dict[str, Any] | None:
    rows = [r for r in read_history(name) if is_valid_parent(r)]
    if not rows:
        return None
    return max(rows, key=score_of)


# ---------------------------------------------------------------------------
# Mutator command / run loop
# ---------------------------------------------------------------------------

def run_mutator_command(args: argparse.Namespace, step: int) -> dict[str, Any]:
    if not args.mutator_cmd:
        raise SystemExit("--mutator-cmd is required when --mutation-engine command")

    state = load_state(args.run)
    candidate = Path(state["working_candidate"]).expanduser().resolve()
    request = mutation_request_path(args.run).expanduser().resolve()
    plan = research_plan_path(args.run).expanduser().resolve()
    leaderboard = (run_dir(args.run) / "leaderboard.md").expanduser().resolve()
    history = history_path(args.run).expanduser().resolve()
    state_file = state_path(args.run).expanduser().resolve()
    logs_dir = run_dir(args.run) / "mutator_logs"
    logs_dir.mkdir(parents=True, exist_ok=True)
    log_path = logs_dir / f"step_{step:04d}.log"

    values = {
        "run": args.run,
        "request": str(request),
        "candidate": str(candidate),
        "plan": str(plan),
        "stage": args.stage,
        "iteration": str(step),
        "loop_step": str(step),
        "leaderboard": str(leaderboard),
        "history": str(history),
        "state": str(state_file),
        "project_dir": str(PROJECT_DIR),
    }
    cmd = args.mutator_cmd.format_map(values)
    before_hash = code_hash(candidate) if candidate.exists() else ""
    env = dict(os.environ)
    env.update({
        "EVOLVE_RUN": args.run,
        "EVOLVE_REQUEST": str(request),
        "EVOLVE_CANDIDATE": str(candidate),
        "EVOLVE_PLAN": str(plan),
        "EVOLVE_STAGE": args.stage,
        "EVOLVE_ITERATION": str(step),
        "EVOLVE_LEADERBOARD": str(leaderboard),
        "EVOLVE_HISTORY": str(history),
        "EVOLVE_STATE": str(state_file),
        "EVOLVE_PROJECT_DIR": str(PROJECT_DIR),
    })
    started = time.time()
    try:
        cp = subprocess.run(
            cmd, shell=True, text=True, capture_output=True,
            timeout=args.mutator_timeout, env=env, cwd=str(run_dir(args.run)),
        )
        after_hash = code_hash(candidate) if candidate.exists() else ""
        payload = {
            "command": cmd,
            "returncode": cp.returncode,
            "elapsed_sec": time.time() - started,
            "candidate_changed": before_hash != after_hash,
            "before_hash": before_hash,
            "after_hash": after_hash,
            "stdout": cp.stdout[-8000:],
            "stderr": cp.stderr[-8000:],
        }
    except subprocess.TimeoutExpired as exc:
        payload = {
            "command": cmd,
            "returncode": -1,
            "elapsed_sec": time.time() - started,
            "candidate_changed": False,
            "before_hash": before_hash,
            "after_hash": code_hash(candidate) if candidate.exists() else "",
            "stdout": (exc.stdout or "")[-8000:] if isinstance(exc.stdout, str) else "",
            "stderr": (exc.stderr or "")[-8000:] if isinstance(exc.stderr, str) else "",
            "error": f"mutator timed out after {args.mutator_timeout}s",
        }
    log_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    payload["log_path"] = str(log_path)
    if payload["returncode"] != 0:
        raise RuntimeError(f"mutator command failed; see {log_path}")
    if args.require_candidate_change and not payload["candidate_changed"]:
        raise RuntimeError(f"mutator command did not modify candidate; see {log_path}")
    return payload


def cmd_run_loop(args: argparse.Namespace) -> int:
    if args.iterations <= 0:
        raise SystemExit("--iterations must be positive")

    initialized = state_path(args.run).exists()
    if not initialized:
        init_args = argparse.Namespace(
            run=args.run, force=False, initial=args.initial,
            stage=args.init_stage, seed=args.seed,
            population_size=args.population_size,
            archive_size=args.archive_size,
            num_islands=args.num_islands,
            elite_selection_ratio=args.elite_selection_ratio,
            exploitation_ratio=args.exploitation_ratio,
        )
        cmd_init(init_args)

    state = load_state(args.run)
    state["loop_runtime"] = {
        "stage": args.stage,
        "param_trials_per_architecture": int(args.param_trials_per_architecture),
        "tpe_startup_trials": int(args.tpe_startup_trials),
        "parallel_workers": int(args.parallel_workers),
        "mutation_engine": ("none" if args.no_generate else args.mutation_engine),
        "iterations": int(args.iterations),
    }
    save_state(args.run, state)
    rows = read_history(args.run)
    write_plan_request(args.run, state, rows, force=False)

    best = _best_row(args.run)
    best_score = score_of(best) if best else float("-inf")
    no_improve = 0
    loop_log: list[dict[str, Any]] = []

    for step in range(1, args.iterations + 1):
        before = best_score
        print(json.dumps({"loop_step": step, "phase": "select", "run": args.run}, ensure_ascii=False))
        cmd_select(argparse.Namespace(run=args.run, stage=args.stage))

        engine = "none" if args.no_generate else args.mutation_engine
        mutator_result: dict[str, Any] | None = None
        if engine == "generate":
            print(json.dumps({"loop_step": step, "phase": "generate", "run": args.run}, ensure_ascii=False))
            cmd_generate(argparse.Namespace(run=args.run))
        elif engine == "command":
            print(json.dumps({"loop_step": step, "phase": "mutator_command", "run": args.run}, ensure_ascii=False))
            try:
                mutator_result = run_mutator_command(args, step)
                print(json.dumps({"loop_step": step, "phase": "mutator_done", "result": {k: v for k, v in mutator_result.items() if k not in {"stdout", "stderr"}}}, ensure_ascii=False))
            except Exception as exc:
                if args.on_mutator_fail == "generate":
                    print(json.dumps({"loop_step": step, "phase": "mutator_failed_generate_fallback", "error": str(exc)}, ensure_ascii=False))
                    cmd_generate(argparse.Namespace(run=args.run))
                elif args.on_mutator_fail == "skip":
                    print(json.dumps({"loop_step": step, "phase": "mutator_failed_skip", "error": str(exc)}, ensure_ascii=False))
                    continue
                else:
                    raise
        elif engine == "none":
            print(json.dumps({"loop_step": step, "phase": "no_mutation", "run": args.run}, ensure_ascii=False))
        else:
            raise SystemExit(f"Unknown mutation engine: {engine}")

        if args.param_trials_per_architecture > 1:
            print(json.dumps({"loop_step": step, "phase": "param_batch", "run": args.run, "stage": args.stage, "trials": args.param_trials_per_architecture}, ensure_ascii=False))
            cmd_param_batch(argparse.Namespace(
                run=args.run, file=None,
                trials=args.param_trials_per_architecture,
                stage=args.stage,
                seed=args.seed + step,
                startup_trials=args.tpe_startup_trials,
                parallel_workers=args.parallel_workers,
                parentless=False,
            ))
        else:
            print(json.dumps({"loop_step": step, "phase": "submit", "run": args.run, "stage": args.stage}, ensure_ascii=False))
            cmd_submit(argparse.Namespace(
                run=args.run, file=None, stage=args.stage, parentless=False,
            ))

        best = _best_row(args.run)
        best_score = score_of(best) if best else float("-inf")
        improved = best_score > before + args.min_improvement
        no_improve = 0 if improved else no_improve + 1
        loop_log.append({
            "step": step,
            "best_score": best_score,
            "best_id": best.get("id") if best else None,
            "improved": improved,
            "no_improve": no_improve,
            "mutation_engine": engine,
            "mutator_log": mutator_result.get("log_path") if mutator_result else None,
        })

        if args.replan_every and step % args.replan_every == 0 and step < args.iterations:
            print(json.dumps({"loop_step": step, "phase": "replan", "run": args.run}, ensure_ascii=False))
            cmd_replan(argparse.Namespace(run=args.run, trigger=f"run-loop step {step}"))
            loop_log[-1]["replanned"] = True

        if args.promote_every and step % args.promote_every == 0:
            print(json.dumps({"loop_step": step, "phase": "promote", "from_stage": args.stage, "to_stage": args.promote_to_stage}, ensure_ascii=False))
            cmd_promote(argparse.Namespace(
                run=args.run, from_stage=args.stage, to_stage=args.promote_to_stage,
                top_k_per_island=args.top_k_per_island, top_k=args.promote_top_k,
                parallel_workers=args.parallel_workers,
            ))

        if args.target_score is not None and best_score >= args.target_score:
            print(json.dumps({"stopped": "target_score", "step": step, "best_score": best_score}, indent=2, ensure_ascii=False))
            break

        if args.patience is not None and no_improve >= args.patience:
            print(json.dumps({"stopped": "patience", "step": step, "best_score": best_score, "patience": args.patience}, indent=2, ensure_ascii=False))
            break

    write_leaderboard(args.run)
    payload = {
        "run": args.run,
        "iterations_requested": args.iterations,
        "iterations_completed": len(loop_log),
        "best": _best_row(args.run),
        "leaderboard": str(run_dir(args.run) / "leaderboard.md"),
        "loop_log": loop_log,
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _add_stage_arg(p: argparse.ArgumentParser, default: str = "small") -> None:
    p.add_argument("--stage", default=default,
                   help=f"Stage label passed to evaluator via EVAL_STAGE (known: {','.join(STAGES)}; any string accepted).")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", default=DEFAULT_RUN)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_init = sub.add_parser("init")
    p_init.add_argument("--force", action="store_true")
    p_init.add_argument("--initial", default=None, help="Path to initial_program.py (defaults to project dir).")
    _add_stage_arg(p_init, default="smoke")
    p_init.add_argument("--seed", type=int, default=42)
    p_init.add_argument("--population-size", type=int, default=40)
    p_init.add_argument("--archive-size", type=int, default=20)
    p_init.add_argument("--num-islands", type=int, default=3)
    p_init.add_argument("--elite-selection-ratio", type=float, default=0.20)
    p_init.add_argument("--exploitation-ratio", type=float, default=0.65)
    p_init.set_defaults(func=cmd_init)

    p_select = sub.add_parser("select")
    _add_stage_arg(p_select, default="small")
    p_select.set_defaults(func=cmd_select)

    p_plan = sub.add_parser("plan")
    p_plan.add_argument("--force", action="store_true")
    p_plan.set_defaults(func=cmd_plan)

    p_replan = sub.add_parser(
        "replan",
        help="Re-trigger the plan agent: review per-island leaderboard, retire/refresh ineffective branches, and rewrite research_plan.md in place.",
    )
    p_replan.set_defaults(func=cmd_replan, trigger="manual")

    p_torch = sub.add_parser("torch-smoke")
    p_torch.set_defaults(func=cmd_torch_smoke)

    p_generate = sub.add_parser("generate")
    p_generate.set_defaults(func=cmd_generate)

    p_submit = sub.add_parser("submit")
    p_submit.add_argument("--file", default=None)
    _add_stage_arg(p_submit, default="small")
    p_submit.add_argument("--parentless", action="store_true")
    p_submit.set_defaults(func=cmd_submit)

    p_param = sub.add_parser("param-batch")
    p_param.add_argument("--file", default=None)
    p_param.add_argument("--trials", type=int, default=12)
    _add_stage_arg(p_param, default="small")
    p_param.add_argument("--seed", type=int, default=None)
    p_param.add_argument("--startup-trials", type=int, default=5)
    p_param.add_argument("--parallel-workers", type=int, default=1)
    p_param.add_argument("--parentless", action="store_true")
    p_param.set_defaults(func=cmd_param_batch)

    p_status = sub.add_parser("status")
    p_status.set_defaults(func=cmd_status)

    p_promote = sub.add_parser("promote")
    p_promote.add_argument("--from-stage", default="small")
    p_promote.add_argument("--to-stage", default="full")
    p_promote.add_argument("--top-k-per-island", type=int, default=1)
    p_promote.add_argument("--top-k", type=int, default=None)
    p_promote.add_argument("--parallel-workers", type=int, default=1)
    p_promote.set_defaults(func=cmd_promote)

    p_loop = sub.add_parser("run-loop")
    p_loop.add_argument("--iterations", "-i", type=int, required=True)
    _add_stage_arg(p_loop, default="small")
    p_loop.add_argument("--initial", default=None)
    p_loop.add_argument("--seed", type=int, default=42)
    p_loop.add_argument("--init-stage", default="smoke")
    p_loop.add_argument("--population-size", type=int, default=40)
    p_loop.add_argument("--archive-size", type=int, default=20)
    p_loop.add_argument("--num-islands", type=int, default=3)
    p_loop.add_argument("--elite-selection-ratio", type=float, default=0.20)
    p_loop.add_argument("--exploitation-ratio", type=float, default=0.65)
    p_loop.add_argument("--target-score", type=float, default=None)
    p_loop.add_argument("--patience", type=int, default=None)
    p_loop.add_argument("--min-improvement", type=float, default=1e-6)
    p_loop.add_argument("--promote-every", type=int, default=0)
    p_loop.add_argument("--replan-every", type=int, default=0,
                        help="Trigger plan agent every K iterations to retire ineffective islands and propose new branches (0 disables).")
    p_loop.add_argument("--promote-to-stage", default="full")
    p_loop.add_argument("--top-k-per-island", type=int, default=1)
    p_loop.add_argument("--promote-top-k", type=int, default=None)
    p_loop.add_argument("--parallel-workers", type=int, default=1)
    p_loop.add_argument("--param-trials-per-architecture", type=int, default=1)
    p_loop.add_argument("--tpe-startup-trials", type=int, default=5)
    p_loop.add_argument("--mutation-engine", choices=["command", "generate", "none"], default="generate")
    p_loop.add_argument("--mutator-cmd", default=None,
                        help="External agent command. Placeholders: {run} {request} {candidate} {plan} {stage} {iteration} {leaderboard} {history} {state} {project_dir}")
    p_loop.add_argument("--mutator-timeout", type=int, default=1800)
    p_loop.add_argument("--on-mutator-fail", choices=["stop", "generate", "skip"], default="stop")
    p_loop.add_argument("--require-candidate-change", action="store_true")
    p_loop.add_argument("--no-generate", action="store_true")
    p_loop.set_defaults(func=cmd_run_loop)

    p_report = sub.add_parser("report")
    _add_stage_arg(p_report, default="small")
    p_report.set_defaults(func=cmd_report)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
