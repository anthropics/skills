#!/usr/bin/env python3
"""Control the local OpenEvolve runtime from Claude Code.

This helper covers the *runtime* concerns (status, bootstrap, optional native
OpenEvolve launch, ad-hoc evaluator call) that surround `evolve.py`. It is
task-agnostic: the project directory it points at must contain at minimum an
`evaluator.py` (and typically `initial_program.py`).
"""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
from pathlib import Path


def _env(name: str, default: str) -> str:
    return os.environ.get(name, default)


LOCAL_HOME = Path.home()
OPENEVOLVE_HOME = _env("OPENEVOLVE_HOME", str(LOCAL_HOME / "openevolve"))
PROJECT_DIR = _env("EVOLVE_PROJECT_DIR", str(Path.cwd()))
EVOLVE_PYTHON = _env("EVOLVE_PYTHON", "python3")
LOG_DIR = _env("EVOLVE_LOG_DIR", str(LOCAL_HOME / ".claude" / "openevolve-runs" / "_logs"))


def run_local(script: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", "-s"], input=script, text=True, capture_output=True, check=check
    )


def print_result(cp: subprocess.CompletedProcess[str]) -> int:
    if cp.stdout:
        print(cp.stdout.rstrip())
    if cp.stderr:
        print(cp.stderr.rstrip(), file=sys.stderr)
    return cp.returncode


def status(_: argparse.Namespace) -> int:
    script = f"""
set +e
echo "== host =="
hostname
uptime
df -h "$HOME" 2>/dev/null || true
echo
echo "== python runtime =="
which {shlex.quote(EVOLVE_PYTHON)} || true
{shlex.quote(EVOLVE_PYTHON)} --version 2>&1 || true
echo
echo "== project =="
echo "EVOLVE_PROJECT_DIR={PROJECT_DIR}"
for p in {shlex.quote(PROJECT_DIR)}/initial_program.py {shlex.quote(PROJECT_DIR)}/evaluator.py; do
  if [ -e "$p" ]; then ls -ldh "$p"; else echo "MISSING $p"; fi
done
echo
echo "== openevolve repo (optional, only needed for native LLM-loop mode) =="
if [ -d {shlex.quote(OPENEVOLVE_HOME)} ]; then ls -ldh {shlex.quote(OPENEVOLVE_HOME)}; else echo "MISSING {OPENEVOLVE_HOME}"; fi
echo
echo "== processes =="
pgrep -af 'openevolve|alphaevolve|evolve.py' || true
echo
echo "== gpu =="
command -v nvidia-smi >/dev/null 2>&1 && nvidia-smi -L || echo "nvidia-smi not available"
echo
echo "== recent logs =="
mkdir -p {shlex.quote(LOG_DIR)}
ls -lt {shlex.quote(LOG_DIR)}/openevolve_*.log 2>/dev/null | head -5 || true
LOG=$(ls -t {shlex.quote(LOG_DIR)}/openevolve_*.log 2>/dev/null | head -1)
if [ -n "$LOG" ]; then tail -30 "$LOG" 2>/dev/null || true; else echo "No OpenEvolve logs found."; fi
"""
    return print_result(run_local(script, check=False))


def bootstrap(args: argparse.Namespace) -> int:
    extras = " ".join(args.extra) if args.extra else ""
    script = f"""
set -e
mkdir -p "$(dirname {shlex.quote(OPENEVOLVE_HOME)})"
if [ ! -d {shlex.quote(OPENEVOLVE_HOME)}/.git ]; then
  git clone https://github.com/algorithmicsuperintelligence/openevolve {shlex.quote(OPENEVOLVE_HOME)}
fi
cd {shlex.quote(OPENEVOLVE_HOME)}
if ! command -v {shlex.quote(EVOLVE_PYTHON)} >/dev/null 2>&1; then
  echo "Missing Python runtime: {EVOLVE_PYTHON}" >&2
  exit 2
fi
{shlex.quote(EVOLVE_PYTHON)} -m pip install -e . -q
{shlex.quote(EVOLVE_PYTHON)} -m pip install optuna numpy {extras} -q
echo "bootstrapped: {OPENEVOLVE_HOME}"
"""
    return print_result(run_local(script, check=False))


def launch(args: argparse.Namespace) -> int:
    """Optional: launch OpenEvolve's native LLM-controlled loop on the project.

    Requires OPENAI_API_KEY and an OpenEvolve example checked into the cloned
    OpenEvolve repo at $OPENEVOLVE_HOME/examples/<name>/.
    """
    api_key = os.environ.get("OPENAI_API_KEY", "")
    if not api_key:
        print("OPENAI_API_KEY is required for native LLM-loop launch.", file=sys.stderr)
        return 2

    iterations = str(args.iterations or os.environ.get("ITERATIONS", "30"))
    example = args.example
    Path(LOG_DIR).mkdir(parents=True, exist_ok=True)
    log_name = f"{LOG_DIR}/openevolve_$(date +%Y%m%d_%H%M%S).log"
    launch_env = {
        "OPENAI_API_KEY": api_key,
        "ITERATIONS": iterations,
        "PYTHONUNBUFFERED": "1",
    }
    env_prefix = " ".join(f"{k}={shlex.quote(v)}" for k, v in launch_env.items())
    script = f"""
set -e
test -d {shlex.quote(OPENEVOLVE_HOME)} || {{ echo "Missing repo: {OPENEVOLVE_HOME}. Run bootstrap." >&2; exit 3; }}
EX={shlex.quote(OPENEVOLVE_HOME)}/examples/{shlex.quote(example)}
test -d "$EX" || {{ echo "Missing example: $EX" >&2; exit 4; }}
RUN_SCRIPT=""
for s in run_local.sh run.sh; do
  if [ -f "$EX/$s" ]; then RUN_SCRIPT="$EX/$s"; break; fi
done
test -n "$RUN_SCRIPT" || {{ echo "Missing run script in $EX (run_local.sh|run.sh)" >&2; exit 5; }}
cd {shlex.quote(OPENEVOLVE_HOME)}
LOG={shlex.quote(log_name)}
nohup bash -lc {shlex.quote(env_prefix + ' bash "$RUN_SCRIPT"')} > "$LOG" 2>&1 &
echo "launched PID=$!"
echo "log=$LOG"
sleep 3
tail -40 "$LOG" || true
"""
    return print_result(run_local(script, check=False))


def evaluate(args: argparse.Namespace) -> int:
    """One-shot evaluator call: useful for sanity checks."""
    program = args.program or f"{PROJECT_DIR}/initial_program.py"
    script = f"""
set -e
test -f {shlex.quote(PROJECT_DIR)}/evaluator.py || {{ echo "Missing evaluator: {PROJECT_DIR}/evaluator.py" >&2; exit 3; }}
test -f {shlex.quote(program)} || {{ echo "Missing program: {program}" >&2; exit 4; }}
cd {shlex.quote(PROJECT_DIR)}
export EVAL_STAGE={shlex.quote(args.stage)}
export EVOLVE_STAGE={shlex.quote(args.stage)}
export PYTHONUNBUFFERED=1
{shlex.quote(EVOLVE_PYTHON)} evaluator.py {shlex.quote(program)}
"""
    return print_result(run_local(script, check=False))


def tail(args: argparse.Namespace) -> int:
    n = int(args.lines)
    script = f"""
LOG=$(ls -t {shlex.quote(LOG_DIR)}/openevolve_*.log 2>/dev/null | head -1)
if [ -z "$LOG" ]; then echo "No OpenEvolve logs found."; exit 0; fi
echo "log=$LOG"
tail -{n} "$LOG"
"""
    return print_result(run_local(script, check=False))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status").set_defaults(func=status)

    p_boot = sub.add_parser("bootstrap")
    p_boot.add_argument("--extra", nargs="*", default=[], help="Extra pip packages to install (e.g. torch pandas).")
    p_boot.set_defaults(func=bootstrap)

    p_launch = sub.add_parser("launch")
    p_launch.add_argument("--example", required=True, help="OpenEvolve example subdirectory under $OPENEVOLVE_HOME/examples/.")
    p_launch.add_argument("--iterations", type=int, default=None)
    p_launch.set_defaults(func=launch)

    p_eval = sub.add_parser("evaluate")
    p_eval.add_argument("--program", default=None)
    p_eval.add_argument("--stage", default="smoke")
    p_eval.set_defaults(func=evaluate)

    p_tail = sub.add_parser("tail")
    p_tail.add_argument("--lines", type=int, default=120)
    p_tail.set_defaults(func=tail)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
