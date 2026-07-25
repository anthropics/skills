#!/usr/bin/env python3
"""
autoresearch-agent: Setup Experiment

Initialize a new experiment with domain, target, evaluator, and git branch.
Creates the .autoresearch/{domain}/{name}/ directory structure.

Usage:
    python scripts/setup_experiment.py --domain engineering --name api-speed \
        --target src/api/search.py --eval "pytest bench.py" \
        --metric p50_ms --direction lower

    python scripts/setup_experiment.py --domain marketing --name medium-ctr \
        --target content/titles.md --eval "python evaluate.py" \
        --metric ctr_score --direction higher --evaluator llm_judge_content

    python scripts/setup_experiment.py --list          # List all experiments
    python scripts/setup_experiment.py --list-evaluators  # List available evaluators
"""

import argparse
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

DOMAINS = ["engineering", "marketing", "content", "prompts", "custom"]

EVALUATOR_DIR = Path(__file__).parent.parent / "evaluators"

DEFAULT_CONFIG = """# autoresearch global config
default_time_budget_minutes: 5
default_scope: project
dashboard_format: markdown
"""

GITIGNORE_CONTENT = """# autoresearch — experiment logs are local state
**/results.tsv
**/run.log
**/run.*.log
config.yaml
"""


def run_cmd(cmd, cwd=None, timeout=None):
    """Run shell command, return (returncode, stdout, stderr)."""
    result = subprocess.run(
        cmd, shell=True, capture_output=True, text=True,
        cwd=cwd, timeout=timeout
    )
    return result.returncode, result.stdout.strip(), result.stderr.strip()


def get_autoresearch_root(scope, project_root=None):
    """Get the .autoresearch root directory based on scope."""
    if scope == "user":
        return Path.home() / ".autoresearch"
    return Path(project_root or ".") / ".autoresearch"


def init_root(root):
    """Initialize .autoresearch root if it doesn't exist."""
    created = False
    if not root.exists():
        root.mkdir(parents=True)
        created = True
        print(f"  Created {root}/")

    config_file = root / "config.yaml"
    if not config_file.exists():
        config_file.write_text(DEFAULT_CONFIG)
        print(f"  Created {config_file}")

    gitignore = root / ".gitignore"
    if not gitignore.exists():
        gitignore.write_text(GITIGNORE_CONTENT)
        print(f"  Created {gitignore}")

    return created


def create_program_md(experiment_dir, domain, name, target, metric, direction, constraints=""):
    """Generate a program.md template for the experiment."""
    direction_word = "Minimize" if direction == "lower" else "Maximize"
    content = f"""# autoresearch — {name}

## Goal
{direction_word} `{metric}` on `{target}`. {"Lower" if direction == "lower" else "Higher"} is better.

## What the Agent Can Change
- Only `{target}` — this is the single file being optimized.
- Everything inside that file is fair game unless constrained below.

## What the Agent Cannot Change
- The evaluation script (`evaluate.py` or the eval command). It is read-only.
- Dependencies — do not add new packages or imports that aren't already available.
- Any other files in the project unless explicitly noted here.
{f"- Additional constraints: {constraints}" if constraints else ""}

## Strategy
1. First run: establish baseline. Do not change anything.
2. Profile/analyze the current state — understand why the metric is what it is.
3. Try the most obvious improvement first (low-hanging fruit).
4. If that works, push further in the same direction.
5. If stuck, try something orthogonal or radical.
6. Read the git log of previous experiments. Don't repeat failed approaches.

## Simplicity Rule
A small improvement that adds ugly complexity is NOT worth it.
Equal performance with simpler code IS worth it.
Removing code that gets same results is the best outcome.

## Stop When
You don't stop. The human will interrupt you when they're satisfied.
If no improvement in 20+ consecutive runs, change strategy drastically.
"""
    (experiment_dir / "program.md").write_text(content)


def create_config(experiment_dir, target, eval_cmd, metric, direction, time_budget):
    """Write experiment config."""
    content = f"""target: {target}
evaluate_cmd: {eval_cmd}
metric: {metric}
metric_direction: {direction}
metric_grep: ^{metric}:
time_budget_minutes: {time_budget}
created: {datetime.now().strftime('%Y-%m-%d %H:%M')}
"""
    (experiment_dir / "config.cfg").write_text(content)


def init_results_tsv(experiment_dir):
    """Create results.tsv with header."""
    tsv = experiment_dir / "results.tsv"
    if tsv.exists():
        print(f"  results.tsv already exists ({tsv.stat().st_size} bytes)")
        return
    tsv.write_text("commit\tmetric\tstatus\tdescription\n")
    print("  Created results.tsv")


def copy_evaluator(experiment_dir, evaluator_name):
    """Copy a built-in evaluator to the experiment directory."""
    source = EVALUATOR_DIR / f"{evaluator_name}.py"
    if not source.exists():
        print(f"  Warning: evaluator '{evaluator_name}' not found in {EVALUATOR_DIR}")
        print(f"  Available: {', '.join(f.stem for f in EVALUATOR_DIR.glob('*.py'))}")
        return False
    dest = experiment_dir / "evaluate.py"
    shutil.copy2(source, dest)
    print(f"  Copied evaluator: {evaluator_name}.py -> evaluate.py")
    return True


def create_branch(path, domain, name):
    """Create and checkout the experiment branch."""
    branch = f"autoresearch/{domain}/{name}"
    result = subprocess.run(
        ["git", "checkout", "-b", branch],
        cwd=path, capture_output=True, text=True
    )
    if result.returncode != 0:
        if "already exists" in result.stderr:
            print(f"  Branch '{branch}' already exists. Checking out...")
            subprocess.run(
                ["git", "checkout", branch],
                cwd=path, capture_output=True, text=True
            )
            return branch
        print(f"  Warning: could not create branch: {result.stderr}")
        return None
    print(f"  Created branch: {branch}")
    return branch


def list_experiments(root):
    """List all experiments across all domains."""
    if not root.exists():
        print("No experiments found. Run setup to create your first experiment.")
        return

    experiments = []
    for domain_dir in sorted(root.iterdir()):
        if not domain_dir.is_dir() or domain_dir.name.startswith("."):
            continue
        for exp_dir in sorted(domain_dir.iterdir()):
            if not exp_dir.is_dir():
                continue
            cfg_file = exp_dir / "config.cfg"
            if not cfg_file.exists():
                continue
            config = {}
            for line in cfg_file.read_text().splitlines():
                if ":" in line:
                    k, v = line.split(":", 1)
                    config[k.strip()] = v.strip()

            # Count results
            tsv = exp_dir / "results.tsv"
            runs = 0
            if tsv.exists():
                runs = max(0, len(tsv.read_text().splitlines()) - 1)

            experiments.append({
                "domain": domain_dir.name,
                "name": exp_dir.name,
                "target": config.get("target", "?"),
                "metric": config.get("metric", "?"),
                "runs": runs,
            })

    if not experiments:
        print("No experiments found.")
        return

    print(f"\n{'DOMAIN':<15} {'EXPERIMENT':<25} {'TARGET':<30} {'METRIC':<15} {'RUNS':>5}")
    print("-" * 95)
    for e in experiments:
        print(f"{e['domain']:<15} {e['name']:<25} {e['target']:<30} {e['metric']:<15} {e['runs']:>5}")
    print(f"\nTotal: {len(experiments)} experiments")


def list_evaluators():
    """List available built-in evaluators."""
    if not EVALUATOR_DIR.exists():
        print("No evaluators directory found.")
        return

    print(f"\nAvailable evaluators ({EVALUATOR_DIR}):\n")
    for f in sorted(EVALUATOR_DIR.glob("*.py")):
        # Read first docstring line
        desc = ""
        for line in f.read_text().splitlines():
            stripped = line.strip()
            if stripped.startswith('"""') or stripped.startswith("'''"):
                quote = stripped[:3]
                # Single-line docstring: """Description."""
                after_quote = stripped[3:]
                if after_quote and after_quote.rstrip(quote[0]).strip():
                    desc = after_quote.rstrip('"').rstrip("'").strip()
                    break
                continue
            if stripped and not line.startswith("#!"):
                desc = stripped.strip('"').strip("'")
                break
        print(f"  {f.stem:<25} {desc}")


def main():
    parser = argparse.ArgumentParser(description="autoresearch-agent setup")
    parser.add_argument("--domain", choices=DOMAINS, help="Experiment domain")
    parser.add_argument("--name", help="Experiment name (e.g. api-speed, medium-ctr)")
    parser.add_argument("--target", help="Target file to optimize")
    parser.add_argument("--eval", dest="eval_cmd", help="Evaluation command")
    parser.add_argument("--metric", help="Metric name (must appear in eval output as 'name: value')")
    parser.add_argument("--direction", choices=["lower", "higher"], default="lower",
                        help="Is lower or higher better?")
    parser.add_argument("--time-budget", type=int, default=5, help="Minutes per experiment (default: 5)")
    parser.add_argument("--evaluator", help="Built-in evaluator to copy (e.g. benchmark_speed)")
    parser.add_argument("--scope", choices=["project", "user"], default="project",
                        help="Where to store experiments: project (./) or user (~/)")
    parser.add_argument("--constraints", default="", help="Additional constraints for program.md")
    parser.add_argument("--path", default=".", help="Project root path")
    parser.add_argument("--skip-branch", action="store_true", help="Don't create git branch")
    parser.add_argument("--list", action="store_true", help="List all experiments")
    parser.add_argument("--list-evaluators", action="store_true", help="List available evaluators")
    args = parser.parse_args()

    project_root = Path(args.path).resolve()

    # List mode
    if args.list:
        root = get_autoresearch_root("project", project_root)
        list_experiments(root)
        user_root = get_autoresearch_root("user")
        if user_root.exists() and user_root != root:
            print(f"\n--- User-level experiments ({user_root}) ---")
            list_experiments(user_root)
        return

    if args.list_evaluators:
        list_evaluators()
        return

    # Validate required args for setup
    if not all([args.domain, args.name, args.target, args.eval_cmd, args.metric]):
        parser.error("Required: --domain, --name, --target, --eval, --metric")

    root = get_autoresearch_root(args.scope, project_root)

    print(f"\n  autoresearch-agent setup")
    print(f"  Project: {project_root}")
    print(f"  Scope: {args.scope}")
    print(f"  Domain: {args.domain}")
    print(f"  Experiment: {args.name}")
    print(f"  Time: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")

    # Check git
    result = subprocess.run(
        ["git", "rev-parse", "--is-inside-work-tree"],
        cwd=str(project_root), capture_output=True, text=True
    )
    code = result.returncode
    if code != 0:
        print("  Error: not a git repository. Run: git init && git add . && git commit -m 'initial'")
        sys.exit(1)
    print("  Git repository found")

    # Check target file
    target_path = project_root / args.target
    if not target_path.exists():
        print(f"  Error: target file not found: {args.target}")
        sys.exit(1)
    print(f"  Target file found: {args.target}")

    # Init root
    init_root(root)

    # Create experiment directory
    experiment_dir = root / args.domain / args.name
    if experiment_dir.exists():
        print(f"  Warning: experiment '{args.domain}/{args.name}' already exists.")
        print(f"  Use --name with a different name, or delete {experiment_dir}")
        sys.exit(1)
    experiment_dir.mkdir(parents=True)
    print(f"  Created {experiment_dir}/")

    # Create files
    create_program_md(experiment_dir, args.domain, args.name,
                      args.target, args.metric, args.direction, args.constraints)
    print("  Created program.md")

    create_config(experiment_dir, args.target, args.eval_cmd,
                  args.metric, args.direction, args.time_budget)
    print("  Created config.cfg")

    init_results_tsv(experiment_dir)

    # Copy evaluator if specified
    if args.evaluator:
        copy_evaluator(experiment_dir, args.evaluator)

    # Create git branch
    if not args.skip_branch:
        create_branch(str(project_root), args.domain, args.name)

    # Test evaluation command
    print(f"\n  Testing evaluation: {args.eval_cmd}")
    code, out, err = run_cmd(args.eval_cmd, cwd=str(project_root), timeout=60)
    if code != 0:
        print(f"  Warning: eval command failed (exit {code})")
        if err:
            print(f"  stderr: {err[:200]}")
        print("  Fix the eval command before running the experiment loop.")
    else:
        # Check metric is parseable
        full_output = out + "\n" + err
        metric_found = False
        for line in full_output.splitlines():
            if line.strip().startswith(f"{args.metric}:"):
                metric_found = True
                print(f"  Eval works. Baseline: {line.strip()}")
                break
        if not metric_found:
            print(f"  Warning: eval ran but '{args.metric}:' not found in output.")
            print(f"  Make sure your eval command outputs: {args.metric}: <value>")

    # Summary
    print(f"\n  Setup complete!")
    print(f"  Experiment: {args.domain}/{args.name}")
    print(f"  Target: {args.target}")
    print(f"  Metric: {args.metric} ({args.direction} is better)")
    print(f"  Budget: {args.time_budget} min/experiment")
    if not args.skip_branch:
        print(f"  Branch: autoresearch/{args.domain}/{args.name}")
    print(f"\n  To start:")
    print(f"  python scripts/run_experiment.py --experiment {args.domain}/{args.name} --single")


if __name__ == "__main__":
    main()
