#!/usr/bin/env python3
"""
autoresearch-agent: Results Viewer

View experiment results in multiple formats: terminal, CSV, Markdown.
Supports single experiment, domain, or cross-experiment dashboard.

Usage:
    python scripts/log_results.py --experiment engineering/api-speed
    python scripts/log_results.py --domain engineering
    python scripts/log_results.py --dashboard
    python scripts/log_results.py --experiment engineering/api-speed --format csv --output results.csv
    python scripts/log_results.py --experiment engineering/api-speed --format markdown --output results.md
    python scripts/log_results.py --dashboard --format markdown --output dashboard.md
"""

import argparse
import csv
import io
import sys
import time
from pathlib import Path


def find_autoresearch_root():
    """Find .autoresearch/ in project or user home."""
    project_root = Path(".").resolve() / ".autoresearch"
    if project_root.exists():
        return project_root
    user_root = Path.home() / ".autoresearch"
    if user_root.exists():
        return user_root
    return None


def load_config(experiment_dir):
    """Load config.cfg."""
    cfg_file = experiment_dir / "config.cfg"
    config = {}
    if cfg_file.exists():
        for line in cfg_file.read_text().splitlines():
            if ":" in line:
                k, v = line.split(":", 1)
                config[k.strip()] = v.strip()
    return config


def load_results(experiment_dir):
    """Load results.tsv into list of dicts."""
    tsv = experiment_dir / "results.tsv"
    if not tsv.exists():
        return []
    results = []
    for line in tsv.read_text().splitlines()[1:]:
        parts = line.split("\t")
        if len(parts) >= 4:
            try:
                metric = float(parts[1]) if parts[1] != "N/A" else None
            except ValueError:
                metric = None
            results.append({
                "commit": parts[0],
                "metric": metric,
                "status": parts[2],
                "description": parts[3],
            })
    return results


def compute_stats(results, direction):
    """Compute statistics from results."""
    keeps = [r for r in results if r["status"] == "keep"]
    discards = [r for r in results if r["status"] == "discard"]
    crashes = [r for r in results if r["status"] == "crash"]

    valid_keeps = [r for r in keeps if r["metric"] is not None]
    baseline = valid_keeps[0]["metric"] if valid_keeps else None
    if valid_keeps:
        best = min(r["metric"] for r in valid_keeps) if direction == "lower" else max(r["metric"] for r in valid_keeps)
    else:
        best = None

    pct_change = None
    if baseline is not None and best is not None and baseline != 0:
        if direction == "lower":
            pct_change = (baseline - best) / baseline * 100
        else:
            pct_change = (best - baseline) / baseline * 100

    return {
        "total": len(results),
        "keeps": len(keeps),
        "discards": len(discards),
        "crashes": len(crashes),
        "baseline": baseline,
        "best": best,
        "pct_change": pct_change,
    }


# --- Terminal Output ---

def print_experiment(experiment_dir, experiment_path):
    """Print single experiment results to terminal."""
    config = load_config(experiment_dir)
    results = load_results(experiment_dir)
    direction = config.get("metric_direction", "lower")
    metric_name = config.get("metric", "metric")

    if not results:
        print(f"No results for {experiment_path}")
        return

    stats = compute_stats(results, direction)

    print(f"\n{'─' * 65}")
    print(f"  {experiment_path}")
    print(f"  Target: {config.get('target', '?')} | Metric: {metric_name} ({direction})")
    print(f"{'─' * 65}")
    print(f"  Total: {stats['total']} | Keep: {stats['keeps']} | Discard: {stats['discards']} | Crash: {stats['crashes']}")

    if stats["baseline"] is not None and stats["best"] is not None:
        pct = f" ({stats['pct_change']:+.1f}%)" if stats["pct_change"] is not None else ""
        print(f"  Baseline: {stats['baseline']:.6f} -> Best: {stats['best']:.6f}{pct}")

    print(f"\n  {'COMMIT':<10} {'METRIC':>12} {'STATUS':<10} DESCRIPTION")
    print(f"  {'─' * 60}")
    for r in results:
        m = f"{r['metric']:.6f}" if r["metric"] is not None else "N/A     "
        icon = {"keep": "+", "discard": "-", "crash": "!"}.get(r["status"], "?")
        print(f"  {r['commit']:<10} {m:>12} {icon} {r['status']:<7} {r['description'][:35]}")
    print()


def print_dashboard(root):
    """Print cross-experiment dashboard."""
    experiments = []
    for domain_dir in sorted(root.iterdir()):
        if not domain_dir.is_dir() or domain_dir.name.startswith("."):
            continue
        for exp_dir in sorted(domain_dir.iterdir()):
            if not exp_dir.is_dir() or not (exp_dir / "config.cfg").exists():
                continue
            config = load_config(exp_dir)
            results = load_results(exp_dir)
            direction = config.get("metric_direction", "lower")
            stats = compute_stats(results, direction)

            best_str = f"{stats['best']:.4f}" if stats["best"] is not None else "—"
            pct_str = f"{stats['pct_change']:+.1f}%" if stats["pct_change"] is not None else "—"

            # Determine status
            status = "idle"
            if stats["total"] > 0:
                tsv = exp_dir / "results.tsv"
                if tsv.exists():
                    age_hours = (time.time() - tsv.stat().st_mtime) / 3600
                    status = "active" if age_hours < 1 else "paused" if age_hours < 24 else "done"

            experiments.append({
                "domain": domain_dir.name,
                "name": exp_dir.name,
                "runs": stats["total"],
                "kept": stats["keeps"],
                "best": best_str,
                "change": pct_str,
                "status": status,
                "metric": config.get("metric", "?"),
            })

    if not experiments:
        print("No experiments found.")
        return experiments

    print(f"\n{'─' * 90}")
    print(f"  autoresearch — Dashboard")
    print(f"{'─' * 90}")
    print(f"  {'DOMAIN':<15} {'EXPERIMENT':<20} {'RUNS':>5} {'KEPT':>5} {'BEST':>12} {'CHANGE':>10} {'STATUS':<8}")
    print(f"  {'─' * 85}")
    for e in experiments:
        print(f"  {e['domain']:<15} {e['name']:<20} {e['runs']:>5} {e['kept']:>5} {e['best']:>12} {e['change']:>10} {e['status']:<8}")
    print()
    return experiments


# --- CSV Export ---

def export_experiment_csv(experiment_dir, experiment_path):
    """Export single experiment as CSV string."""
    config = load_config(experiment_dir)
    results = load_results(experiment_dir)
    direction = config.get("metric_direction", "lower")
    stats = compute_stats(results, direction)

    buf = io.StringIO()
    writer = csv.writer(buf)

    # Header with metadata
    writer.writerow(["# Experiment", experiment_path])
    writer.writerow(["# Target", config.get("target", "")])
    writer.writerow(["# Metric", f"{config.get('metric', '')} ({direction} is better)"])
    if stats["baseline"] is not None:
        writer.writerow(["# Baseline", f"{stats['baseline']:.6f}"])
    if stats["best"] is not None:
        pct = f" ({stats['pct_change']:+.1f}%)" if stats["pct_change"] is not None else ""
        writer.writerow(["# Best", f"{stats['best']:.6f}{pct}"])
    writer.writerow(["# Total", stats["total"]])
    writer.writerow(["# Keep/Discard/Crash", f"{stats['keeps']}/{stats['discards']}/{stats['crashes']}"])
    writer.writerow([])

    writer.writerow(["Commit", "Metric", "Status", "Description"])
    for r in results:
        m = f"{r['metric']:.6f}" if r["metric"] is not None else "N/A"
        writer.writerow([r["commit"], m, r["status"], r["description"]])

    return buf.getvalue()


def export_dashboard_csv(root, domain_filter=None):
    """Export dashboard as CSV string."""
    experiments = []
    for domain_dir in sorted(root.iterdir()):
        if not domain_dir.is_dir() or domain_dir.name.startswith("."):
            continue
        if domain_filter and domain_dir.name != domain_filter:
            continue
        for exp_dir in sorted(domain_dir.iterdir()):
            if not exp_dir.is_dir() or not (exp_dir / "config.cfg").exists():
                continue
            config = load_config(exp_dir)
            results = load_results(exp_dir)
            direction = config.get("metric_direction", "lower")
            stats = compute_stats(results, direction)
            best_str = f"{stats['best']:.6f}" if stats["best"] is not None else ""
            pct_str = f"{stats['pct_change']:+.1f}%" if stats["pct_change"] is not None else ""
            experiments.append([
                domain_dir.name, exp_dir.name, config.get("metric", ""),
                stats["total"], stats["keeps"], stats["discards"], stats["crashes"],
                best_str, pct_str
            ])

    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["Domain", "Experiment", "Metric", "Runs", "Kept", "Discarded", "Crashed", "Best", "Change"])
    for e in experiments:
        writer.writerow(e)
    return buf.getvalue()


# --- Markdown Export ---

def export_experiment_markdown(experiment_dir, experiment_path):
    """Export single experiment as Markdown string."""
    config = load_config(experiment_dir)
    results = load_results(experiment_dir)
    direction = config.get("metric_direction", "lower")
    metric_name = config.get("metric", "metric")
    stats = compute_stats(results, direction)

    lines = []
    lines.append(f"# Autoresearch: {experiment_path}\n")
    lines.append(f"**Target:** `{config.get('target', '?')}`  ")
    lines.append(f"**Metric:** `{metric_name}` ({direction} is better)  ")
    lines.append(f"**Experiments:** {stats['total']} total — {stats['keeps']} kept, {stats['discards']} discarded, {stats['crashes']} crashed\n")

    if stats["baseline"] is not None and stats["best"] is not None:
        pct = f" ({stats['pct_change']:+.1f}%)" if stats["pct_change"] is not None else ""
        lines.append(f"**Progress:** `{stats['baseline']:.6f}` → `{stats['best']:.6f}`{pct}\n")

    lines.append(f"| Commit | Metric | Status | Description |")
    lines.append(f"|--------|--------|--------|-------------|")
    for r in results:
        m = f"`{r['metric']:.6f}`" if r["metric"] is not None else "N/A"
        lines.append(f"| `{r['commit']}` | {m} | {r['status']} | {r['description']} |")
    lines.append("")

    return "\n".join(lines)


def export_dashboard_markdown(root, domain_filter=None):
    """Export dashboard as Markdown string."""
    lines = []
    lines.append("# Autoresearch Dashboard\n")
    lines.append("| Domain | Experiment | Metric | Runs | Kept | Best | Change | Status |")
    lines.append("|--------|-----------|--------|------|------|------|--------|--------|")

    for domain_dir in sorted(root.iterdir()):
        if not domain_dir.is_dir() or domain_dir.name.startswith("."):
            continue
        if domain_filter and domain_dir.name != domain_filter:
            continue
        for exp_dir in sorted(domain_dir.iterdir()):
            if not exp_dir.is_dir() or not (exp_dir / "config.cfg").exists():
                continue
            config = load_config(exp_dir)
            results = load_results(exp_dir)
            direction = config.get("metric_direction", "lower")
            stats = compute_stats(results, direction)
            best = f"`{stats['best']:.4f}`" if stats["best"] is not None else "—"
            pct = f"{stats['pct_change']:+.1f}%" if stats["pct_change"] is not None else "—"

            tsv = exp_dir / "results.tsv"
            status = "idle"
            if tsv.exists() and stats["total"] > 0:
                age_h = (time.time() - tsv.stat().st_mtime) / 3600
                status = "active" if age_h < 1 else "paused" if age_h < 24 else "done"

            lines.append(f"| {domain_dir.name} | {exp_dir.name} | {config.get('metric', '?')} | {stats['total']} | {stats['keeps']} | {best} | {pct} | {status} |")

    lines.append("")
    return "\n".join(lines)


# --- Main ---

def main():
    parser = argparse.ArgumentParser(description="autoresearch-agent results viewer")
    parser.add_argument("--experiment", help="Show one experiment: domain/name")
    parser.add_argument("--domain", help="Show all experiments in a domain")
    parser.add_argument("--dashboard", action="store_true", help="Cross-experiment dashboard")
    parser.add_argument("--format", choices=["terminal", "csv", "markdown"], default="terminal",
                        help="Output format (default: terminal)")
    parser.add_argument("--output", "-o", help="Write to file instead of stdout")
    parser.add_argument("--all", action="store_true", help="Show all experiments (alias for --dashboard)")
    args = parser.parse_args()

    root = find_autoresearch_root()
    if root is None:
        print("No .autoresearch/ found. Run setup_experiment.py first.")
        sys.exit(1)

    output_text = None

    # Single experiment
    if args.experiment:
        experiment_dir = root / args.experiment
        if not experiment_dir.exists():
            print(f"Experiment not found: {args.experiment}")
            sys.exit(1)

        if args.format == "csv":
            output_text = export_experiment_csv(experiment_dir, args.experiment)
        elif args.format == "markdown":
            output_text = export_experiment_markdown(experiment_dir, args.experiment)
        else:
            print_experiment(experiment_dir, args.experiment)
            return

    # Domain
    elif args.domain:
        domain_dir = root / args.domain
        if not domain_dir.exists():
            print(f"Domain not found: {args.domain}")
            sys.exit(1)
        for exp_dir in sorted(domain_dir.iterdir()):
            if exp_dir.is_dir() and (exp_dir / "config.cfg").exists():
                if args.format == "terminal":
                    print_experiment(exp_dir, f"{args.domain}/{exp_dir.name}")
                # For CSV/MD, fall through to dashboard with domain filter
        if args.format != "terminal":
            # Use dashboard export filtered to domain
            output_text = export_dashboard_csv(root, domain_filter=args.domain) if args.format == "csv" else export_dashboard_markdown(root, domain_filter=args.domain)
        else:
            return

    # Dashboard
    elif args.dashboard or args.all:
        if args.format == "csv":
            output_text = export_dashboard_csv(root)
        elif args.format == "markdown":
            output_text = export_dashboard_markdown(root)
        else:
            print_dashboard(root)
            return

    else:
        # Default: dashboard
        if args.format == "terminal":
            print_dashboard(root)
            return
        output_text = export_dashboard_csv(root) if args.format == "csv" else export_dashboard_markdown(root)

    # Write output
    if output_text:
        if args.output:
            Path(args.output).write_text(output_text)
            print(f"Written to {args.output}")
        else:
            print(output_text)


if __name__ == "__main__":
    main()
