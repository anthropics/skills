#!/usr/bin/env python3
"""Check a figure_storyboard.yaml for multi-figure narrative integrity.

**Optional validation tool** — This script is an optional validation tool in
LLM-as-artist mode. It validates multi-figure storyboards for narrative
completeness, role coverage, acyclic dependencies, and cross-figure consistency.

Validates the storyboard that orchestrates multiple figures within a manuscript:
narrative completeness, role coverage (by manuscript type), acyclic evidence
dependencies, non-placeholder claims, contract evidence-chain linkage,
no-redundancy across figures, and style-consistency declaration.

Usage:
    python scripts/check_storyboard.py figure_storyboard.yaml
    python scripts/check_storyboard.py figure_storyboard.yaml --json

Exit codes: 0 = pass, 1 = warning, 2 = error.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover - environment guard
    yaml = None


# Complete role enum. Must stay in sync with the template comments.
VALID_ROLES = {
    "establish_system",
    "prove_mechanism",
    "show_performance",
    "validate_durability",
    "summarize",
    "compare",
    "method_development",
}

# Tokens that mark a claim as a placeholder (case-insensitive substring match).
PLACEHOLDER_TOKENS = (
    "tbd",
    "todo",
    "placeholder",
    "template-only",
    "template_only",
    "replace this",
    "fill in",
    "lorem ipsum",
)

# Tokens that mark a contract evidence-chain data source as a placeholder, so it
# is skipped by the no-redundancy check (avoids false positives on templates).
SOURCE_PLACEHOLDER_TOKENS = (
    "example",
    "template",
    "placeholder",
    "tbd",
    "n/a",
    "not applicable",
)

# Default validation config, used when the storyboard omits the validation block
# or individual keys. Mirrors the shipped template.
DEFAULT_VALIDATION = {
    "required_roles_research": ["establish_system", "prove_mechanism", "show_performance"],
    "required_roles_review": ["establish_system", "summarize"],
    "required_roles_case_study": ["establish_system", "show_performance"],
    "min_figures": 1,
    "max_figures": 12,
    "allow_cycles": False,
}

REQUIRED_FIGURE_FIELDS = ("figure_id", "figure_name", "role", "claim", "contract_path")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _is_placeholder(text: str) -> bool:
    lowered = text.lower()
    return any(tok in lowered for tok in PLACEHOLDER_TOKENS)


def _extract_section(text: str, heading: str) -> str:
    """Return content between a '## heading' and the next '## ' heading."""
    pattern = rf"## {re.escape(heading)}\s*\n(.*?)(?=\n## |\Z)"
    match = re.search(pattern, text, re.DOTALL)
    return match.group(1) if match else ""


def _parse_evidence_chain_rows(contract_text: str) -> list[list[str]]:
    """Parse the Evidence Chain markdown table into a list of cell rows.

    Skips the header and separator rows. Each row is the list of stripped cell
    values: [Panel, Evidence source, Source anchor, What it supports, Boundary].
    """
    section = _extract_section(contract_text, "Evidence Chain")
    rows: list[list[str]] = []
    for line in section.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.split("|")[1:-1]]
        if len(cells) < 3:
            continue
        first = cells[0].lower()
        # Skip header row and markdown separator row (---, :--, etc.).
        if first in ("panel", ""):
            continue
        if set(cells[0]) <= set("-: "):
            continue
        rows.append(cells)
    return rows


def _detect_cycle(nodes: list[str], edges: dict[str, list[str]]) -> list[str] | None:
    """DFS cycle detection. Returns the cycle path (including the repeated node
    at the end) if a cycle exists, else None."""
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {n: WHITE for n in nodes}
    stack: list[str] = []

    def dfs(u: str) -> list[str] | None:
        color[u] = GRAY
        stack.append(u)
        for v in edges.get(u, []):
            if v not in color:
                continue  # unknown target handled by a separate check
            if color[v] == GRAY:
                idx = stack.index(v)
                return stack[idx:] + [v]
            if color[v] == WHITE:
                found = dfs(v)
                if found:
                    return found
        stack.pop()
        color[u] = BLACK
        return None

    for n in nodes:
        if color[n] == WHITE:
            found = dfs(n)
            if found:
                return found
    return None


# ---------------------------------------------------------------------------
# Checks. Each appends result dicts to `results`.
# ---------------------------------------------------------------------------

def check_narrative_completeness(storyboard: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc")
    if not isinstance(arc, list) or not arc:
        results.append({
            "check": "narrative_completeness",
            "result": "error",
            "message": "narrative_arc is empty or missing",
        })
        return

    missing: list[str] = []
    for fig in arc:
        if not isinstance(fig, dict):
            missing.append("non-mapping figure entry")
            continue
        for field in REQUIRED_FIGURE_FIELDS:
            val = fig.get(field)
            if val is None or (isinstance(val, str) and not val.strip()):
                missing.append(f"{fig.get('figure_id', '?')}.{field}")

    if missing:
        results.append({
            "check": "narrative_completeness",
            "result": "error",
            "message": f"{len(arc)} figures; missing fields: {', '.join(missing)}",
        })
    else:
        results.append({
            "check": "narrative_completeness",
            "result": "pass",
            "message": f"{len(arc)} figures in narrative arc, all required fields present",
        })


def check_figure_count(storyboard: dict, validation: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc") or []
    count = len(arc) if isinstance(arc, list) else 0
    lo = int(validation.get("min_figures", DEFAULT_VALIDATION["min_figures"]))
    hi = int(validation.get("max_figures", DEFAULT_VALIDATION["max_figures"]))
    if count < lo:
        results.append({
            "check": "figure_count",
            "result": "error",
            "message": f"{count} figures below minimum {lo}",
        })
    elif count > hi:
        results.append({
            "check": "figure_count",
            "result": "error",
            "message": f"{count} figures above maximum {hi}",
        })
    else:
        results.append({
            "check": "figure_count",
            "result": "pass",
            "message": f"{count} figures within [{lo}, {hi}]",
        })


def check_role_validity(storyboard: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc") or []
    bad: list[str] = []
    for fig in arc:
        if not isinstance(fig, dict):
            continue
        role = fig.get("role")
        if role not in VALID_ROLES:
            bad.append(f"{fig.get('figure_id', '?')}={role!r}")
    if bad:
        results.append({
            "check": "role_validity",
            "result": "error",
            "message": f"invalid roles: {', '.join(bad)}; allowed: {sorted(VALID_ROLES)}",
        })
    else:
        results.append({
            "check": "role_validity",
            "result": "pass",
            "message": "all roles are valid",
        })


def check_role_coverage(storyboard: dict, validation: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc") or []
    present = {fig.get("role") for fig in arc if isinstance(fig, dict)}
    mtype = storyboard.get("manuscript_type", "research")
    key = {
        "research": "required_roles_research",
        "review": "required_roles_review",
        "case-study": "required_roles_case_study",
    }.get(mtype, "required_roles_research")
    required = validation.get(key, DEFAULT_VALIDATION[key])
    missing = [r for r in required if r not in present]
    if missing:
        results.append({
            "check": "role_coverage",
            "result": "warning",
            "message": f"{mtype} manuscript missing required roles: {', '.join(missing)}",
        })
    else:
        results.append({
            "check": "role_coverage",
            "result": "pass",
            "message": f"{mtype} manuscript covers required roles: {', '.join(required)}",
        })


def check_dependency_targets(storyboard: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc") or []
    ids = {fig.get("figure_id") for fig in arc if isinstance(fig, dict)}
    bad: list[str] = []
    for fig in arc:
        if not isinstance(fig, dict):
            continue
        deps = fig.get("evidence_depends_on") or []
        if not isinstance(deps, list):
            bad.append(f"{fig.get('figure_id', '?')}.evidence_depends_on not a list")
            continue
        for dep in deps:
            if dep not in ids:
                bad.append(f"{fig.get('figure_id', '?')} -> {dep} (target not in arc)")
    if bad:
        results.append({
            "check": "dependency_targets_exist",
            "result": "error",
            "message": "; ".join(bad),
        })
    else:
        results.append({
            "check": "dependency_targets_exist",
            "result": "pass",
            "message": "all evidence_depends_on targets exist in narrative_arc",
        })


def check_acyclic(storyboard: dict, validation: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc") or []
    nodes = [fig.get("figure_id") for fig in arc if isinstance(fig, dict)]
    edges: dict[str, list[str]] = {}
    for fig in arc:
        if not isinstance(fig, dict):
            continue
        fid = fig.get("figure_id")
        deps = fig.get("evidence_depends_on") or []
        edges[fid] = [d for d in deps if d in nodes]
    cycle = _detect_cycle(nodes, edges)
    allow_cycles = bool(validation.get("allow_cycles", DEFAULT_VALIDATION["allow_cycles"]))
    if cycle:
        path = " -> ".join(cycle)
        severity = "warning" if allow_cycles else "error"
        results.append({
            "check": "acyclic_dependency",
            "result": severity,
            "message": f"cycle detected: {path}",
        })
    else:
        results.append({
            "check": "acyclic_dependency",
            "result": "pass",
            "message": "evidence dependencies form a DAG",
        })


def check_claims_nonempty(storyboard: dict, results: list[dict]) -> None:
    arc = storyboard.get("narrative_arc") or []
    problems: list[str] = []
    for fig in arc:
        if not isinstance(fig, dict):
            continue
        fid = fig.get("figure_id", "?")
        claim = fig.get("claim") or ""
        claim = claim.strip() if isinstance(claim, str) else ""
        if not claim:
            problems.append(f"{fid} claim is empty")
        elif _is_placeholder(claim):
            problems.append(f"{fid} claim is placeholder: {claim!r}")
    if problems:
        # Empty claim is an error; placeholder is a warning. Report worst.
        empty = [p for p in problems if "is empty" in p]
        if empty:
            results.append({
                "check": "claim_nonempty",
                "result": "error",
                "message": "; ".join(problems),
            })
        else:
            results.append({
                "check": "claim_nonempty",
                "result": "warning",
                "message": "; ".join(problems),
            })
    else:
        results.append({
            "check": "claim_nonempty",
            "result": "pass",
            "message": "all figure claims are non-empty and non-placeholder",
        })


def check_contract_evidence_linkage(
    storyboard: dict, base_dir: Path, results: list[dict]
) -> None:
    """For each figure with an existing contract, verify its evidence chain
    references the figure_ids/figure_names it depends on."""
    arc = storyboard.get("narrative_arc") or []
    by_id = {fig.get("figure_id"): fig for fig in arc if isinstance(fig, dict)}
    checked = 0
    gaps: list[str] = []
    for fig in arc:
        if not isinstance(fig, dict):
            continue
        contract_path = fig.get("contract_path")
        if not contract_path:
            continue
        resolved = (base_dir / contract_path).resolve()
        if not resolved.is_file():
            continue  # contract not present yet; skip (not an error here)
        checked += 1
        text = resolved.read_text(encoding="utf-8", errors="replace")
        deps = fig.get("evidence_depends_on") or []
        for dep in deps:
            dep_fig = by_id.get(dep, {})
            dep_name = dep_fig.get("figure_name", "")
            # Reference is satisfied if the contract mentions the dep figure_id
            # or its figure_name anywhere in the text.
            if dep in text or (dep_name and dep_name in text):
                continue
            gaps.append(f"{fig.get('figure_id', '?')} contract does not reference dependency {dep}")
    if not checked:
        results.append({
            "check": "contract_evidence_linkage",
            "result": "pass",
            "message": "no contract files present yet; linkage skipped",
        })
    elif gaps:
        results.append({
            "check": "contract_evidence_linkage",
            "result": "warning",
            "message": "; ".join(gaps),
        })
    else:
        results.append({
            "check": "contract_evidence_linkage",
            "result": "pass",
            "message": f"{checked} contract(s) reference their declared dependencies",
        })


def check_no_redundancy(storyboard: dict, base_dir: Path, results: list[dict]) -> None:
    """Cross-figure panel data-source redundancy check.

    Extracts (evidence source, source anchor) fingerprints from each existing
    contract's Evidence Chain table, skips placeholder anchors, and flags any
    fingerprint appearing in two or more figures.
    """
    arc = storyboard.get("narrative_arc") or []
    # Map fingerprint -> list of figure_ids that use it.
    seen: dict[str, list[str]] = {}
    checked = 0
    for fig in arc:
        if not isinstance(fig, dict):
            continue
        contract_path = fig.get("contract_path")
        if not contract_path:
            continue
        resolved = (base_dir / contract_path).resolve()
        if not resolved.is_file():
            continue
        checked += 1
        text = resolved.read_text(encoding="utf-8", errors="replace")
        rows = _parse_evidence_chain_rows(text)
        fid = fig.get("figure_id", "?")
        for cells in rows:
            # cells: [Panel, Evidence source, Source anchor, ...]
            evidence_source = cells[1] if len(cells) > 1 else ""
            source_anchor = cells[2] if len(cells) > 2 else ""
            combined = f"{evidence_source} | {source_anchor}".strip(" |")
            if not combined:
                continue
            if _is_source_placeholder(evidence_source, source_anchor):
                continue
            seen.setdefault(combined, []).append(fid)

    duplicates = {fp: fids for fp, fids in seen.items() if len(set(fids)) > 1}
    if not checked:
        results.append({
            "check": "no_redundancy",
            "result": "pass",
            "message": "no contract files present yet; redundancy check skipped",
        })
    elif duplicates:
        details = "; ".join(
            f"{fp} in {sorted(set(fids))}" for fp, fids in duplicates.items()
        )
        results.append({
            "check": "no_redundancy",
            "result": "warning",
            "message": f"shared data sources across figures: {details}",
        })
    else:
        results.append({
            "check": "no_redundancy",
            "result": "pass",
            "message": f"{checked} contract(s) checked; no duplicated panel data sources",
        })


def _is_source_placeholder(evidence_source: str, source_anchor: str) -> bool:
    blob = f"{evidence_source} {source_anchor}".lower()
    return any(tok in blob for tok in SOURCE_PLACEHOLDER_TOKENS)


def check_style_consistency(storyboard: dict, results: list[dict]) -> None:
    """Simplified check: verify a style_consistency constraint is declared and
    names a shared_palette."""
    constraints = storyboard.get("cross_figure_constraints") or []
    style = next(
        (c for c in constraints if isinstance(c, dict) and c.get("type") == "style_consistency"),
        None,
    )
    if style is None:
        results.append({
            "check": "style_consistency",
            "result": "warning",
            "message": "no style_consistency constraint declared",
        })
        return
    palette = style.get("shared_palette")
    if not palette:
        results.append({
            "check": "style_consistency",
            "result": "warning",
            "message": "style_consistency declared without shared_palette",
        })
    else:
        results.append({
            "check": "style_consistency",
            "result": "pass",
            "message": f"style_consistency declared with shared_palette={palette!r}",
        })


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------

def run_checks(storyboard: dict, base_dir: Path) -> list[dict]:
    results: list[dict] = []
    validation = storyboard.get("validation") or {}

    check_narrative_completeness(storyboard, results)
    check_figure_count(storyboard, validation, results)
    check_role_validity(storyboard, results)
    check_role_coverage(storyboard, validation, results)
    check_dependency_targets(storyboard, results)
    check_acyclic(storyboard, validation, results)
    check_claims_nonempty(storyboard, results)
    check_contract_evidence_linkage(storyboard, base_dir, results)
    check_no_redundancy(storyboard, base_dir, results)
    check_style_consistency(storyboard, results)
    return results


def aggregate_status(results: list[dict]) -> str:
    if any(r["result"] == "error" for r in results):
        return "error"
    if any(r["result"] == "warning" for r in results):
        return "warning"
    return "pass"


def exit_code_for(status: str) -> int:
    return {"pass": 0, "warning": 1, "error": 2}[status]


def load_storyboard(path: Path) -> tuple[dict | None, str | None]:
    if yaml is None:
        return None, "PyYAML is required: pip install pyyaml"
    if not path.is_file():
        return None, f"storyboard not found: {path}"
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as exc:
        return None, f"YAML parse error: {exc}"
    if not isinstance(data, dict):
        return None, "storyboard root must be a mapping"
    return data, None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("storyboard", help="path to figure_storyboard.yaml")
    parser.add_argument("--json", action="store_true", help="emit JSON result")
    args = parser.parse_args(argv)

    path = Path(args.storyboard).resolve()
    storyboard, err = load_storyboard(path)
    if err is not None:
        report = {"status": "error", "checks": [{"check": "load", "result": "error", "message": err}]}
        if args.json:
            print(json.dumps(report, ensure_ascii=False, indent=2))
        else:
            print(f"ERROR: {err}", file=sys.stderr)
        return 2

    base_dir = path.parent
    results = run_checks(storyboard, base_dir)
    status = aggregate_status(results)
    report = {"status": status, "checks": results}

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(f"STATUS: {status.upper()}")
        for r in results:
            print(f"  [{r['result'].upper():7}] {r['check']}: {r['message']}")
    return exit_code_for(status)


if __name__ == "__main__":
    raise SystemExit(main())
