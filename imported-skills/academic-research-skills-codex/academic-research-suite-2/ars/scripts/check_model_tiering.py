#!/usr/bin/env python3
"""Model-tiering classification drift guard (#517).

The tiering mechanism (shared/model_tiering.md) is prose + manifest: agent files are
never edited, so the only thing that can rot is the CLASSIFICATION — an agent added
without a tier, a manifest entry pointing at a deleted file, or the canonical table
and the manifest silently disagreeing. This lint pins all three:

  1. SET EQUALITY — the ``*_agent.md`` files on disk (five skill agent dirs; the
     top-level ``agents/`` plugin mirror is excluded, it is byte-pinned separately
     by check_agents_mirror_sync.py) exactly match the manifest's ``path`` set.
     A new agent without a tier assignment fails CI here. A repo-wide sweep also
     rejects any ``*_agent.md`` OUTSIDE the known roster dirs (a new skill
     directory cannot smuggle unclassified agents past the fixed dir list).
  2. TIER ENUM — every manifest ``tier`` is ``judgment`` or ``execution``.
  3. DOC SYNC — shared/model_tiering.md's classification table carries EXACTLY the
     manifest's short-name set per (tier, skill) row: a missing token, an extra or
     duplicate token, a wrong per-row ``(N)`` count, a duplicate skill row, or a
     headline-count mismatch each fail.

Exit codes: 0 = pass; 1 = drift found.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANIFEST = REPO / "scripts" / "model_tiering_manifest.json"
DOC = REPO / "shared" / "model_tiering.md"

# The five skill agent dirs in scope. The top-level plugin mirror dir `agents/` is
# deliberately NOT listed (byte-copies, guarded by check_agents_mirror_sync.py).
AGENT_DIRS = [
    "deep-research/agents",
    "academic-paper/agents",
    "academic-paper-reviewer/agents",
    "academic-pipeline/agents",
    "shared/agents",
]

VALID_TIERS = {"judgment", "execution"}

JUDGMENT_HEADING = re.compile(r"^### Judgment-type \((\d+)\)", re.M)
EXECUTION_HEADING = re.compile(r"^### Execution-type \((\d+)\)", re.M)


def disk_agent_paths() -> set[str]:
    found: set[str] = set()
    for d in AGENT_DIRS:
        base = REPO / d
        if not base.is_dir():
            continue
        for f in sorted(base.glob("*_agent.md")):
            found.add(f.relative_to(REPO).as_posix())
    return found


# Paths outside the roster where *_agent.md files are legitimate and out of scope:
# the top-level plugin mirror (byte-pinned by check_agents_mirror_sync.py) and
# design/docs material that may quote agent filenames as examples.
OUT_OF_SCOPE_PREFIXES = (
    "agents/",
    "experiment-agent/",
    "docs/",
    "tests/",
    "audits/",
    "evals/",
    ".git/",
)


def out_of_roster_agents() -> list[str]:
    """Repo-wide sweep: *_agent.md files in an agents/ dir NOT covered by AGENT_DIRS."""
    strays: list[str] = []
    for f in sorted(REPO.rglob("*_agent.md")):
        rel = f.relative_to(REPO).as_posix()
        if rel.startswith(OUT_OF_SCOPE_PREFIXES):
            continue
        if not any(rel.startswith(d + "/") for d in AGENT_DIRS):
            strays.append(rel)
    return strays


def load_manifest() -> list[dict]:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    agents = data.get("agents")
    if not isinstance(agents, list) or not agents:
        raise ValueError("manifest 'agents' must be a non-empty list")
    return agents


def short_name(path: str) -> str:
    return Path(path).name.removesuffix("_agent.md")


def skill_of(path: str) -> str:
    # 'shared/agents/x.md' -> 'shared'; 'deep-research/agents/x.md' -> 'deep-research'
    return path.split("/", 1)[0]


def doc_sections(text: str) -> tuple[str, int, str, int]:
    jm = JUDGMENT_HEADING.search(text)
    em = EXECUTION_HEADING.search(text)
    if not jm or not em:
        raise ValueError("canonical doc is missing a '### Judgment-type (N)' or '### Execution-type (N)' heading")
    if em.start() < jm.start():
        raise ValueError("canonical doc tier sections are out of the expected order (Judgment before Execution)")
    judgment_body = text[jm.end() : em.start()]
    execution_body = text[em.end() :]
    return judgment_body, int(jm.group(1)), execution_body, int(em.group(1))


ROW_RE = re.compile(r"^\|\s*([a-z-]+(?:-[a-z]+)*) \((\d+)\)\s*\|(.*)\|\s*$")
TOKEN_RE = re.compile(r"`([^`]+)`")


def section_rows(section: str) -> tuple[dict[str, tuple[int, list[str]]], list[str]]:
    """Parse a tier section's table rows into {skill: (declared_count, tokens)}.

    Returns (rows, errors). A duplicate skill row is an error — a contradictory
    second row must never be silently shadowed by first-match-wins.
    """
    rows: dict[str, tuple[int, list[str]]] = {}
    errors: list[str] = []
    for line in section.splitlines():
        m = ROW_RE.match(line)
        if not m:
            continue
        skill, count, body = m.group(1), int(m.group(2)), m.group(3)
        if skill == "Skill":  # header guard (never matches the regex, kept for clarity)
            continue
        if skill in rows:
            errors.append(f"duplicate '{skill}' row in one tier section — contradictory rows are ambiguous")
            continue
        rows[skill] = (count, TOKEN_RE.findall(body))
    return rows, errors


def main() -> int:
    errors: list[str] = []

    try:
        agents = load_manifest()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"[model-tiering] FAIL: cannot load manifest: {exc}")
        return 1

    manifest_paths = [a.get("path", "") for a in agents]
    manifest_set = set(manifest_paths)
    if len(manifest_set) != len(manifest_paths):
        dupes = sorted({p for p in manifest_paths if manifest_paths.count(p) > 1})
        errors.append(f"manifest contains duplicate path(s): {dupes}")

    # 1. set equality with disk + repo-wide stray sweep
    disk = disk_agent_paths()
    missing_from_manifest = sorted(disk - manifest_set)
    missing_from_disk = sorted(manifest_set - disk)
    for p in missing_from_manifest:
        errors.append(f"agent file on disk has NO tier classification: {p} (add it to scripts/model_tiering_manifest.json AND shared/model_tiering.md)")
    for p in missing_from_disk:
        errors.append(f"manifest classifies a file that does not exist on disk: {p}")
    for p in out_of_roster_agents():
        errors.append(f"agent file outside the known skill agent dirs: {p} (a new skill directory must be added to AGENT_DIRS in this lint AND its agents classified)")

    # 2. tier enum
    for a in agents:
        if a.get("tier") not in VALID_TIERS:
            errors.append(f"invalid tier {a.get('tier')!r} for {a.get('path')} (must be one of {sorted(VALID_TIERS)})")

    # 3. doc sync
    try:
        text = DOC.read_text(encoding="utf-8")
        judgment_body, judgment_count, execution_body, execution_count = doc_sections(text)
    except (OSError, ValueError) as exc:
        print(f"[model-tiering] FAIL: cannot parse canonical doc: {exc}")
        return 1

    by_tier = {"judgment": [], "execution": []}
    for a in agents:
        if a.get("tier") in by_tier:
            by_tier[a["tier"]].append(a["path"])

    if judgment_count != len(by_tier["judgment"]):
        errors.append(f"doc says Judgment-type ({judgment_count}) but manifest has {len(by_tier['judgment'])}")
    if execution_count != len(by_tier["execution"]):
        errors.append(f"doc says Execution-type ({execution_count}) but manifest has {len(by_tier['execution'])}")

    # Exact per-(tier, skill) token-set equality: missing, extra, and duplicate
    # tokens, wrong per-row (N) counts, and duplicate skill rows all fail.
    doc_map: dict[tuple[str, str], set[str]] = {}
    for tier, body in (("judgment", judgment_body), ("execution", execution_body)):
        rows, row_errors = section_rows(body)
        errors.extend(f"{tier} section: {e}" for e in row_errors)
        for skill, (declared, tokens) in rows.items():
            if len(tokens) != declared:
                errors.append(f"{tier} section '{skill}' row declares ({declared}) but lists {len(tokens)} backticked agent name(s)")
            dupes = sorted({t for t in tokens if tokens.count(t) > 1})
            if dupes:
                errors.append(f"{tier} section '{skill}' row lists duplicate token(s): {dupes}")
            doc_map[(tier, skill)] = set(tokens)

    manifest_map: dict[tuple[str, str], set[str]] = {}
    for tier in VALID_TIERS:
        for path in by_tier[tier]:
            manifest_map.setdefault((tier, skill_of(path)), set()).add(short_name(path))

    doc_rel = DOC.relative_to(REPO)
    for key in sorted(set(doc_map) | set(manifest_map)):
        tier, skill = key
        missing = sorted(manifest_map.get(key, set()) - doc_map.get(key, set()))
        extra = sorted(doc_map.get(key, set()) - manifest_map.get(key, set()))
        if missing:
            errors.append(f"{tier} section '{skill}' row in {doc_rel} is missing manifest agent(s): {missing}")
        if extra:
            errors.append(f"{tier} section '{skill}' row in {doc_rel} lists agent(s) not classified '{tier}' for that skill in the manifest: {extra}")

    if errors:
        print(f"[model-tiering] FAIL ({len(errors)} error(s)):")
        for e in errors:
            print(f"  - {e}")
        return 1

    print(f"[model-tiering] PASS: {len(agents)} agents classified ({len(by_tier['judgment'])} judgment / {len(by_tier['execution'])} execution); disk, manifest, and canonical table agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
