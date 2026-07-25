#!/usr/bin/env python3
"""kb_ingester.py

Walk a directory of markdown files (Notion export, Confluence space export,
Obsidian vault, Drive/SOPs/ directory) and emit a KB health report.

Extracts:
  - cross-link map (which page references which)
  - orphan pages (no inbound links)
  - glossary candidates (frequently-used proper nouns / acronyms recurring
    in 3+ docs with no single canonical definition page)
  - glossary drift (same term used inconsistently across docs)
  - stale pages (no edit in > N months — N defaults to 12)
  - missing-owner pages (no `owner:` in YAML frontmatter)
  - prioritized cleanup list ranked by (staleness × inbound-link-count)

Stdlib only.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path


YAML_FRONTMATTER_RE = re.compile(
    r"^---\s*\n(.*?)\n---\s*\n", re.DOTALL)
MD_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
WIKI_LINK_RE = re.compile(r"\[\[([^\]|]+)(?:\|[^\]]+)?\]\]")
ACRONYM_RE = re.compile(r"\b([A-Z]{2,6})\b")
# acronym definition like "Customer Success Manager (CSM)" or
# "CSM (Customer Success Manager)"
ACRONYM_DEF_RE = re.compile(
    r"\b((?:[A-Z][A-Za-z]+\s+){1,4}[A-Z][A-Za-z]+)\s*\(([A-Z]{2,6})\)"
    r"|\b([A-Z]{2,6})\s*\(((?:[A-Z][A-Za-z]+\s+){1,4}[A-Z][A-Za-z]+)\)"
)


@dataclass
class PageInfo:
    path: Path
    title: str = ""
    owner: str = ""
    last_reviewed: str = ""
    mtime_days_ago: int = 0
    outbound_links: list = field(default_factory=list)
    inbound_link_count: int = 0
    acronyms_used: list = field(default_factory=list)
    acronym_definitions: dict = field(default_factory=dict)
    word_count: int = 0


def _parse_frontmatter(text: str) -> dict:
    m = YAML_FRONTMATTER_RE.match(text)
    if not m:
        return {}
    body = m.group(1)
    fm = {}
    for line in body.splitlines():
        if ":" in line:
            k, _, v = line.partition(":")
            fm[k.strip().lower()] = v.strip().strip('"').strip("'")
    return fm


def _extract_title(text: str, path: Path) -> str:
    for line in text.splitlines():
        m = re.match(r"^#\s+(.+)$", line)
        if m:
            return m.group(1).strip()
    return path.stem.replace("-", " ").replace("_", " ").title()


def _extract_links(text: str) -> list:
    links = []
    for m in MD_LINK_RE.finditer(text):
        target = m.group(2).strip()
        if target.startswith(("http://", "https://", "mailto:")):
            continue
        links.append(target)
    for m in WIKI_LINK_RE.finditer(text):
        links.append(m.group(1).strip())
    return links


def _extract_acronyms(text: str) -> tuple:
    acronyms = ACRONYM_RE.findall(text)
    defs = {}
    for m in ACRONYM_DEF_RE.finditer(text):
        if m.group(1) and m.group(2):
            defs[m.group(2)] = m.group(1).strip()
        elif m.group(3) and m.group(4):
            defs[m.group(3)] = m.group(4).strip()
    return acronyms, defs


def _normalize_link_target(target: str, source: Path, root: Path) -> str:
    """Resolve a link target to a canonical relative path string."""
    target = target.split("#")[0].split("?")[0].strip()
    if not target:
        return ""
    if target.endswith(".md"):
        candidate = (source.parent / target).resolve()
    elif "/" in target or "\\" in target:
        candidate_md = (source.parent / (target + ".md")).resolve()
        if candidate_md.exists():
            candidate = candidate_md
        else:
            candidate = (source.parent / target).resolve()
    else:
        # bare title — try to match against any .md filename
        candidate_md = (source.parent / (target + ".md")).resolve()
        candidate = candidate_md
    try:
        return str(candidate.relative_to(root))
    except ValueError:
        return str(candidate)


def walk_vault(root: Path, stale_days: int = 365) -> list:
    """Walk a directory tree and return a list of PageInfo objects."""
    pages = []
    now = dt.datetime.now()
    for path in sorted(root.rglob("*.md")):
        if not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        fm = _parse_frontmatter(text)
        title = fm.get("title") or _extract_title(text, path)
        owner = fm.get("owner", "")
        last_reviewed = fm.get("last_reviewed", "") or fm.get(
            "last-reviewed", "")
        # mtime fallback
        try:
            mtime = dt.datetime.fromtimestamp(path.stat().st_mtime)
            mtime_days_ago = (now - mtime).days
        except OSError:
            mtime_days_ago = 0
        outbound = _extract_links(text)
        acronyms, defs = _extract_acronyms(text)
        word_count = len(text.split())
        pages.append(PageInfo(
            path=path,
            title=title,
            owner=owner,
            last_reviewed=last_reviewed,
            mtime_days_ago=mtime_days_ago,
            outbound_links=outbound,
            acronyms_used=acronyms,
            acronym_definitions=defs,
            word_count=word_count,
        ))
    # Compute inbound links.
    by_relpath = {str(p.path.relative_to(root)): p for p in pages}
    by_title = {p.title.lower(): p for p in pages}
    by_stem = {p.path.stem.lower(): p for p in pages}
    for src in pages:
        for raw in src.outbound_links:
            target_rel = _normalize_link_target(raw, src.path, root)
            if target_rel in by_relpath:
                by_relpath[target_rel].inbound_link_count += 1
                continue
            tgt = raw.split("#")[0].split("?")[0].strip().lower()
            if tgt.endswith(".md"):
                tgt = tgt[:-3]
            if tgt in by_title:
                by_title[tgt].inbound_link_count += 1
            elif tgt in by_stem:
                by_stem[tgt].inbound_link_count += 1
    return pages


def detect_orphans(pages: list) -> list:
    return [p for p in pages if p.inbound_link_count == 0]


def detect_stale(pages: list, stale_days: int) -> list:
    out = []
    for p in pages:
        is_stale = False
        if p.last_reviewed:
            try:
                lr = dt.datetime.strptime(p.last_reviewed[:10], "%Y-%m-%d")
                if (dt.datetime.now() - lr).days > stale_days:
                    is_stale = True
            except ValueError:
                pass
        elif p.mtime_days_ago > stale_days:
            is_stale = True
        if is_stale:
            out.append(p)
    return out


def detect_missing_owner(pages: list) -> list:
    return [p for p in pages if not p.owner]


def detect_glossary_drift(pages: list) -> dict:
    """Return a dict {acronym: [list of (definition, source page)]} for
    acronyms that have >= 2 distinct definitions across the vault."""
    by_acronym = defaultdict(list)
    for p in pages:
        for ac, defin in p.acronym_definitions.items():
            by_acronym[ac].append((defin, str(p.path)))
    drift = {}
    for ac, defs in by_acronym.items():
        distinct = set(d.lower() for d, _ in defs)
        if len(distinct) >= 2:
            drift[ac] = defs
    return drift


def detect_glossary_candidates(pages: list, min_docs: int = 3) -> list:
    """Acronyms used in >= min_docs pages with no canonical definition
    page (no page where the acronym appears in the title)."""
    doc_count = Counter()
    titled = set()
    for p in pages:
        seen = set(p.acronyms_used)
        for ac in seen:
            doc_count[ac] += 1
        for ac in p.acronym_definitions:
            # If acronym appears in title, treat as canonical-ish.
            if ac in p.title:
                titled.add(ac)
    return sorted([(ac, c) for ac, c in doc_count.items()
                   if c >= min_docs and ac not in titled],
                  key=lambda x: -x[1])


def cleanup_priority(pages: list, stale_days: int) -> list:
    """Rank pages by (staleness × inbound-link-count) — high-traffic
    stale docs surface first."""
    scored = []
    for p in pages:
        staleness = 0
        if p.last_reviewed:
            try:
                lr = dt.datetime.strptime(p.last_reviewed[:10], "%Y-%m-%d")
                staleness = max(0, (dt.datetime.now() - lr).days
                                - stale_days)
            except ValueError:
                staleness = max(0, p.mtime_days_ago - stale_days)
        else:
            staleness = max(0, p.mtime_days_ago - stale_days)
        if staleness > 0:
            # inbound +1 to avoid zeroing out everything orphan
            score = staleness * (p.inbound_link_count + 1)
            scored.append((score, p))
    scored.sort(key=lambda x: -x[0])
    return scored


def generate_report(root: Path, pages: list, stale_days: int) -> str:
    orphans = detect_orphans(pages)
    stale = detect_stale(pages, stale_days)
    missing_owner = detect_missing_owner(pages)
    drift = detect_glossary_drift(pages)
    candidates = detect_glossary_candidates(pages)
    priority = cleanup_priority(pages, stale_days)

    lines = [
        f"# KB health report — `{root}`",
        "",
        f"**Pages scanned:** {len(pages)}",
        f"**Stale threshold:** {stale_days} days",
        "",
        "## Summary metrics",
        "",
        "| Metric | Count | % of vault |",
        "|--------|-------|------------|",
        f"| Orphan pages (no inbound links) | {len(orphans)} | "
        f"{round(len(orphans) / max(len(pages), 1) * 100, 1)}% |",
        f"| Stale pages (> {stale_days}d) | {len(stale)} | "
        f"{round(len(stale) / max(len(pages), 1) * 100, 1)}% |",
        f"| Missing-owner pages | {len(missing_owner)} | "
        f"{round(len(missing_owner) / max(len(pages), 1) * 100, 1)}% |",
        f"| Glossary drift (acronyms with >= 2 defs) | {len(drift)} | — |",
        f"| Glossary candidates (acronyms in 3+ docs, no canonical page) "
        f"| {len(candidates)} | — |",
        "",
    ]

    lines.append("## Top-20 cleanup priority "
                 "(staleness × inbound-link-count + 1)")
    lines.append("")
    if priority:
        lines.append("| Rank | Score | Path | Inbound | "
                     "Days stale | Owner |")
        lines.append("|------|-------|------|---------|"
                     "------------|-------|")
        for i, (score, p) in enumerate(priority[:20], start=1):
            rel = p.path.relative_to(root)
            staleness = (p.mtime_days_ago - stale_days
                         if not p.last_reviewed else
                         (dt.datetime.now() - dt.datetime.strptime(
                             p.last_reviewed[:10], "%Y-%m-%d")).days
                         - stale_days)
            lines.append(
                f"| {i} | {score} | `{rel}` | {p.inbound_link_count} "
                f"| {staleness} | {p.owner or '(MISSING)'} |"
            )
    else:
        lines.append("_(no stale pages — KB is current)_")
    lines.append("")

    lines.append("## Orphan pages (no inbound links)")
    lines.append("")
    if orphans:
        for p in orphans[:30]:
            rel = p.path.relative_to(root)
            lines.append(f"- `{rel}` — {p.title}")
        if len(orphans) > 30:
            lines.append(f"- _(+{len(orphans) - 30} more not shown)_")
    else:
        lines.append("_(none — every page has at least one inbound link)_")
    lines.append("")

    lines.append("## Glossary drift (acronym defined differently across "
                 "docs)")
    lines.append("")
    if drift:
        for ac, defs in drift.items():
            lines.append(f"**{ac}:**")
            for defin, src in defs:
                lines.append(f"  - `{defin}` (in `{src}`)")
            lines.append("")
    else:
        lines.append("_(none detected — acronyms are used consistently)_")
    lines.append("")

    lines.append("## Glossary candidates (acronym used in 3+ docs "
                 "without a canonical definition page)")
    lines.append("")
    if candidates:
        for ac, count in candidates[:20]:
            lines.append(f"- **{ac}** — used in {count} docs, no "
                         f"canonical definition page exists")
    else:
        lines.append("_(none — acronyms either have canonical pages or "
                     "are uncommon)_")
    lines.append("")

    lines.append("## Missing-owner pages")
    lines.append("")
    if missing_owner:
        for p in missing_owner[:30]:
            rel = p.path.relative_to(root)
            lines.append(f"- `{rel}` — {p.title}")
        if len(missing_owner) > 30:
            lines.append(
                f"- _(+{len(missing_owner) - 30} more not shown)_")
    else:
        lines.append("_(none — every page has an owner)_")
    lines.append("")

    lines.append("## Recommended next actions")
    lines.append("")
    lines.append("1. Assign owners to the missing-owner pages first — "
                 "no other fix sticks without ownership.")
    lines.append("2. Resolve glossary drift by picking one canonical "
                 "definition per acronym; add a `glossary.md` page; "
                 "link every other doc to it.")
    lines.append("3. Triage the top-20 cleanup list: archive, rewrite, "
                 "or refresh. Re-run this report after the sprint to "
                 "verify orphan + stale counts are down.")
    lines.append("4. Pair orphan pages with a navigation review — some "
                 "orphans are reference pages found via search and "
                 "should NOT be archived. Curate, don't bulk-delete.")
    return "\n".join(lines) + "\n"


def generate_json_report(root: Path, pages: list, stale_days: int) -> dict:
    orphans = detect_orphans(pages)
    stale = detect_stale(pages, stale_days)
    missing_owner = detect_missing_owner(pages)
    drift = detect_glossary_drift(pages)
    candidates = detect_glossary_candidates(pages)
    priority = cleanup_priority(pages, stale_days)
    return {
        "root": str(root),
        "page_count": len(pages),
        "stale_days_threshold": stale_days,
        "orphan_count": len(orphans),
        "stale_count": len(stale),
        "missing_owner_count": len(missing_owner),
        "glossary_drift_count": len(drift),
        "glossary_candidate_count": len(candidates),
        "top_cleanup": [
            {
                "rank": i + 1,
                "score": score,
                "path": str(p.path.relative_to(root)),
                "inbound_links": p.inbound_link_count,
                "owner": p.owner or None,
            }
            for i, (score, p) in enumerate(priority[:20])
        ],
        "orphans": [str(p.path.relative_to(root)) for p in orphans],
        "glossary_drift": {ac: [{"definition": d, "source": s}
                                for d, s in defs]
                           for ac, defs in drift.items()},
        "glossary_candidates": [{"acronym": ac, "doc_count": c}
                                for ac, c in candidates],
        "missing_owner": [str(p.path.relative_to(root))
                          for p in missing_owner],
    }


SAMPLE_PAGES = {
    "index.md": """---
owner: alex@company.com
last_reviewed: 2026-04-01
---
# Ops Index

Welcome to the Ops wiki. Start with [Vendor Offboarding](sops/vendor-offboarding.md) or [Incident Comms](runbooks/incident-comms.md).
The [Glossary](glossary.md) defines our terms.
""",
    "glossary.md": """---
owner: alex@company.com
last_reviewed: 2026-04-15
---
# Glossary

- Customer Success Manager (CSM) — owns post-sale account relationship.
- Vendor Management Office (VMO) — owns third-party vendor lifecycle.
""",
    "sops/vendor-offboarding.md": """---
owner: jordan@company.com
last_reviewed: 2026-02-01
---
# Vendor Offboarding SOP

The VMO operator runs this SOP when a vendor contract is terminated.
See also [Incident Comms](../runbooks/incident-comms.md).
The CSM is notified.
""",
    "sops/procurement-intake.md": """---
owner: jordan@company.com
last_reviewed: 2024-01-01
---
# Procurement Intake SOP

Run this when finance receives a purchase request. The CSM (Customer Solutions Manager) reviews it.
""",  # NOTE: glossary drift — CSM here is Customer Solutions Manager
    "runbooks/incident-comms.md": """---
last_reviewed: 2026-03-01
---
# Incident Comms Cascade

(no owner field — missing-owner case)
Send alerts to the on-call SRE.
""",
    "orphan-page.md": """---
owner: pat@company.com
last_reviewed: 2026-04-01
---
# Orphan Page

Nobody links here.
The CSM may find this useful.
""",
    "old-stale-page.md": """# Old Page

(no frontmatter at all — missing-owner AND probably stale via mtime)
""",
    "sops/employee-onboarding.md": """---
owner: hr@company.com
last_reviewed: 2026-04-20
---
# Employee Onboarding SOP

Coordinate with the CSM and VMO for system access.
Link: [Vendor Offboarding](vendor-offboarding.md).
""",
}


def _materialize_sample_vault() -> Path:
    tmp = Path(tempfile.mkdtemp(prefix="kb-sample-"))
    for relpath, content in SAMPLE_PAGES.items():
        full = tmp / relpath
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text(content, encoding="utf-8")
    # Backdate one file via os.utime so mtime-based stale detection
    # has something to find.
    import os
    old = tmp / "old-stale-page.md"
    if old.exists():
        old_ts = (dt.datetime.now() -
                  dt.timedelta(days=720)).timestamp()
        os.utime(old, (old_ts, old_ts))
    return tmp


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Walk a markdown KB and emit a hygiene report: "
                    "orphans, stale, missing-owner, glossary drift."
    )
    p.add_argument("--input", "-i", type=str,
                   help="Path to KB root directory.")
    p.add_argument("--output", "-o", choices=["markdown", "json"],
                   default="markdown",
                   help="Output format (default: markdown).")
    p.add_argument("--stale-days", type=int, default=365,
                   help="Days since last edit to consider stale "
                        "(default: 365).")
    p.add_argument("--sample", action="store_true",
                   help="Run against a tiny synthetic vault in a "
                        "tmpdir.")
    args = p.parse_args(argv)

    if args.sample:
        root = _materialize_sample_vault()
    elif args.input:
        root = Path(args.input).resolve()
        if not root.exists() or not root.is_dir():
            print(f"ERROR: input directory not found: {args.input}",
                  file=sys.stderr)
            return 2
    else:
        print("ERROR: provide --input <kb-root-dir> or --sample",
              file=sys.stderr)
        return 2

    pages = walk_vault(root, stale_days=args.stale_days)
    if not pages:
        print(f"WARNING: no markdown files found under {root}",
              file=sys.stderr)
        return 1

    if args.output == "json":
        print(json.dumps(generate_json_report(root, pages, args.stale_days),
                         indent=2))
    else:
        print(generate_report(root, pages, args.stale_days))
    return 0


if __name__ == "__main__":
    sys.exit(main())
