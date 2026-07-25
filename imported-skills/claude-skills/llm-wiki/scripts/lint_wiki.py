#!/usr/bin/env python3
"""
lint_wiki.py — Health-check an LLM Wiki vault.

Surfaces structural problems the LLM-as-wiki-maintainer should fix:

  - orphans:        pages with zero inbound [[wikilinks]]
  - broken_links:   [[wikilinks]] pointing to non-existent pages
  - stale:          pages whose `updated:` frontmatter is older than --stale-days
  - missing_fm:     pages without a title/category/summary in frontmatter
  - duplicate_titles: two or more pages sharing the same title
  - log_gaps:       no log entry in the last --log-gap-days

Usage:
    python lint_wiki.py --vault ~/vaults/research
    python lint_wiki.py --vault . --stale-days 60 --json
"""
from __future__ import annotations
import argparse
import datetime as dt
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

FRONTMATTER_RE = re.compile(r"^---\s*\n(.*?)\n---\s*\n", re.DOTALL)
WIKILINK_RE = re.compile(r"\[\[([^\]|#]+)(?:#[^\]|]*)?(?:\|[^\]]*)?\]\]")
LOG_ENTRY_RE = re.compile(r"^## \[(\d{4}-\d{2}-\d{2})\]", re.MULTILINE)


def parse_frontmatter(text: str) -> dict[str, str]:
    m = FRONTMATTER_RE.match(text)
    if not m:
        return {}
    fm: dict[str, str] = {}
    for line in m.group(1).splitlines():
        if ":" in line and not line.lstrip().startswith("#"):
            k, _, v = line.partition(":")
            fm[k.strip()] = v.strip().strip("'\"")
    return fm


def scan(vault: Path, stale_days: int, log_gap_days: int) -> dict:
    wiki = vault / "wiki"
    if not wiki.exists():
        raise SystemExit(f"[error] {wiki} not found")

    pages: dict[str, dict] = {}
    inbound: dict[str, set[str]] = defaultdict(set)
    outbound: dict[str, set[str]] = defaultdict(set)

    for md in wiki.rglob("*.md"):
        rel = md.relative_to(wiki)
        if rel.name in {"index.md", "log.md"}:
            continue
        if any(part.startswith(".") for part in rel.parts):
            continue
        key = str(rel).replace("\\", "/")[:-3]  # strip .md
        text = md.read_text(encoding="utf-8", errors="replace")
        fm = parse_frontmatter(text)
        pages[key] = {"path": key + ".md", "fm": fm, "text": text}

    # Build link graph
    stems = {Path(k).name: k for k in pages}
    for key, page in pages.items():
        for m in WIKILINK_RE.finditer(page["text"]):
            target = m.group(1).strip()
            # Normalize: strip .md, try full path match first, then stem
            if target.endswith(".md"):
                target = target[:-3]
            if target in pages:
                outbound[key].add(target)
                inbound[target].add(key)
            elif Path(target).name in stems:
                resolved = stems[Path(target).name]
                outbound[key].add(resolved)
                inbound[resolved].add(key)
            else:
                outbound[key].add(f"__BROKEN__:{target}")

    today = dt.date.today()
    stale_cutoff = today - dt.timedelta(days=stale_days)

    orphans = sorted(k for k in pages if not inbound.get(k))
    broken_links: list[tuple[str, str]] = []
    for src, targets in outbound.items():
        for t in targets:
            if t.startswith("__BROKEN__:"):
                broken_links.append((src, t.split(":", 1)[1]))
    broken_links.sort()

    stale: list[tuple[str, str]] = []
    missing_fm: list[str] = []
    titles: dict[str, list[str]] = defaultdict(list)
    for key, page in pages.items():
        fm = page["fm"]
        title = fm.get("title") or Path(key).name
        titles[title].append(key)
        required = {"title", "category", "summary"}
        if not required.issubset(fm.keys()):
            missing_fm.append(key)
        updated = fm.get("updated")
        if updated:
            try:
                d = dt.date.fromisoformat(updated)
                if d < stale_cutoff:
                    stale.append((key, updated))
            except ValueError:
                pass
    duplicate_titles = {t: ks for t, ks in titles.items() if len(ks) > 1}

    # Log gap check
    log_path = wiki / "log.md"
    log_gap = None
    if log_path.exists():
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        dates = [dt.date.fromisoformat(m) for m in LOG_ENTRY_RE.findall(log_text)]
        if dates:
            last = max(dates)
            gap = (today - last).days
            if gap > log_gap_days:
                log_gap = {"last_entry": last.isoformat(), "days_ago": gap}
        else:
            log_gap = {"last_entry": None, "days_ago": None}

    return {
        "vault": str(vault),
        "total_pages": len(pages),
        "orphans": orphans,
        "broken_links": broken_links,
        "stale": stale,
        "missing_frontmatter": sorted(missing_fm),
        "duplicate_titles": duplicate_titles,
        "log_gap": log_gap,
    }


def print_report(r: dict) -> None:
    print(f"LLM Wiki health check — {r['vault']}")
    print(f"Total pages: {r['total_pages']}")
    print()

    def header(label: str, count: int) -> None:
        sym = "OK" if count == 0 else "WARN"
        print(f"[{sym}] {label}: {count}")

    header("orphan pages", len(r["orphans"]))
    for p in r["orphans"][:20]:
        print(f"   - {p}")
    if len(r["orphans"]) > 20:
        print(f"   ... and {len(r['orphans']) - 20} more")
    print()

    header("broken wikilinks", len(r["broken_links"]))
    for src, tgt in r["broken_links"][:20]:
        print(f"   - {src} -> [[{tgt}]]")
    print()

    header("stale pages", len(r["stale"]))
    for p, d in r["stale"][:20]:
        print(f"   - {p} (updated {d})")
    print()

    header("pages missing frontmatter", len(r["missing_frontmatter"]))
    for p in r["missing_frontmatter"][:20]:
        print(f"   - {p}")
    print()

    header("duplicate titles", len(r["duplicate_titles"]))
    for title, keys in list(r["duplicate_titles"].items())[:10]:
        print(f"   - '{title}': {keys}")
    print()

    gap = r["log_gap"]
    if gap:
        print(f"[WARN] log gap: last entry {gap['last_entry']} ({gap['days_ago']} days ago)")
    else:
        print("[OK] log gap: recent")


def main() -> None:
    p = argparse.ArgumentParser(description="Lint an LLM Wiki vault")
    p.add_argument("--vault", required=True)
    p.add_argument("--stale-days", type=int, default=90)
    p.add_argument("--log-gap-days", type=int, default=14)
    p.add_argument("--json", action="store_true")
    args = p.parse_args()

    report = scan(
        Path(args.vault).expanduser().resolve(),
        stale_days=args.stale_days,
        log_gap_days=args.log_gap_days,
    )
    if args.json:
        print(json.dumps(report, indent=2, default=list))
    else:
        print_report(report)


if __name__ == "__main__":
    main()
