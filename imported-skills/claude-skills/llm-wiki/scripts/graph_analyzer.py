#!/usr/bin/env python3
"""
graph_analyzer.py — Analyze the wikilink graph of an LLM Wiki vault.

Reports hubs, orphans, bridges, and weakly-connected components so the LLM
knows where to focus cross-referencing work.

Usage:
    python graph_analyzer.py --vault ~/vaults/research
    python graph_analyzer.py --vault . --json
    python graph_analyzer.py --vault . --top 20
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

WIKILINK_RE = re.compile(r"\[\[([^\]|#]+)(?:#[^\]|]*)?(?:\|[^\]]*)?\]\]")


def build_graph(vault: Path):
    wiki = vault / "wiki"
    if not wiki.exists():
        raise SystemExit(f"[error] {wiki} not found")
    nodes: set[str] = set()
    out: dict[str, set[str]] = defaultdict(set)
    inb: dict[str, set[str]] = defaultdict(set)
    stems: dict[str, str] = {}

    for md in wiki.rglob("*.md"):
        rel = md.relative_to(wiki)
        if rel.name in {"index.md", "log.md"}:
            continue
        if any(part.startswith(".") for part in rel.parts):
            continue
        key = str(rel).replace("\\", "/")[:-3]
        nodes.add(key)
        stems[Path(key).name] = key

    for md in wiki.rglob("*.md"):
        rel = md.relative_to(wiki)
        if rel.name in {"index.md", "log.md"} or any(p.startswith(".") for p in rel.parts):
            continue
        key = str(rel).replace("\\", "/")[:-3]
        text = md.read_text(encoding="utf-8", errors="replace")
        for m in WIKILINK_RE.finditer(text):
            target = m.group(1).strip()
            if target.endswith(".md"):
                target = target[:-3]
            if target in nodes:
                out[key].add(target)
                inb[target].add(key)
            elif Path(target).name in stems:
                resolved = stems[Path(target).name]
                out[key].add(resolved)
                inb[resolved].add(key)

    return nodes, out, inb


def connected_components(nodes: set[str], out: dict[str, set[str]], inb: dict[str, set[str]]):
    adj: dict[str, set[str]] = defaultdict(set)
    for n in nodes:
        adj[n] |= out.get(n, set())
        adj[n] |= inb.get(n, set())
    seen: set[str] = set()
    components: list[set[str]] = []
    for n in nodes:
        if n in seen:
            continue
        stack = [n]
        comp: set[str] = set()
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            comp.add(v)
            stack.extend(adj[v] - seen)
        components.append(comp)
    components.sort(key=len, reverse=True)
    return components


def analyze(vault: Path, top: int) -> dict:
    nodes, out, inb = build_graph(vault)
    hubs_out = sorted(nodes, key=lambda n: len(out.get(n, set())), reverse=True)[:top]
    hubs_in = sorted(nodes, key=lambda n: len(inb.get(n, set())), reverse=True)[:top]
    orphans = sorted(n for n in nodes if not inb.get(n))
    sinks = sorted(n for n in nodes if not out.get(n))
    comps = connected_components(nodes, out, inb)
    return {
        "total_pages": len(nodes),
        "total_edges": sum(len(v) for v in out.values()),
        "top_outbound_hubs": [{"page": h, "outbound": len(out.get(h, set()))} for h in hubs_out],
        "top_inbound_hubs": [{"page": h, "inbound": len(inb.get(h, set()))} for h in hubs_in],
        "orphans": orphans,
        "sinks": sinks,
        "components": [
            {"size": len(c), "sample": sorted(c)[:5]} for c in comps[:10]
        ],
        "component_count": len(comps),
    }


def main() -> None:
    p = argparse.ArgumentParser(description="Analyze the wikilink graph of an LLM Wiki vault")
    p.add_argument("--vault", required=True)
    p.add_argument("--top", type=int, default=10)
    p.add_argument("--json", action="store_true")
    args = p.parse_args()
    r = analyze(Path(args.vault).expanduser().resolve(), args.top)

    if args.json:
        print(json.dumps(r, indent=2, default=list))
        return

    print(f"LLM Wiki graph — {r['total_pages']} pages, {r['total_edges']} links")
    print(f"Connected components: {r['component_count']}")
    print()
    print("Top outbound hubs (pages that link to many others):")
    for h in r["top_outbound_hubs"]:
        print(f"  - {h['page']}  ({h['outbound']} out)")
    print()
    print("Top inbound hubs (pages many others link TO):")
    for h in r["top_inbound_hubs"]:
        print(f"  - {h['page']}  ({h['inbound']} in)")
    print()
    print(f"Orphans (no inbound): {len(r['orphans'])}")
    for o in r["orphans"][:10]:
        print(f"  - {o}")
    print()
    print(f"Sinks (no outbound): {len(r['sinks'])}")
    for s in r["sinks"][:10]:
        print(f"  - {s}")


if __name__ == "__main__":
    main()
