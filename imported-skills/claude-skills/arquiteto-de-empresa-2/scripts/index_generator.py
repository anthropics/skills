#!/usr/bin/env python3
"""index_generator.py — (Re)generates the concept tables of the index.md files of an OKF bundle.

For each folder that has an `index.md` with the markers
`<!-- okf:index:start -->` ... `<!-- okf:index:end -->`, it reads the sibling concepts
(.md that are not index.md/log.md), extracts title/description/type/status from the
frontmatter, and regenerates the table between the markers.

By default it is a dry-run (shows what would change). Use --write to save.
Deterministic, standard library only.

Usage:
    python index_generator.py                      # demo on an embedded example bundle
    python index_generator.py ./my-company   # dry-run: shows proposed tables
    python index_generator.py ./my-company --write
    python index_generator.py ./my-company --output json
    python index_generator.py --sample
"""

import argparse
import json
import os
import sys
import tempfile

START = "<!-- okf:index:start -->"
END = "<!-- okf:index:end -->"
RESERVED = {"index.md", "log.md"}


def parse_frontmatter(text):
    if not text.startswith("---"):
        return {}
    end = text.find("\n---", 3)
    if end == -1:
        return {}
    fm = {}
    for line in text[3:end].strip("\n").splitlines():
        if line and not line.startswith((" ", "\t")) and ":" in line:
            key, _, val = line.partition(":")
            fm[key.strip()] = val.strip().strip('"').strip("'")
    return fm


def concept_rows(folder):
    rows = []
    for name in sorted(os.listdir(folder)):
        if not name.endswith(".md") or name in RESERVED:
            continue
        full = os.path.join(folder, name)
        if not os.path.isfile(full):
            continue
        try:
            with open(full, "r", encoding="utf-8") as f:
                fm = parse_frontmatter(f.read())
        except (IOError, OSError):
            fm = {}
        slug = name[:-3]
        title = fm.get("title", slug)
        what = fm.get("description", title)
        tp = fm.get("type", "?")
        status = fm.get("status", "")
        rows.append(f"| [{slug}]({name}) | {what} | {tp} | {status} |")
    if not rows:
        rows = ["<!-- (no concepts yet) -->"]
    return rows


def replace_between(text, body):
    si = text.find(START)
    ei = text.find(END)
    if si == -1 or ei == -1 or ei < si:
        return None  # no markers
    new_block = START + "\n" + "\n".join(body) + "\n" + END
    return text[:si] + new_block + text[ei + len(END):]


def process(bundle_dir, write):
    bundle_dir = os.path.abspath(bundle_dir)
    results = []
    for root, _, files in os.walk(bundle_dir):
        if "index.md" not in files:
            continue
        idx = os.path.join(root, "index.md")
        try:
            with open(idx, "r", encoding="utf-8") as f:
                text = f.read()
        except (IOError, OSError):
            continue
        if START not in text:
            continue
        rows = concept_rows(root)
        new_text = replace_between(text, rows)
        rel = os.path.relpath(idx, bundle_dir)
        changed = new_text is not None and new_text != text
        if write and changed:
            with open(idx, "w", encoding="utf-8") as f:
                f.write(new_text)
        results.append({
            "index": rel,
            "concepts": len([r for r in rows if r.startswith("|")]),
            "changed": changed,
            "rows": rows,
        })
    return {
        "bundle": bundle_dir,
        "mode": "write" if write else "dry-run",
        "indexes_processed": len(results),
        "indexes_changed": sum(1 for r in results if r["changed"]),
        "results": results,
    }


def build_sample_bundle(base):
    root = os.path.join(base, "exemplo")
    os.makedirs(os.path.join(root, "00-fundacao"), exist_ok=True)
    with open(os.path.join(root, "00-fundacao", "index.md"), "w", encoding="utf-8") as f:
        f.write("# Foundation\n\n## Concepts\n\n| Concept | What it is | type | status |\n|---|---|---|---|\n"
                + START + "\n" + END + "\n")
    with open(os.path.join(root, "00-fundacao", "identidade.md"), "w", encoding="utf-8") as f:
        f.write("---\ntype: Foundation\ntitle: Identity\ndescription: Purpose, mission, and values\n"
                "status: draft\n---\n\n# Identity\n")
    return root


def render_text(r):
    out = ["=" * 64, "INDEX GENERATOR (OKF)", f"Bundle: {r['bundle']}",
           f"Mode: {r['mode']}   index.md processed: {r['indexes_processed']}   "
           f"changed: {r['indexes_changed']}", "=" * 64]
    for item in r["results"]:
        flag = "CHANGE" if item["changed"] else "ok"
        out.append(f"\n[{flag}] {item['index']}  ({item['concepts']} concept(s))")
        for row in item["rows"]:
            out.append(f"    {row}")
    if r["mode"] == "dry-run":
        out.append("\n(dry-run: nothing saved. Use --write to apply.)")
    return "\n".join(out)


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

    p = argparse.ArgumentParser(
        description="(Re)generates the concept tables of the index.md files of an OKF bundle.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    p.add_argument("path", nargs="?", help="Bundle folder (omitted = embedded example)")
    p.add_argument("--sample", action="store_true", help="Uses the embedded example bundle")
    p.add_argument("--write", action="store_true", help="Saves the changes (default: dry-run)")
    p.add_argument("--output", choices=("text", "json"), default="text")
    args = p.parse_args()

    if args.path and not args.sample:
        if not os.path.isdir(args.path):
            print(f"error: not a folder: {args.path}", file=sys.stderr)
            return 2
        result = process(args.path, args.write)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            result = process(build_sample_bundle(tmp), args.write)
            result["bundle"] = "<embedded example bundle>"

    if args.output == "json":
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        print(render_text(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
