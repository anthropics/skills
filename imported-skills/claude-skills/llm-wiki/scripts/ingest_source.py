#!/usr/bin/env python3
"""
ingest_source.py — Prepare a source for LLM ingestion.

This is a *helper* — it does not call an LLM. It extracts text and metadata from
a source file and emits a JSON brief the LLM (via the /wiki-ingest command or
the wiki-ingestor sub-agent) can read, discuss with the user, and use to update
the wiki.

Supported source types (stdlib only):
  .md  .txt  .html .htm  .json  .csv

For .pdf and binary formats, install optional readers yourself, or let the LLM
read the file directly via its Read tool.

Usage:
    python ingest_source.py --vault ~/vaults/research --source raw/paper.md
    python ingest_source.py --vault . --source raw/article.html --json

Output (JSON):
    {
      "source_path": "raw/paper.md",
      "relative": "raw/paper.md",
      "bytes": 12345,
      "sha256": "...",
      "ext": ".md",
      "title_guess": "Monosemanticity",
      "word_count": 8432,
      "preview": "First 1200 chars...",
      "existing_summary_page": "wiki/sources/monosemanticity.md" | null,
      "suggested_summary_path": "wiki/sources/monosemanticity.md"
    }
"""
from __future__ import annotations
import argparse
import hashlib
import html.parser
import json
import re
import sys
from pathlib import Path

PREVIEW_CHARS = 1200
SLUG_RE = re.compile(r"[^a-z0-9]+")


def slugify(text: str) -> str:
    text = text.lower().strip()
    text = SLUG_RE.sub("-", text).strip("-")
    return text[:60] or "untitled"


class _HTMLTextExtractor(html.parser.HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []
        self.title: str | None = None
        self._in_title = False
        self._skip = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in {"script", "style"}:
            self._skip = True
        if tag == "title":
            self._in_title = True

    def handle_endtag(self, tag: str) -> None:
        if tag in {"script", "style"}:
            self._skip = False
        if tag == "title":
            self._in_title = False

    def handle_data(self, data: str) -> None:
        if self._skip:
            return
        if self._in_title and self.title is None:
            self.title = data.strip() or None
        else:
            text = data.strip()
            if text:
                self.parts.append(text)

    def text(self) -> str:
        return "\n".join(self.parts)


def extract(path: Path) -> tuple[str, str | None]:
    ext = path.suffix.lower()
    data = path.read_bytes()
    if ext in {".md", ".txt"}:
        text = data.decode("utf-8", errors="replace")
        title = None
        for line in text.splitlines()[:20]:
            if line.startswith("# "):
                title = line[2:].strip()
                break
        return text, title
    if ext in {".html", ".htm"}:
        parser = _HTMLTextExtractor()
        try:
            parser.feed(data.decode("utf-8", errors="replace"))
        except Exception:
            pass
        return parser.text(), parser.title
    if ext == ".json":
        try:
            obj = json.loads(data.decode("utf-8", errors="replace"))
            return json.dumps(obj, indent=2)[:100000], None
        except Exception:
            return data.decode("utf-8", errors="replace"), None
    if ext == ".csv":
        text = data.decode("utf-8", errors="replace")
        head = "\n".join(text.splitlines()[:50])
        return head, None
    # Unknown: attempt utf-8 decode, let the LLM handle it
    try:
        return data.decode("utf-8", errors="replace"), None
    except Exception:
        return "", None


def main() -> None:
    p = argparse.ArgumentParser(description="Prepare a source for LLM ingestion.")
    p.add_argument("--vault", required=True)
    p.add_argument("--source", required=True, help="Path to the source file (inside raw/)")
    p.add_argument("--json", action="store_true", help="Emit JSON only")
    args = p.parse_args()

    vault = Path(args.vault).expanduser().resolve()
    src = Path(args.source).expanduser().resolve()
    if not src.exists():
        print(f"[error] source not found: {src}", file=sys.stderr)
        sys.exit(1)

    try:
        rel = src.relative_to(vault)
    except ValueError:
        rel = src

    text, title = extract(src)
    title_guess = title or src.stem.replace("-", " ").replace("_", " ").title()
    slug = slugify(title_guess)
    suggested = f"wiki/sources/{slug}.md"
    existing = vault / suggested
    existing_path = str(suggested) if existing.exists() else None

    brief = {
        "source_path": str(src),
        "relative": str(rel).replace("\\", "/"),
        "bytes": src.stat().st_size,
        "sha256": hashlib.sha256(src.read_bytes()).hexdigest()[:16],
        "ext": src.suffix.lower(),
        "title_guess": title_guess,
        "word_count": len(text.split()),
        "preview": text[:PREVIEW_CHARS],
        "existing_summary_page": existing_path,
        "suggested_summary_path": suggested,
    }

    if args.json:
        print(json.dumps(brief, indent=2, ensure_ascii=False))
    else:
        print(f"Source:         {brief['source_path']}")
        print(f"Title (guess):  {brief['title_guess']}")
        print(f"Size:           {brief['bytes']} bytes ({brief['word_count']} words)")
        print(f"SHA256 (short): {brief['sha256']}")
        print(f"Suggested page: {brief['suggested_summary_path']}")
        if existing_path:
            print(f"EXISTING PAGE:  {existing_path}  ← re-ingest / merge mode")
        print()
        print("--- preview ---")
        print(brief["preview"])
        print("--- /preview ---")


if __name__ == "__main__":
    main()
