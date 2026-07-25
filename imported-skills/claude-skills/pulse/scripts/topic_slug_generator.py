#!/usr/bin/env python3
"""topic_slug_generator.py — Filesystem-safe slug for pulse output paths.

Stdlib-only. Given a topic string + date, produce:

  - slug:           kebab-case, alphanumeric-only, max 60 chars
  - filename:       <slug>-<YYYY-MM-DD>.md
  - output_path:    ${RESEARCH_DIR}/pulse/<slug>-<YYYY-MM-DD>.md
                    (RESEARCH_DIR resolved from env or default ~/research)
  - duplicate:      true/false — does the file already exist at the path?
  - suggested_alt:  if duplicate, an alternate filename (e.g., <slug>-<date>-v2.md)

NO LLM CALLS. Pure string transformation + filesystem stat.

Usage:
    python topic_slug_generator.py --topic "Self-Hosted LLM Deployment" --date 2026-05-15
    python topic_slug_generator.py --topic "Claude Code adoption" --date 2026-05-15 --output json
    python topic_slug_generator.py --topic "AI safety regulation" --research-dir /tmp/research
"""

import argparse
import json
import os
import re
import sys
from datetime import date as date_type, datetime
from pathlib import Path
from typing import Any, Dict, List


SLUG_MAX_LEN = 60
DEFAULT_RESEARCH_DIR_NAME = "research"


def slugify(topic: str) -> str:
    """Convert a topic string to a kebab-case slug.

    - Lowercase
    - Replace non-alphanumeric with hyphens
    - Collapse consecutive hyphens
    - Trim leading/trailing hyphens
    - Truncate to SLUG_MAX_LEN (preferring to break at hyphen boundaries)
    """
    s = topic.lower()
    s = re.sub(r"[^a-z0-9]+", "-", s)
    s = re.sub(r"-+", "-", s)
    s = s.strip("-")
    if len(s) > SLUG_MAX_LEN:
        # Truncate at the last hyphen before the limit, if possible
        truncated = s[:SLUG_MAX_LEN]
        last_hyphen = truncated.rfind("-")
        if last_hyphen > SLUG_MAX_LEN // 2:
            s = truncated[:last_hyphen]
        else:
            s = truncated
    return s or "untitled"


def resolve_research_dir(override: str = None) -> Path:
    if override:
        return Path(override).expanduser().resolve()
    env = os.environ.get("RESEARCH_DIR")
    if env:
        return Path(env).expanduser().resolve()
    return (Path.home() / DEFAULT_RESEARCH_DIR_NAME).resolve()


def generate(topic: str, when: date_type, research_dir: Path) -> Dict[str, Any]:
    slug = slugify(topic)
    date_str = when.strftime("%Y-%m-%d")
    filename = f"{slug}-{date_str}.md"
    output_dir = research_dir / "pulse"
    output_path = output_dir / filename

    duplicate = output_path.exists()
    suggested_alt = None
    if duplicate:
        # Find the lowest -vN suffix that doesn't already exist
        for n in range(2, 100):
            alt = output_dir / f"{slug}-{date_str}-v{n}.md"
            if not alt.exists():
                suggested_alt = str(alt)
                break

    return {
        "topic": topic,
        "slug": slug,
        "date": date_str,
        "filename": filename,
        "output_dir": str(output_dir),
        "output_path": str(output_path),
        "research_dir_resolved": str(research_dir),
        "duplicate": duplicate,
        "suggested_alt": suggested_alt,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Topic:                  {result['topic']}")
    out.append(f"Slug:                   {result['slug']}")
    out.append(f"Date:                   {result['date']}")
    out.append(f"Filename:               {result['filename']}")
    out.append(f"Output dir:             {result['output_dir']}")
    out.append(f"Output path:            {result['output_path']}")
    out.append(f"Research dir resolved:  {result['research_dir_resolved']}")
    out.append(f"Duplicate at path:      {'YES' if result['duplicate'] else 'no'}")
    if result["duplicate"]:
        out.append(f"Suggested alternative:  {result['suggested_alt']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--topic", help="Topic string")
    parser.add_argument("--date", help="Date (YYYY-MM-DD), default today")
    parser.add_argument("--research-dir", help="Override RESEARCH_DIR (default: $RESEARCH_DIR or ~/research)")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if not args.topic:
        parser.print_help()
        return 0

    if args.date:
        try:
            when = datetime.strptime(args.date, "%Y-%m-%d").date()
        except ValueError:
            print(f"error: --date must be YYYY-MM-DD, got '{args.date}'", file=sys.stderr)
            return 2
    else:
        when = date_type.today()

    research_dir = resolve_research_dir(args.research_dir)
    result = generate(args.topic, when, research_dir)

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
