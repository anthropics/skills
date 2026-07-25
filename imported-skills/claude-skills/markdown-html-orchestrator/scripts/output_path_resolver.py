#!/usr/bin/env python3
"""output_path_resolver.py - Resolve the final output path for a conversion.

Stdlib-only. Given:
  - the input markdown filename
  - an optional --out user override
  - the design-system config's default_output_dir
  - a --doctype hint (document/review/slides) for naming convention

Returns the final absolute path the converter should write to. Handles
collisions by suffixing -2, -3, ... or by inserting an ISO-8601 stamp,
depending on --on-collision mode. Refuses if the chosen parent isn't
writable (matches onboard.py's hard rule).

Pattern (kebab slug + collision detection + timestamp fallback) lifted from
marketing/landing/skills/landing/scripts/kebab_slug_generator.py and
adapted: doctype prefix in the filename, --out override, design-system
default_output_dir as the fallback root.

NO LLM CALLS. Pure path math.

Usage:
    python output_path_resolver.py --input report.md
    python output_path_resolver.py --input report.md --out ./docs/ --doctype document
    python output_path_resolver.py --input PR-123.md --doctype review --on-collision timestamp
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

# Bridge to the design-system config
_DESIGN_SYSTEM_SCRIPTS = (
    Path(__file__).resolve().parent.parent.parent / "design-system" / "scripts"
)
sys.path.insert(0, str(_DESIGN_SYSTEM_SCRIPTS))
try:
    import config_loader as cfg
except ImportError:
    cfg = None

DOCTYPE_PREFIXES = {
    "document": "doc",
    "review": "review",
    "slides": "deck",
}


def kebab_slug(name: str) -> str:
    """Convert a filename or title to a clean kebab-case slug.

    'My Report v2!.md' -> 'my-report-v2'
    '  Spaces   And   Stuff  ' -> 'spaces-and-stuff'
    """
    base = name.rsplit(".", 1)[0] if "." in name else name
    # Strip non-alphanumerics, collapse to hyphen
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", base).strip("-").lower()
    return slug or "untitled"


def _writable(path: Path) -> bool:
    p = path.expanduser()
    parent = p.parent if p.suffix else p
    while not parent.exists():
        if parent.parent == parent:
            return False
        parent = parent.parent
    return os.access(parent, os.W_OK)


def _resolve_base_dir(out_override: str | None) -> Path:
    if out_override:
        return Path(out_override).expanduser()
    if cfg is not None and not os.environ.get("MARKDOWN_HTML_NO_CONFIG") == "1":
        config = cfg.load_config()
        default_dir = config.get("default_output_dir") or "./markdown-html-out/"
    else:
        default_dir = "./markdown-html-out/"
    return Path(default_dir).expanduser()


def resolve(
    input_path: str,
    out_override: str | None = None,
    doctype: str | None = None,
    on_collision: str = "suffix",
) -> dict[str, Any]:
    """Resolve the final output path. Returns a structured dict with the path
    and any collision-handling that happened.
    """
    in_p = Path(input_path)
    slug = kebab_slug(in_p.name)
    prefix = DOCTYPE_PREFIXES.get(doctype or "", "")
    filename_base = f"{prefix}-{slug}" if prefix else slug

    base_dir = _resolve_base_dir(out_override)
    base_dir.mkdir(parents=True, exist_ok=True)

    target = base_dir / f"{filename_base}.html"

    collision_info: dict[str, Any] = {"existed": False, "strategy": None}
    if target.exists():
        collision_info["existed"] = True
        if on_collision == "timestamp":
            stamp = _dt.datetime.now().strftime("%Y%m%dT%H%M%S")
            target = base_dir / f"{filename_base}-{stamp}.html"
            collision_info["strategy"] = "timestamp"
        elif on_collision == "overwrite":
            collision_info["strategy"] = "overwrite"
            # target unchanged
        else:  # suffix
            for n in range(2, 1000):
                candidate = base_dir / f"{filename_base}-{n}.html"
                if not candidate.exists():
                    target = candidate
                    collision_info["strategy"] = f"suffix-{n}"
                    break
            else:
                stamp = _dt.datetime.now().strftime("%Y%m%dT%H%M%S")
                target = base_dir / f"{filename_base}-{stamp}.html"
                collision_info["strategy"] = "timestamp-after-suffix-exhausted"

    return {
        "input": str(in_p),
        "slug": slug,
        "doctype": doctype,
        "prefix": prefix,
        "base_dir": str(base_dir),
        "output_path": str(target),
        "writable": _writable(target),
        "collision": collision_info,
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--input", help="Input markdown filename or path")
    parser.add_argument("--out", help="Override the output directory (else uses config default)")
    parser.add_argument("--doctype", choices=["document", "review", "slides"],
                        help="Doc type — controls filename prefix (doc-, review-, deck-)")
    parser.add_argument("--on-collision", choices=["suffix", "timestamp", "overwrite"],
                        default="suffix")
    parser.add_argument("--output", choices=["human", "json"], default="human",
                        dest="output_format")
    parser.add_argument("--sample", action="store_true",
                        help="Show a resolved-path example without touching disk semantics")
    args = parser.parse_args(argv)

    if args.sample:
        result = resolve("example-report.md", None, "document", "suffix")
    elif args.input:
        result = resolve(args.input, args.out, args.doctype, args.on_collision)
    else:
        parser.print_help()
        return 0

    if not result["writable"]:
        print(
            f"refusing: target parent '{result['base_dir']}' is not writable. "
            f"Re-run onboarding or pass --out to a writable dir.",
            file=sys.stderr,
        )
        return 3

    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(f"output -> {result['output_path']}")
        if result["collision"]["existed"]:
            print(f"  (collision handled: {result['collision']['strategy']})")
        print(f"  base_dir: {result['base_dir']}")
        print(f"  slug: {result['slug']}, prefix: {result['prefix']}")

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
