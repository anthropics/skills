#!/usr/bin/env python3
"""kebab_slug_generator.py — Product name → kebab-case .html filename.

Stdlib-only. Given a product name and an output directory, produce:

  - slug:           kebab-case alphanumeric (max 50 chars)
  - filename:       <slug>.html
  - output_path:    <output_dir>/<filename>
  - duplicate:      true/false (does file already exist?)
  - suggested_alt:  if duplicate, suggest timestamped alternative

NO LLM CALLS. Pure string transformation + filesystem stat.

Usage:
    python kebab_slug_generator.py --product "Quill AI"
    python kebab_slug_generator.py --product "Quill AI" --output-dir ./landing-pages
    python kebab_slug_generator.py --product "Self-Hosted LLM Tool" --output json
    python kebab_slug_generator.py --sample
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List


SLUG_MAX_LEN = 50
DEFAULT_OUTPUT_DIR = "./landing-pages"


def slugify(product: str) -> str:
    """Convert product name to kebab-case slug."""
    s = product.lower()
    s = re.sub(r"[^a-z0-9]+", "-", s)
    s = re.sub(r"-+", "-", s)
    s = s.strip("-")
    if len(s) > SLUG_MAX_LEN:
        truncated = s[:SLUG_MAX_LEN]
        last_hyphen = truncated.rfind("-")
        if last_hyphen > SLUG_MAX_LEN // 2:
            s = truncated[:last_hyphen]
        else:
            s = truncated
    return s or "landing-page"


def resolve_output_dir(override: str = None) -> Path:
    if override:
        return Path(override).expanduser().resolve()
    env = os.environ.get("OUTPUT_DIR")
    if env:
        return Path(env).expanduser().resolve()
    return Path(DEFAULT_OUTPUT_DIR).resolve()


def generate(product: str, output_dir: Path) -> Dict[str, Any]:
    slug = slugify(product)
    filename = f"{slug}.html"
    output_path = output_dir / filename

    duplicate = output_path.exists()
    suggested_alt = None
    if duplicate:
        ts = datetime.now().strftime("%Y%m%d-%H%M%S")
        alt = output_dir / f"{slug}-{ts}.html"
        suggested_alt = str(alt)

    return {
        "product": product,
        "slug": slug,
        "filename": filename,
        "output_dir": str(output_dir),
        "output_path": str(output_path),
        "duplicate": duplicate,
        "suggested_alt": suggested_alt,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Product:                {result['product']}")
    out.append(f"Slug:                   {result['slug']}")
    out.append(f"Filename:               {result['filename']}")
    out.append(f"Output dir:             {result['output_dir']}")
    out.append(f"Output path:            {result['output_path']}")
    out.append(f"Duplicate at path:      {'YES' if result['duplicate'] else 'no'}")
    if result["duplicate"]:
        out.append(f"Suggested alternative:  {result['suggested_alt']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--product", help="Product name")
    parser.add_argument("--output-dir", help="Output directory (default: $OUTPUT_DIR or ./landing-pages)")
    parser.add_argument("--sample", action="store_true", help="Run on sample product")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = generate("Quill AI — Async Standup Tool", Path("/tmp/sample-landing"))
    elif args.product:
        output_dir = resolve_output_dir(args.output_dir)
        result = generate(args.product, output_dir)
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
