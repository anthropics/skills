#!/usr/bin/env python3
"""Generate the eval-set editor from its existing template, without raw HTML substitution.

Usage: python -m scripts.generate_eval_review evals.json --skill-name demo \
    --skill-description "Current description" --output /tmp/eval_review.html
"""

import argparse
import html
import json
import re
from pathlib import Path


def generate_review(evals: object, skill_name: str, skill_description: str) -> str:
    """Embed eval JSON in script context and names/descriptions in HTML text context."""
    if not isinstance(evals, list) or any(
        not isinstance(item, dict)
        or not isinstance(item.get("query"), str)
        or not isinstance(item.get("should_trigger"), bool)
        for item in evals
    ):
        raise ValueError("Expected an eval array with string query and boolean should_trigger fields")
    template = (Path(__file__).resolve().parents[1] / "assets" / "eval_review.html").read_text(encoding="utf-8")
    eval_json = json.dumps(evals, ensure_ascii=True)
    for char, escaped in (("<", "\\u003c"), (">", "\\u003e"), ("&", "\\u0026")):
        eval_json = eval_json.replace(char, escaped)
    replacements = {
        "__EVAL_DATA_PLACEHOLDER__": eval_json,
        "__SKILL_NAME_PLACEHOLDER__": html.escape(skill_name),
        "__SKILL_DESCRIPTION_PLACEHOLDER__": html.escape(skill_description),
    }
    # One pass over the template: placeholder-looking user data stays literal.
    return re.sub("|".join(map(re.escape, replacements)), lambda match: replacements[match[0]], template)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate a safe eval-set review page")
    parser.add_argument("eval_set", type=Path)
    parser.add_argument("--skill-name", required=True)
    parser.add_argument("--skill-description", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        evals = json.loads(args.eval_set.read_text(encoding="utf-8"))
        page = generate_review(evals, args.skill_name, args.skill_description)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    args.output.write_text(page, encoding="utf-8")


if __name__ == "__main__":
    main()
