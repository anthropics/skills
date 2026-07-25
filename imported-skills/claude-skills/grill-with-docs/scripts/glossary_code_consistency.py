#!/usr/bin/env python3
"""glossary_code_consistency.py — Cross-reference CONTEXT.md terms against the codebase.

Stdlib-only. Reads bold terms from CONTEXT.md and scans a codebase directory for
each term's usage. Surfaces two grilling-question seeds:

  1. DEAD GLOSSARY — a term is defined in CONTEXT.md but never appears in code.
     Either the term is stale (delete it) or the code uses a synonym (rename).

  2. CODE-ONLY PROPER NOUN — a capitalized word that appears frequently in code
     but isn't defined in CONTEXT.md. Either it's a generic programming concept
     (ignore) or it's a domain term that snuck in undefined (add to glossary).

Both lists are seeded as opening grill-with-docs questions.

NO LLM CALLS. Pure file walking + regex + frequency counting.

Limitations (intentional, stdlib-only):
  - Word-boundary matching is case-insensitive. "Order" matches "order", "ORDER", "orders".
  - "Code-only proper noun" detection uses a simple heuristic: capitalized
    words >= MIN_FREQUENCY occurrences across non-test files. Tunable via flags.
  - Only scans common source extensions by default (override with --extensions).

Usage:
    python glossary_code_consistency.py --context CONTEXT.md --code src/
    python glossary_code_consistency.py --context CONTEXT.md --code src/ --output json
    python glossary_code_consistency.py --sample
"""

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple


DEFAULT_EXTENSIONS = {
    ".py",
    ".ts",
    ".tsx",
    ".js",
    ".jsx",
    ".go",
    ".java",
    ".kt",
    ".rb",
    ".cs",
    ".rs",
    ".swift",
    ".php",
    ".scala",
    ".clj",
    ".ex",
    ".exs",
}
DEFAULT_EXCLUDE_DIRS = {"node_modules", ".git", "dist", "build", "target", ".venv", "venv", "__pycache__"}
TEST_FILE_HINTS = (".test.", ".spec.", "_test.", "tests/", "/test/")
PROPER_NOUN_RE = re.compile(r"\b([A-Z][a-zA-Z]{2,})\b")
GENERIC_WORDS = {
    # Programming concepts that capitalize but aren't domain terms
    "True", "False", "None", "Null", "Promise", "Error", "Exception",
    "String", "Number", "Boolean", "Array", "Object", "Map", "Set",
    "List", "Dict", "Tuple", "Optional", "Any", "Result", "Date",
    "Math", "JSON", "URL", "URI", "HTTP", "HTTPS", "API", "ID", "UUID",
    "GET", "POST", "PUT", "DELETE", "PATCH", "OK", "TODO", "FIXME",
    "Test", "Mock", "Stub", "Spy", "Given", "When", "Then", "Describe",
}

SAMPLE_CONTEXT_MD = """# Ordering

## Language

**Order**:
A confirmed request from a Customer to acquire one or more Products.
_Avoid_: Purchase, transaction

**Customer**:
A person or organization that places Orders.
_Avoid_: Client, buyer

**Product**:
A single SKU that can appear on an Order line.
_Avoid_: Item, good

**Discount**:
A reduction applied to an Order at checkout.
_Avoid_: Coupon, promo
"""

SAMPLE_CODE_FILES: Dict[str, str] = {
    "src/orders.py": (
        "class Order:\n"
        "    pass\n"
        "\n"
        "def cancel_order(order_id: str) -> None:\n"
        "    pass\n"
        "\n"
        "def list_customer_orders(customer_id: str) -> list[Order]:\n"
        "    pass\n"
    ),
    "src/customers.py": (
        "class Customer:\n"
        "    pass\n"
        "\n"
        "class Subscription:\n"
        "    # NOTE: Subscription is used heavily but not in glossary\n"
        "    pass\n"
        "\n"
        "def find_customer(email: str) -> Customer:\n"
        "    pass\n"
    ),
    "src/products.py": (
        "class Product:\n"
        "    pass\n"
        "\n"
        "class Inventory:\n"
        "    pass\n"
        "\n"
        "def find_product(sku: str) -> Product:\n"
        "    pass\n"
    ),
    # Note: Discount is defined in glossary but never used in code.
}


def extract_glossary_terms(context_md_text: str) -> List[str]:
    """Pull bold terms from CONTEXT.md `**Term**:` patterns."""
    return re.findall(r"\*\*([^*]+?)\*\*\s*:", context_md_text)


def walk_codebase(root: Path, extensions: Set[str], exclude_dirs: Set[str]) -> List[Path]:
    found: List[Path] = []
    for path in root.rglob("*"):
        if path.is_dir():
            continue
        if any(part in exclude_dirs for part in path.parts):
            continue
        if path.suffix in extensions:
            found.append(path)
    return found


def is_test_file(path: Path) -> bool:
    s = str(path).replace("\\", "/")
    return any(hint in s for hint in TEST_FILE_HINTS)


def count_term_in_text(text: str, term: str) -> int:
    pattern = re.compile(rf"\b{re.escape(term)}\b", re.IGNORECASE)
    return len(pattern.findall(text))


def count_proper_nouns(text: str) -> Counter:
    counter: Counter = Counter()
    for match in PROPER_NOUN_RE.finditer(text):
        counter[match.group(1)] += 1
    return counter


def analyze(
    context_md_text: str,
    code_files: List[Tuple[str, str]],
    min_proper_noun_frequency: int,
) -> Dict[str, Any]:
    """code_files: list of (relative_path, text) tuples."""
    glossary_terms = extract_glossary_terms(context_md_text)
    glossary_term_set_lower = {t.lower() for t in glossary_terms}

    # Per-term usage count in non-test files
    term_usage: Dict[str, int] = {t: 0 for t in glossary_terms}
    code_proper_nouns: Counter = Counter()
    files_scanned = 0
    files_tests_skipped = 0

    for path_str, text in code_files:
        path = Path(path_str)
        if is_test_file(path):
            files_tests_skipped += 1
            continue
        files_scanned += 1
        for term in glossary_terms:
            term_usage[term] += count_term_in_text(text, term)
        for noun, count in count_proper_nouns(text).items():
            code_proper_nouns[noun] += count

    # Dead glossary: terms with zero usage
    dead_terms = [t for t, n in term_usage.items() if n == 0]

    # Code-only proper nouns: frequent capitalized identifiers NOT in glossary
    # and NOT in the generic stop-list
    code_only: List[Tuple[str, int]] = []
    for noun, count in code_proper_nouns.most_common():
        if count < min_proper_noun_frequency:
            break
        if noun.lower() in glossary_term_set_lower:
            continue
        if noun in GENERIC_WORDS:
            continue
        code_only.append((noun, count))

    return {
        "files_scanned": files_scanned,
        "files_tests_skipped": files_tests_skipped,
        "glossary_term_count": len(glossary_terms),
        "term_usage": term_usage,
        "dead_glossary_terms": dead_terms,
        "code_only_proper_nouns": code_only,
        "min_proper_noun_frequency": min_proper_noun_frequency,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append("Glossary↔Code consistency report")
    out.append(f"  Files scanned: {result['files_scanned']}  (test files skipped: {result['files_tests_skipped']})")
    out.append(f"  Glossary terms: {result['glossary_term_count']}")
    out.append("")
    out.append("Term usage (occurrences in non-test code):")
    for term, count in sorted(result["term_usage"].items(), key=lambda kv: (-kv[1], kv[0])):
        marker = "  " if count > 0 else "!!"
        out.append(f"  {marker} {term:<30s} {count}")
    out.append("")
    if result["dead_glossary_terms"]:
        out.append("DEAD GLOSSARY (defined but never used in code) — grill these:")
        for term in result["dead_glossary_terms"]:
            out.append(f"  - '{term}': dead term, or rename happened?")
    else:
        out.append("DEAD GLOSSARY: (none — every defined term is used in code)")
    out.append("")
    if result["code_only_proper_nouns"]:
        out.append(
            f"CODE-ONLY PROPER NOUNS (>= {result['min_proper_noun_frequency']}x, not in glossary, not generic) — grill these:"
        )
        for noun, count in result["code_only_proper_nouns"]:
            out.append(f"  - '{noun}' ({count} occurrences): domain term that needs definition, or generic?")
    else:
        out.append("CODE-ONLY PROPER NOUNS: (none above threshold — glossary covers the frequent domain nouns)")
    return "\n".join(out)


def run_sample(min_freq: int) -> Dict[str, Any]:
    files = [(p, t) for p, t in SAMPLE_CODE_FILES.items()]
    return analyze(SAMPLE_CONTEXT_MD, files, min_freq)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--context", help="Path to CONTEXT.md")
    parser.add_argument("--code", help="Path to codebase root")
    parser.add_argument(
        "--extensions",
        help="Comma-separated source extensions to scan (default: common languages)",
        default=None,
    )
    parser.add_argument(
        "--min-frequency",
        type=int,
        default=3,
        help="Minimum occurrences for a code-only proper noun to surface (default: 3)",
    )
    parser.add_argument("--sample", action="store_true", help="Run on the embedded sample data")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = run_sample(args.min_frequency)
    elif args.context and args.code:
        context_path = Path(args.context)
        code_root = Path(args.code)
        if not context_path.exists():
            print(f"error: {args.context} not found", file=sys.stderr)
            return 2
        if not code_root.exists():
            print(f"error: {args.code} not found", file=sys.stderr)
            return 2
        if args.extensions:
            exts = {e.strip() if e.strip().startswith(".") else "." + e.strip() for e in args.extensions.split(",")}
        else:
            exts = DEFAULT_EXTENSIONS
        files: List[Tuple[str, str]] = []
        for p in walk_codebase(code_root, exts, DEFAULT_EXCLUDE_DIRS):
            try:
                files.append((str(p), p.read_text(encoding="utf-8", errors="ignore")))
            except (OSError, UnicodeDecodeError):
                continue
        result = analyze(context_path.read_text(encoding="utf-8"), files, args.min_frequency)
    else:
        parser.print_help()
        return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
