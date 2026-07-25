#!/usr/bin/env python3
"""token_savings_estimator.py — Estimate token-cost savings from caveman compression.

Stdlib-only. Uses a chars-per-token heuristic (4 chars/token average for English
prose; 3.5 for technical text) to estimate output tokens before vs after caveman
compression.

Why heuristic and not real tokenizer:
- No external dependencies (stdlib only)
- Tokenizer accuracy varies by model (cl100k_base vs o200k_base vs others)
- Heuristic is within 10-15% of real tokenizer output for English prose
- Reports both heuristic + character count so user can apply their own multiplier

Usage:
    python token_savings_estimator.py                         # uses embedded sample
    python token_savings_estimator.py "your text"
    python token_savings_estimator.py --file path/to/input.txt
    python token_savings_estimator.py "text" --output json
    python token_savings_estimator.py "text" --price-per-mtok 3.00
"""

import argparse
import json
import sys
from typing import Any, Dict

# Import the compressor as a module
import os
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from caveman_compressor import compress, SAMPLE_INPUT  # noqa: E402


# Heuristic: average chars per token
CHARS_PER_TOKEN_PROSE = 4.0
CHARS_PER_TOKEN_TECHNICAL = 3.5
TECHNICAL_TOKEN_INDICATORS = ("```", "{", "}", "()", "->", "==", "//", "/*", "import ", "function ")


def _estimate_chars_per_token(text: str) -> float:
    """Heuristic: technical text has more tokens per char than prose."""
    hit_count = sum(1 for sig in TECHNICAL_TOKEN_INDICATORS if sig in text)
    if hit_count >= 3:
        return CHARS_PER_TOKEN_TECHNICAL
    return CHARS_PER_TOKEN_PROSE


def estimate_tokens(text: str) -> int:
    return int(round(len(text) / _estimate_chars_per_token(text)))


def analyze(original: str, price_per_mtok: float = 0.0) -> Dict[str, Any]:
    compressed = compress(original)
    orig_tokens = estimate_tokens(original)
    new_tokens = estimate_tokens(compressed)
    saved = orig_tokens - new_tokens
    pct = round(100.0 * saved / max(orig_tokens, 1), 1)

    out: Dict[str, Any] = {
        "original_chars": len(original),
        "compressed_chars": len(compressed),
        "chars_per_token_used": _estimate_chars_per_token(original),
        "estimated_original_tokens": orig_tokens,
        "estimated_compressed_tokens": new_tokens,
        "tokens_saved": saved,
        "percent_token_savings": pct,
        "compressed_preview": compressed[:200] + ("..." if len(compressed) > 200 else ""),
    }

    if price_per_mtok > 0:
        cost_per_token = price_per_mtok / 1_000_000.0
        out["price_per_million_tokens"] = price_per_mtok
        out["cost_saved_per_response_usd"] = round(saved * cost_per_token, 6)
        out["cost_saved_per_1k_responses_usd"] = round(saved * cost_per_token * 1000, 4)

    return out


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("TOKEN SAVINGS ESTIMATOR (caveman compression)")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Chars/token heuristic: {r['chars_per_token_used']:.1f} (prose=4.0; technical=3.5)")
    lines.append("")
    lines.append(f"Original:   {r['original_chars']} chars  ~ {r['estimated_original_tokens']} tokens")
    lines.append(f"Compressed: {r['compressed_chars']} chars  ~ {r['estimated_compressed_tokens']} tokens")
    lines.append("")
    lines.append(f"Savings: {r['tokens_saved']} tokens ({r['percent_token_savings']}%)")
    if "price_per_million_tokens" in r:
        lines.append("")
        lines.append(f"At ${r['price_per_million_tokens']}/Mtok:")
        lines.append(f"  Cost saved per response:   ${r['cost_saved_per_response_usd']:.6f}")
        lines.append(f"  Cost saved per 1k responses: ${r['cost_saved_per_1k_responses_usd']:.4f}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("Compressed preview:")
    lines.append(f"  {r['compressed_preview']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Estimate token + cost savings from caveman compression.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    price_help = "Per-million-token price (USD) to estimate cost savings"
    parser.add_argument("text", nargs="?", help="Input text (uses embedded sample if omitted)")
    parser.add_argument("--file", help="Read input from file")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    parser.add_argument("--price-per-mtok", type=float, default=0.0, help=price_help)
    args = parser.parse_args()

    if args.file:
        try:
            with open(args.file, "r", encoding="utf-8") as f:
                original = f.read()
        except (IOError, OSError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
    elif args.text:
        original = args.text
    else:
        original = SAMPLE_INPUT

    result = analyze(original, args.price_per_mtok)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
