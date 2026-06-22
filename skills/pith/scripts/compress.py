#!/usr/bin/env python3
"""
PITH v2 — Inter-Agent Payload Compressor (standalone CLI, zero dependencies)
Shannon local information scoring + Benford structural validation

Usage:
    echo "<payload>" | python3 compress.py
    python3 compress.py --payload "<text>" --ratio 0.7
    python3 compress.py --payload "<text>" --json

Pipeline:
  1. Size gate  (< 10000 chars → passthrough; guarantees Benford stability ≥100 sentences)
  2. LOG_CACHE  O(1) lookup table for log2
  3. FILLER     sentence-level boilerplate removal before Shannon scoring
  4. Shannon    local profiling  I(w) = log2(total) - LOG_CACHE[count(w)]
  5. Whitelist  logical connectors always preserved
  6. Pruning    adaptive token pruning: keep if I(w) >= threshold
  7. Polarity   micro-checksum per sentence; rollback on negation change
  8. Benford    macro gate; halve reduction and retry on MAD breach (max 3)
  9. Receptor   wrap output in <pith_optimization_layer> XML
"""

import sys
import re
import json
import math
import argparse
from collections import Counter

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # type: ignore[attr-defined]
if hasattr(sys.stdin, "reconfigure"):
    sys.stdin.reconfigure(encoding="utf-8")  # type: ignore[attr-defined]

# ── Constants ─────────────────────────────────────────────────────────
SIZE_GATE         = 10000  # chars; guarantees ≥100 sentences for Benford stability
DEFAULT_RATIO     = 0.70
BENFORD_TOLERANCE = 2.0
MIN_SENTENCES     = 3
MAX_RETRIES       = 3
_VERSION          = "2.0"
_ENGINE           = "shannon_local"

# ── Log2 Lookup Table (LUT) ───────────────────────────────────────────
LOG_CACHE: dict[int, float] = {}


def _log2(n: int) -> float:
    v = LOG_CACHE.get(n)
    if v is None:
        v = math.log2(n) if n > 0 else 0.0
        LOG_CACHE[n] = v
    return v


BENFORD = {d: math.log10(1 + 1 / d) * 100 for d in range(1, 10)}

LOGICAL_WHITELIST = frozenset({
    "if", "then", "else", "because", "not", "never", "non", "perché",
    "but", "however", "although", "unless", "nor", "neither", "without",
    "no", "and", "or",
})

FILLER_PATTERNS = re.compile(
    r"^(i believe\b|i think\b|i found\b|i searched\b|i need to\b|i am\b"
    r"|let me\b"
    r"|the search (was|is|has been|returned|completed)\b"
    r"|the (query|operation|computation|script|output) (was|is|ran|has been|returned|completed|produced)\b"
    r"|no (errors?|issues?|problems?|warnings?)\b"
    r"|everything (looks?|appears?|seems?)\b)",
    re.IGNORECASE,
)

NEGATION_PARTICLES = frozenset({
    "not", "no", "never", "neither", "nor", "non",
    "cannot", "cant", "wont", "dont", "doesnt", "didnt",
    "isnt", "arent", "wasnt", "werent", "hasnt", "havent",
    "hadnt", "shouldnt", "wouldnt", "couldnt",
})

PRESERVE_PATTERNS = [
    ("code_block",  re.compile(r"```[\s\S]*?```")),
    ("inline_code", re.compile(r"`[^`\n]+`")),
    ("json_obj",    re.compile(r"\{[^{}]{10,}\}")),
    ("json_arr",    re.compile(r"\[[^\[\]]{10,}\]")),
    ("url",         re.compile(r"https?://\S+")),
    ("filepath",    re.compile(r"(?:/[\w.\-_]+){2,}")),
    ("xml_tag",     re.compile(r"<[a-zA-Z][^>]*>[\s\S]*?</[a-zA-Z]+>")),
]

_SPLIT_SENT_RE = re.compile(r"(?<=[.!?])\s+(?=[A-ZÀ-ɏ])")
_WORD_RE       = re.compile(r"[a-zA-ZÀ-ɏ']+")
_SPACE_RE      = re.compile(r" {2,}")
_APOS_RE       = re.compile(r"'")


def extract_preserved(text):
    preserved = {}
    idx = [0]

    def replacer(m, kind):
        key = f"\x00PITH_{kind}_{idx[0]}\x00"
        preserved[key] = m.group(0)
        idx[0] += 1
        return key

    for kind, pattern in PRESERVE_PATTERNS:
        text = pattern.sub(lambda m, k=kind: replacer(m, k), text)
    return text, preserved


def restore_preserved(text, preserved):
    for key, value in preserved.items():
        text = text.replace(key, value)
    return text


def split_sentences(text):
    raw = _SPLIT_SENT_RE.split(text.strip())
    result = []
    for part in raw:
        for line in part.split("\n"):
            line = line.strip()
            if len(line.split()) >= 2:
                result.append(line)
    return result


def _compute_shannon(words):
    total = len(words)
    if total == 0:
        return {}
    log_total = _log2(total)
    counts = Counter(words)
    return {w: log_total - _log2(c) for w, c in counts.items()}


def _count_negations(sentence):
    return sum(
        1 for w in _WORD_RE.findall(sentence.lower())
        if _APOS_RE.sub("", w) in NEGATION_PARTICLES
    )


def _prune_tokens(sentence, info, threshold):
    tokens = re.findall(r"[a-zA-ZÀ-ɏ']+|[^a-zA-ZÀ-ɏ']+", sentence)
    kept = []
    for tok in tokens:
        if _WORD_RE.match(tok):
            w = tok.lower()
            if w in LOGICAL_WHITELIST or info.get(w, float("inf")) >= threshold:
                kept.append(tok)
        else:
            kept.append(tok)
    return _SPACE_RE.sub(" ", "".join(kept)).strip()


def benford_mad(sentences):
    lengths = [len(s.split()) for s in sentences if s.split()]
    if len(lengths) < 5:
        return 0.0
    first_digits = [int(str(max(l, 1))[0]) for l in lengths]
    dist  = Counter(first_digits)
    total = len(first_digits)
    return round(
        sum(abs(dist.get(d, 0) / total * 100 - BENFORD[d]) for d in range(1, 10)) / 9,
        2,
    )


def compress(text, target_ratio=DEFAULT_RATIO):
    original_len    = len(text)
    original_tokens = len(text.split())

    if original_len < SIZE_GATE:
        return text, {
            "action":            "passthrough",
            "reason":            f"payload {original_len} chars < {SIZE_GATE} size gate",
            "original_tokens":   original_tokens,
            "compressed_tokens": original_tokens,
            "ratio":             1.0,
            "saved_pct":         0.0,
            "benford_mad":       0.0,
            "benford_ok":        True,
            "engine":            _ENGINE,
            "version":           _VERSION,
        }

    target_reduction = 1.0 - target_ratio

    working, preserved = extract_preserved(text)
    n_preserved = len(preserved)

    sentences = split_sentences(working)

    if len(sentences) < MIN_SENTENCES:
        return text, {
            "action":            "passthrough",
            "reason":            f"only {len(sentences)} sentences (< {MIN_SENTENCES})",
            "original_tokens":   original_tokens,
            "compressed_tokens": original_tokens,
            "ratio":             1.0,
            "saved_pct":         0.0,
            "benford_mad":       benford_mad(sentences),
            "benford_ok":        True,
            "preserved_blocks":  n_preserved,
            "engine":            _ENGINE,
            "version":           _VERSION,
        }

    original_mad = benford_mad(sentences)

    all_words  = [w.lower() for w in _WORD_RE.findall(working)]
    info       = _compute_shannon(all_words)
    all_scores = sorted(info.get(w, 0.0) for w in all_words)

    pruned            = sentences
    compressed_mad    = original_mad
    current_reduction = target_reduction

    for _attempt in range(MAX_RETRIES):
        if not all_scores:
            break

        cutoff_idx = min(int(current_reduction * len(all_scores)), len(all_scores) - 1)
        threshold  = all_scores[cutoff_idx]

        pruned = []
        for sent in sentences:
            if FILLER_PATTERNS.match(sent.strip()):
                continue

            neg_before = _count_negations(sent)
            candidate  = _prune_tokens(sent, info, threshold)
            neg_after  = _count_negations(candidate)
            if neg_before != neg_after or not candidate.strip():
                pruned.append(sent)
            else:
                pruned.append(candidate)

        candidate_mad = benford_mad(pruned)
        if original_mad > 0 and candidate_mad > original_mad * BENFORD_TOLERANCE:
            current_reduction *= 0.5
            continue

        compressed_mad = candidate_mad
        break
    else:
        compressed_mad = benford_mad(pruned)

    compressed_working = " ".join(s for s in pruned if s.strip())
    compressed_text    = restore_preserved(compressed_working, preserved)

    for key, value in preserved.items():
        if key not in compressed_working:
            compressed_text += f"\n{value}"

    compressed_tokens = len(compressed_text.split())
    ratio = round(compressed_tokens / original_tokens, 3) if original_tokens > 0 else 1.0

    meta = {
        "action":                 "compressed",
        "original_tokens":        original_tokens,
        "compressed_tokens":      compressed_tokens,
        "ratio":                  ratio,
        "saved_pct":              round((1 - ratio) * 100, 1),
        "sentences_original":     len(sentences),
        "sentences_kept":         len(pruned),
        "original_benford_mad":   original_mad,
        "compressed_benford_mad": compressed_mad,
        "benford_ok":             compressed_mad <= original_mad * BENFORD_TOLERANCE or original_mad == 0,
        "preserved_blocks":       n_preserved,
        "engine":                 _ENGINE,
        "version":                _VERSION,
    }

    wrapped = (
        f"<pith_optimization_layer version='{_VERSION}' engine='{_ENGINE}' ratio='{ratio}'>\n"
        f"{compressed_text}\n"
        f"</pith_optimization_layer>"
    )

    return wrapped, meta


def main():
    parser = argparse.ArgumentParser(
        description="PITH v2 — Inter-Agent Payload Compressor",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  echo "Your verbose agent output..." | python3 compress.py
  python3 compress.py --payload "Long text..." --ratio 0.5
  python3 compress.py --payload "Long text..." --json
        """,
    )
    parser.add_argument("--payload", type=str)
    parser.add_argument("--ratio", type=float, default=DEFAULT_RATIO)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.payload:
        text = args.payload
    elif not sys.stdin.isatty():
        text = sys.stdin.read()
    else:
        parser.print_help()
        sys.exit(1)

    text = text.strip()
    if not text:
        print('{"error": "empty input"}' if args.json else "Error: empty input", file=sys.stderr)
        sys.exit(1)

    if not 0.1 <= args.ratio <= 1.0:
        print("Error: --ratio must be between 0.1 and 1.0", file=sys.stderr)
        sys.exit(1)

    compressed, meta = compress(text, target_ratio=args.ratio)

    if args.json:
        print(json.dumps({"compressed": compressed, "meta": meta}, indent=2, ensure_ascii=False))
    else:
        benford_icon = "✓" if meta.get("benford_ok", True) else "⚠"
        action       = meta.get("action", "compressed")
        saved        = meta.get("saved_pct", 0)
        b_mad        = meta.get("compressed_benford_mad", meta.get("benford_mad", 0))
        header       = f"[PITH v{_VERSION} | {benford_icon} | -{saved:.0f}% tokens | benford:{b_mad:.1f}% | {action}]"
        print(header)
        print(compressed)


if __name__ == "__main__":
    main()
