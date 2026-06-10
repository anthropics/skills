#!/usr/bin/env python3
"""
PITH — Inter-Agent Payload Compressor
Zipf word-density scoring + Benford structural validation

Usage:
    echo "<payload>" | python3 compress.py
    python3 compress.py --payload "<text>" --ratio 0.6
    python3 compress.py --payload "<text>" --json
"""

import sys, re, json, math, argparse
from collections import Counter

DEFAULT_RATIO      = 0.60
BENFORD_TOLERANCE  = 2.0
MIN_SENTENCES      = 5
DENSE_WORD_CHARS   = 7
MAX_RETRIES        = 3

BENFORD = {d: math.log10(1 + 1/d) * 100 for d in range(1, 10)}

STOPWORDS = set("""
a about above after again against all am an and any are as at be because been before
being below between both but by can cannot could did do does doing down during each few
for from further get got had has have having he her here him his how i if in into is it
its itself let me more most my myself no nor not of off on once only or other our out
over own same she should so some such than that the their them then there these they this
those through to too under until up very was we were what when where which while who
whose why will with would you your yours
""".split())

PRESERVE_PATTERNS = [
    ("code_block",  r"```[\s\S]*?```"),
    ("inline_code", r"`[^`\n]+`"),
    ("json_obj",    r"\{[^{}]{10,}\}"),
    ("json_arr",    r"\[[^\[\]]{10,}\]"),
    ("url",         r"https?://\S+"),
    ("filepath",    r"(?:/[\w.\-_]+){2,}"),
    ("xml_tag",     r"<[a-zA-Z][^>]*>[\s\S]*?</[a-zA-Z]+>"),
]

def extract_preserved(text):
    preserved = {}
    idx = [0]
    def replacer(m, kind):
        key = f"\x00PITH_{kind}_{idx[0]}\x00"
        preserved[key] = m.group(0)
        idx[0] += 1
        return key
    for kind, pattern in PRESERVE_PATTERNS:
        text = re.sub(pattern, lambda m, k=kind: replacer(m, k), text, flags=re.MULTILINE)
    return text, preserved

def restore_preserved(text, preserved):
    for key, value in preserved.items():
        text = text.replace(key, value)
    return text

def split_sentences(text):
    raw = re.split(r'(?<=[.!?])\s+(?=[A-Z\u0080-\uFFFF])', text.strip())
    result = []
    for part in raw:
        for line in part.split('\n'):
            line = line.strip()
            if len(line.split()) >= 2:
                result.append(line)
    return result

def zipf_density(sentence):
    words = re.sub(r'[^a-zA-Z\s]', ' ', sentence.lower()).split()
    content = [w for w in words if w not in STOPWORDS and len(w) > 2]
    if not content:
        return 0.0
    n_dense = sum(1 for w in content if len(w) >= DENSE_WORD_CHARS)
    mean_len = sum(len(w) for w in content) / len(content)
    return round(min((n_dense / len(content)) * 0.6 + min(mean_len / 12.0, 1.0) * 0.4, 1.0), 4)

def benford_mad(sentences):
    lengths = [len(s.split()) for s in sentences if s.split()]
    if len(lengths) < 5:
        return 0.0
    first_digits = [int(str(max(l, 1))[0]) for l in lengths]
    dist = Counter(first_digits)
    total = len(first_digits)
    return round(sum(abs(dist.get(d, 0) / total * 100 - BENFORD[d]) for d in range(1, 10)) / 9, 2)

def compress(text, target_ratio=DEFAULT_RATIO):
    original_tokens = len(text.split())
    working, preserved = extract_preserved(text)
    sentences = split_sentences(working)
    n_preserved = len(preserved)

    if len(sentences) < MIN_SENTENCES:
        return text, {
            "action": "passthrough",
            "reason": f"only {len(sentences)} sentences",
            "original_tokens": original_tokens,
            "compressed_tokens": original_tokens,
            "ratio": 1.0,
            "saved_pct": 0.0,
            "benford_ok": True,
            "benford_mad": benford_mad(sentences),
            "preserved_blocks": n_preserved,
        }

    scored = [(i, s, zipf_density(s)) for i, s in enumerate(sentences)]
    original_mad = benford_mad(sentences)
    keep_n = max(MIN_SENTENCES, round(len(sentences) * target_ratio))
    kept_sentences = sentences
    compressed_mad = original_mad

    for _ in range(MAX_RETRIES):
        top = sorted(scored, key=lambda x: x[2], reverse=True)[:keep_n]
        kept_indices = sorted(x[0] for x in top)
        candidate = [sentences[i] for i in kept_indices]
        candidate_mad = benford_mad(candidate)
        if original_mad > 0 and candidate_mad > original_mad * BENFORD_TOLERANCE:
            keep_n = min(len(sentences), keep_n + 2)
        else:
            kept_sentences = candidate
            compressed_mad = candidate_mad
            break
    else:
        kept_sentences = candidate
        compressed_mad = candidate_mad

    compressed_working = " ".join(kept_sentences)
    compressed_text = restore_preserved(compressed_working, preserved)
    for key, value in preserved.items():
        if key not in compressed_working:
            compressed_text += f"\n{value}"

    compressed_tokens = len(compressed_text.split())
    ratio = round(compressed_tokens / original_tokens, 3) if original_tokens > 0 else 1.0

    return compressed_text, {
        "action": "compressed",
        "original_tokens": original_tokens,
        "compressed_tokens": compressed_tokens,
        "ratio": ratio,
        "saved_pct": round((1 - ratio) * 100, 1),
        "sentences_original": len(sentences),
        "sentences_kept": len(kept_sentences),
        "original_benford_mad": original_mad,
        "compressed_benford_mad": compressed_mad,
        "benford_ok": compressed_mad <= original_mad * BENFORD_TOLERANCE or original_mad == 0,
        "preserved_blocks": n_preserved,
    }

def main():
    parser = argparse.ArgumentParser(description="PITH — Inter-Agent Payload Compressor")
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
        sys.exit(1)

    compressed, meta = compress(text, target_ratio=args.ratio)

    if args.json:
        print(json.dumps({"compressed": compressed, "meta": meta}, indent=2))
    else:
        icon = "✓" if meta.get("benford_ok", True) else "⚠"
        saved = meta.get("saved_pct", 0)
        b_mad = meta.get("compressed_benford_mad", meta.get("benford_mad", 0))
        action = meta.get("action", "compressed")
        print(f"[PITH | {icon} | -{saved:.0f}% tokens | benford:{b_mad:.1f}% | {action}]")
        print(compressed)

if __name__ == "__main__":
    main()
