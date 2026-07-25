#!/usr/bin/env python3
"""voice_sample_analyzer.py — Extract voice patterns from sent-email samples.

Stdlib-only. Reads 3-5 sent-email samples (separated by `---` delimiters) and
extracts deterministic voice signals:

  1. Opening phrases — first 4-6 tokens of each sample body
  2. Sign-offs       — last 4-6 tokens of each sample
  3. Sentence-length distribution — short (<10 words) / medium (10-25) / long (>25) ratio
  4. Register markers — counts of casual indicators (lol, yeah, btw, tbh) vs formal
     (I would like to, please find, kindly)
  5. Hedging frequency — counts of softeners (maybe, perhaps, I think, just)
  6. Personal pronouns — "I" vs "we" ratio
  7. Punctuation patterns — em-dashes, exclamation marks, ellipses per sample

Output: a structured patterns block that gets dropped into email-patterns.md
under "Voice Patterns (Extracted from Samples)".

NO LLM CALLS. Pure regex + frequency counting.

Limitations (intentional, stdlib-only):
  - No semantic understanding (it's surface-feature stylometry)
  - English-only register markers
  - Tokenization is whitespace-based (not linguistic)

Usage:
    python voice_sample_analyzer.py --samples-file /path/to/samples.txt
    python voice_sample_analyzer.py --samples-file /path/to/samples.txt --output json
    python voice_sample_analyzer.py --sample
"""

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List, Tuple


SAMPLE_DELIMITER_RE = re.compile(r"^\s*---+\s*$", re.MULTILINE)
SENTENCE_END_RE = re.compile(r"[.!?]+(?:\s|$)")

CASUAL_MARKERS = {
    "lol", "lmao", "haha", "yeah", "yup", "nope", "tbh", "btw", "fwiw",
    "imo", "imho", "rn", "btw", "ok", "okay", "cool", "sure", "yep",
    "gonna", "wanna", "kinda", "sorta", "dunno",
}
FORMAL_MARKERS_PHRASES = [
    "i would like to", "please find", "kindly", "i hope this email finds you",
    "i am writing to", "as per our", "at your earliest convenience",
    "thank you for your", "i look forward to hearing", "to whom it may concern",
    "respectfully", "sincerely",
]
HEDGING_MARKERS = {
    "maybe", "perhaps", "i think", "i guess", "i suppose", "just",
    "kinda", "sorta", "might", "could", "possibly", "potentially",
    "i feel", "i believe",
}


def split_samples(text: str) -> List[str]:
    """Split combined samples text on `---` delimiters; trim each."""
    parts = SAMPLE_DELIMITER_RE.split(text)
    return [p.strip() for p in parts if p.strip()]


def first_n_tokens(text: str, n: int) -> str:
    tokens = text.split()
    return " ".join(tokens[:n])


def last_n_tokens(text: str, n: int) -> str:
    tokens = text.split()
    return " ".join(tokens[-n:])


def count_phrase_occurrences(text_lower: str, phrases: List[str]) -> int:
    return sum(text_lower.count(p) for p in phrases)


def count_word_occurrences(text_lower: str, words: set) -> int:
    pattern = re.compile(rf"\b({'|'.join(re.escape(w) for w in words)})\b", re.IGNORECASE)
    return len(pattern.findall(text_lower))


def split_sentences(text: str) -> List[str]:
    parts = SENTENCE_END_RE.split(text)
    return [s.strip() for s in parts if s.strip()]


def length_bucket(word_count: int) -> str:
    if word_count < 10:
        return "short"
    if word_count <= 25:
        return "medium"
    return "long"


def analyze_sample(sample: str) -> Dict[str, Any]:
    text_lower = sample.lower()
    sentences = split_sentences(sample)
    length_dist = Counter()
    for s in sentences:
        words = s.split()
        length_dist[length_bucket(len(words))] += 1
    return {
        "opening": first_n_tokens(sample, 6),
        "sign_off": last_n_tokens(sample, 6),
        "sentence_count": len(sentences),
        "length_distribution": dict(length_dist),
        "casual_marker_count": count_word_occurrences(text_lower, CASUAL_MARKERS),
        "formal_marker_count": count_phrase_occurrences(text_lower, FORMAL_MARKERS_PHRASES),
        "hedging_count": count_word_occurrences(text_lower, HEDGING_MARKERS),
        "i_count": count_word_occurrences(text_lower, {"i", "i'm", "i've", "i'll", "i'd"}),
        "we_count": count_word_occurrences(text_lower, {"we", "we're", "we've", "we'll", "we'd", "our", "us"}),
        "em_dash_count": sample.count("—") + sample.count(" -- "),
        "exclamation_count": sample.count("!"),
        "ellipsis_count": sample.count("...") + sample.count("…"),
    }


def aggregate(per_sample: List[Dict[str, Any]]) -> Dict[str, Any]:
    if not per_sample:
        return {"error": "no samples"}
    n = len(per_sample)
    openings = [s["opening"] for s in per_sample]
    sign_offs = [s["sign_off"] for s in per_sample]
    total_sentences = sum(s["sentence_count"] for s in per_sample)
    total_lengths: Counter = Counter()
    for s in per_sample:
        total_lengths.update(s["length_distribution"])
    casual = sum(s["casual_marker_count"] for s in per_sample)
    formal = sum(s["formal_marker_count"] for s in per_sample)
    hedging = sum(s["hedging_count"] for s in per_sample)
    i_count = sum(s["i_count"] for s in per_sample)
    we_count = sum(s["we_count"] for s in per_sample)
    em_dash = sum(s["em_dash_count"] for s in per_sample)
    exclamation = sum(s["exclamation_count"] for s in per_sample)
    ellipsis = sum(s["ellipsis_count"] for s in per_sample)

    if casual > formal * 2:
        register_verdict = "casual"
    elif formal > casual * 2:
        register_verdict = "formal"
    else:
        register_verdict = "in-between"

    if total_sentences > 0:
        short_ratio = total_lengths.get("short", 0) / total_sentences
        medium_ratio = total_lengths.get("medium", 0) / total_sentences
        long_ratio = total_lengths.get("long", 0) / total_sentences
    else:
        short_ratio = medium_ratio = long_ratio = 0.0

    if short_ratio > 0.5:
        length_verdict = "one-liner / short-paragraph"
    elif long_ratio > 0.3:
        length_verdict = "longer (multi-paragraph)"
    else:
        length_verdict = "short-paragraph (medium average)"

    return {
        "sample_count": n,
        "openings": openings,
        "sign_offs": sign_offs,
        "register_verdict": register_verdict,
        "register_signals": {"casual_markers": casual, "formal_markers": formal},
        "length_verdict": length_verdict,
        "length_distribution": {
            "short_pct": round(short_ratio * 100, 1),
            "medium_pct": round(medium_ratio * 100, 1),
            "long_pct": round(long_ratio * 100, 1),
        },
        "hedging_frequency_per_sample": round(hedging / n, 2),
        "i_vs_we": {
            "i_count": i_count,
            "we_count": we_count,
            "voice": "individual" if i_count > we_count * 2 else "team" if we_count > i_count * 2 else "mixed",
        },
        "punctuation": {
            "em_dash_per_sample": round(em_dash / n, 2),
            "exclamation_per_sample": round(exclamation / n, 2),
            "ellipsis_per_sample": round(ellipsis / n, 2),
        },
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Voice analysis ({result['sample_count']} samples)")
    out.append("")
    out.append(f"Register verdict:    {result['register_verdict']}")
    out.append(f"  Casual markers:    {result['register_signals']['casual_markers']}")
    out.append(f"  Formal markers:    {result['register_signals']['formal_markers']}")
    out.append("")
    out.append(f"Length verdict:      {result['length_verdict']}")
    ld = result['length_distribution']
    out.append(f"  Short / Medium / Long: {ld['short_pct']}% / {ld['medium_pct']}% / {ld['long_pct']}%")
    out.append("")
    out.append(f"Hedging frequency:   {result['hedging_frequency_per_sample']} per sample")
    iw = result['i_vs_we']
    out.append(f"I vs We voice:       {iw['voice']} (I:{iw['i_count']}  We:{iw['we_count']})")
    out.append("")
    p = result['punctuation']
    out.append(f"Punctuation per sample: em-dash {p['em_dash_per_sample']}, ! {p['exclamation_per_sample']}, ... {p['ellipsis_per_sample']}")
    out.append("")
    out.append("Opening phrases (first 6 tokens):")
    for o in result['openings']:
        out.append(f"  - {o}")
    out.append("")
    out.append("Sign-offs (last 6 tokens):")
    for s in result['sign_offs']:
        out.append(f"  - {s}")
    out.append("")
    out.append("Output block for email-patterns.md:")
    out.append("---")
    out.append("## Voice Patterns (Extracted from Samples)")
    out.append("")
    out.append(f"- Register: {result['register_verdict']}")
    out.append(f"- Typical reply length: {result['length_verdict']}")
    out.append(f"- Hedging frequency: {result['hedging_frequency_per_sample']} per email")
    out.append(f"- Voice perspective: {result['i_vs_we']['voice']}")
    out.append(f"- Sentence-length distribution: short {ld['short_pct']}% / medium {ld['medium_pct']}% / long {ld['long_pct']}%")
    out.append("- Observed opening patterns:")
    for o in result['openings'][:5]:
        out.append(f"  - \"{o}\"")
    out.append("- Observed sign-off patterns:")
    for s in result['sign_offs'][:5]:
        out.append(f"  - \"{s}\"")
    return "\n".join(out)


SAMPLE_TEXT = """Hey, just looping back on the Q3 launch — pricing's mostly locked but I want to revisit the bundle option before we ship. Quick call tomorrow?

—Alex

---

Thanks for the proposal. Honestly, the timeline is tight and our team is heads-down on shipping. We'd need to push to Q4. Open to that?

Alex

---

Got it — sending the revised draft now. Couple of comments inline, mostly around the auth flow. Let me know what you think.

Best,
Alex

---

I'm going to pass on this one. Scope is too broad for what we can commit to in the next 6 weeks and the budget doesn't match the work involved.

Thanks for thinking of us though.

—Alex

---

Quick update: shipped the migration today, no incidents so far. Will keep an eye on it through the weekend. Lmk if you see anything weird.
"""


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--samples-file", help="Path to file containing sent-email samples separated by ---")
    parser.add_argument("--sample", action="store_true", help="Analyze embedded sample text")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        text = SAMPLE_TEXT
    elif args.samples_file:
        p = Path(args.samples_file)
        if not p.exists():
            print(f"error: {args.samples_file} not found", file=sys.stderr); return 2
        text = p.read_text(encoding="utf-8")
    else:
        parser.print_help(); return 0

    samples = split_samples(text)
    if not samples:
        print("error: no samples detected (use --- as delimiter between samples)", file=sys.stderr); return 2
    if len(samples) < 3:
        print(f"warning: only {len(samples)} sample(s) detected; recommend 3-5 for reliable patterns", file=sys.stderr)

    per_sample = [analyze_sample(s) for s in samples]
    result = aggregate(per_sample)

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
