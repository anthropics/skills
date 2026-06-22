---
name: pith
description: >
  PITH compresses inter-agent payloads to eliminate token waste in multi-agent pipelines.
  Use this skill whenever an agent produces verbose output that will be passed to another
  agent — tool results, reasoning traces, search summaries, intermediate context.
  Trigger on: "compress this for the next agent", "pith this output", "slim down this
  payload", "reduce context before passing", "this tool result is too long", "optimize
  this handoff", or any time intermediate agent output exceeds ~300 tokens and will be
  forwarded downstream. Also trigger PROACTIVELY when orchestrating chains of agents and
  noticing intermediate results growing large — do not wait to be asked.
  PITH preserves all code blocks, JSON, URLs, file paths, and numbers without touching them.
  Compresses only natural language using Shannon local information scoring (I(w) = log2(total)
  - LOG_CACHE[count(w)]), validated by Benford's Law structural integrity check. Typical
  savings: 25–50% on verbose agent outputs exceeding 10 000 characters. Payloads below
  10 000 characters pass through unchanged (< 1ms). Zero external dependencies.
---

# PITH v2 — Inter-Agent Payload Compressor

PITH compresses inter-agent payloads to eliminate token waste in multi-agent pipelines. Use this tool whenever an agent produces verbose output that will be passed to another agent — tool results, reasoning traces, search summaries, or intermediate context.

The compression engine targets natural language using **Shannon local information scoring**, dynamically validated by a **Benford's Law structural integrity check**.

## Why 10 000 Characters?

`SIZE_GATE = 10000` for two independent reasons:

**Benford statistical stability:** MAD is reliable only over ≥ 50–100 sentences. At ~80–100 chars/sentence, 10 000 chars ≈ 100–125 sentences — the minimum for a low-variance MAD estimate. Below this floor, a single outlier sentence can move MAD several percentage points, causing false-positive Benford rollbacks.

**Compute ROI:** Shannon scoring, threshold lookups, whitelist checks, and polarity checksums have per-token overhead. On a 500-char payload this overhead exceeds savings. On 10 000+ chars, overhead is amortized across hundreds of tokens and net reduction (25–50%) far outweighs cost.

Payloads below the gate return in < 1ms with zero processing.

## Core Pillars

* **Typical Savings:** 25–50% reduction on verbose agent outputs (payloads ≥ 10 000 chars).
* **Zero Dependencies:** No external libraries, no API calls, works completely offline.
* **Safety First:** Perfectly preserves all code blocks, inline code, JSON objects/arrays, URLs, file paths, XML/HTML tags, and numbers.

## Mathematical Foundation

1. **Shannon Local Information:** $I(w) = \log_2(\text{total}) - \log_2(\text{count}(w))$. Rare words carry more information; common words are pruned. LOG_CACHE LUT provides O(1) log2 lookup.
2. **Adaptive Token Pruning:** `threshold = all_scores[int(reduction × N)]`. Token kept if `I(w) >= threshold` (>= is critical — avoids degenerate bulk-pruning of rare words sharing identical scores).
3. **Logical Whitelist:** `if/not/never/nor/and/or` unconditionally kept.
4. **Polarity Micro-Checksum:** Negation particle count checked before/after pruning per sentence; mismatch triggers local raw passthrough.
5. **Benford's Law MAD Gate:** If `MAD_compressed > 2 × MAD_original`, halve reduction and retry (max 3 attempts). The 10 000-char floor guarantees statistical stability.
6. **Meta-Context Receptor:** Output wrapped in `<pith_optimization_layer version='2.0' engine='shannon_local' ratio='...'>`.

## Invocation & CLI Reference

Run from the skill's root directory:

```bash
# Default (70% keep ratio)
python3 scripts/compress.py --payload "<text>"

# Explicit ratio
python3 scripts/compress.py --payload "<text>" --ratio 0.4

# JSON output with metadata
python3 scripts/compress.py --payload "<text>" --json

# Via standard input piping
echo "<verbose output>" | python3 scripts/compress.py
```

## Test Suite

```bash
# Full suite (unit tests + eval suite), from skill root
python -m pytest tests/ -v

# Unit tests only
python -m pytest tests/test_pith_v2.py -v

# Eval suite only
python -m pytest tests/test_evals.py -v
```

22 tests cover: SIZE_GATE passthrough, Shannon >= threshold, FILLER_PATTERNS, Benford gate stability, polarity protection, XML receptor.

## Passthrough Conditions

The engine automatically bypasses compression and outputs raw text if:

- Payload < 10 000 chars (size gate — ensures Benford stability and positive ROI).
- Fewer than 3 sentences after parsing.
- Input is pure JSON or pure markdown code block.
