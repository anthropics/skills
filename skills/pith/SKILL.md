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
  Compresses only natural language using Zipf word-density scoring, validated by Benford's
  Law structural integrity check. Typical savings: 30–60% on verbose agent outputs.
  Zero external dependencies. No API calls. Works offline.
---

# PITH — Inter-Agent Payload Compressor

PITH compresses inter-agent payloads to eliminate token waste in multi-agent pipelines. Use this tool whenever an agent produces verbose output that will be passed to another agent — tool results, reasoning traces, search summaries, or intermediate context.

The compression engine targets natural language using **Zipf word-density scoring**, which is dynamically validated by a **Benford's Law structural integrity check**. This ensures that the compressed output retains the structural statistical signature of natural prose without degrading the downstream LLM's comprehension.

## Core Pillars

* **Typical Savings:** 30–60% reduction on verbose agent outputs.
* **Zero Dependencies:** No external libraries, no API calls, works completely offline.
* **Safety First:** Perfectly preserves all code blocks, inline code, JSON objects/arrays, URLs, file paths, XML/HTML tags, and numbers.

## Mathematical Foundation

1. **Zipf Power Law:** Words with length >= 7 characters are used as a low-latency proxy for vocabulary rarity. Rare words carry higher information density per token.
2. **Benford's Law:** Sentence lengths in organic text follow a logarithmic distribution of the first digit. PITH measures the Mean Absolute Deviation (MAD). If compression corrupts the structural syntax (MAD increases > 2x), the engine automatically relaxes the compression ratio and retries (up to 3 times).

## Invocation & CLI Reference

Run from the skill's root directory:

```bash
# Default (60% keep ratio)
python3 scripts/compress.py --payload "<text>"

# Explicit ratio
python3 scripts/compress.py --payload "<text>" --ratio 0.4

# JSON output with metadata
python3 scripts/compress.py --payload "<text>" --json

# Via standard input piping
echo "<verbose output>" | python3 scripts/compress.py
```

## Passthrough Conditions

The engine automatically bypasses compression and outputs raw text if:

- The payload has fewer than 5 sentences.
- The payload is pure JSON or a pure markdown code block.
- The token count is already below the ~300 token safety threshold.
