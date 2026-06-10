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
license: Complete terms in LICENSE.txt
---

# PITH — Inter-Agent Payload Compressor

> *Compresses what agents say to each other — the gap no other tool fills.*

Removes token waste from agent-to-agent handoffs. Uses Zipf word-density scoring to rank
sentences by information content, Benford's Law as a structural integrity validator, and
a feedback loop that prevents over-compression from damaging meaning.

---

## Origin

PITH was created by **Albert** ([@VjAlbert](https://github.com/VjAlbert)), a developer
and builder of Claude skills with a background in **game theory** and **Benford's Law**.

The motivation came from a simple observation: every existing compression tool targets
either the input (LLMLingua) or the output (Caveman). The enormous token payload exchanged
*between* agents in a pipeline — tool results, reasoning traces, intermediate context —
was being passed raw and untouched.

From a game theory perspective, this is a deviation from equilibrium. In any multi-player
system, the Nash equilibrium of communication is the strategy where each agent transmits
the minimum information necessary for the next agent to act optimally. Every token above
that minimum is pure cost.

The mathematical insight: Zipf's Law governs which words carry information (rare = dense),
and Benford's Law governs whether compressed text still has the statistical signature of
natural writing. Together they form a compression-validation loop that is principled,
fast, and requires no model calls.

The empirical test confirmed it: human text has Benford MAD of 3–5%. AI-generated and
over-compressed text deviates to 7–14%. PITH's Benford gate prevents compression from
crossing that threshold.

---

## Quick Start

```bash
# Compress via stdin
echo "<verbose agent output>" | python3 scripts/compress.py

# With explicit ratio
python3 scripts/compress.py --payload "<text>" --ratio 0.6

# JSON output with metadata
python3 scripts/compress.py --payload "<text>" --json
```

---

## When to Use PITH

| Situation | Action |
|-----------|--------|
| Agent A output > 300 tokens → passes to Agent B | Compress before handoff |
| Tool result includes verbose preamble + actual data | Compress — JSON/code preserved |
| Growing context window in multi-step pipeline | Compress each intermediate result |
| Reasoning trace forwarded downstream | Compress — core logic survives |
| Payload < 5 sentences | Skip — PITH passes through automatically |
| Pure code / pure JSON | Skip — PITH detects and passes through |

---

## Compression Modes

| Flag | Ratio | Best For |
|------|-------|----------|
| `--ratio 0.8` | Conservative | Sensitive reasoning, first pass |
| `--ratio 0.6` | **Default** | Most agent tool results |
| `--ratio 0.4` | Aggressive | Bulk search results, summaries |
| `--ratio 0.3` | Maximum | Context window critical |

---

## Output Format

```
[PITH | ✓ | -42% tokens | benford:4.3% | compressed]
<compressed payload here>
```

| Field | Meaning |
|-------|---------|
| `✓` / `⚠` | Benford validation passed / structure warning |
| `-42%` | Token reduction achieved |
| `benford:4.3%` | MAD from Benford distribution (< 6% = natural) |
| `compressed` / `passthrough` | Action taken |

---

## JSON Output

```bash
python3 scripts/compress.py --payload "<text>" --json
```

```json
{
  "compressed": "<compressed text>",
  "meta": {
    "action": "compressed",
    "original_tokens": 487,
    "compressed_tokens": 284,
    "ratio": 0.583,
    "saved_pct": 41.7,
    "sentences_original": 22,
    "sentences_kept": 13,
    "original_benford_mad": 3.91,
    "compressed_benford_mad": 4.42,
    "benford_ok": true,
    "preserved_blocks": 2
  }
}
```

---

## Python Integration

```python
import subprocess, json

def pith(payload: str, ratio: float = 0.6) -> tuple[str, dict]:
    result = subprocess.run(
        ["python3", "scripts/compress.py", "--ratio", str(ratio), "--json"],
        input=payload, capture_output=True, text=True
    )
    data = json.loads(result.stdout)
    return data["compressed"], data["meta"]

# In your pipeline
raw = agent_a.run(task)
compressed, meta = pith(raw)
print(f"Saved {meta['saved_pct']:.0f}% tokens | Benford: {'✓' if meta['benford_ok'] else '⚠'}")
agent_b.run(compressed)
```

---

## What PITH Preserves vs Compresses

**Always preserved (never touched):**
` ```code blocks``` `, `` `inline code` ``, JSON objects/arrays, URLs, file paths,
XML/HTML tags, numbers and measurements.

**Compressed:**
Verbose reasoning, redundant context repetition, transitional filler,
restatements of prior conclusions, elaboration on points already established.

---

## The Benford Signal

| MAD | Interpretation |
|-----|----------------|
| < 4% | Highly natural — compression was gentle |
| 4–6% | Normal range for most text |
| 6–9% | Moderate — acceptable |
| > 9% | ⚠ Check compressed output |

When MAD exceeds 2× the original's MAD, PITH automatically relaxes the compression
ratio and retries (up to 3 attempts). The compressor cannot produce output more
structurally artificial than its input.

---

## How It Works

1. **Parser** — Extracts code, JSON, URLs, paths, numbers. Quarantined, never touched.
2. **Zipf Scorer** — Scores each sentence: words ≥ 7 chars = rare = high information.
   Keeps top N% by density score.
3. **Benford Gate** — Validates compressed MAD vs original MAD. Relaxes + retries if
   threshold exceeded.
4. **Reassembler** — Restores original sentence order. Reinserts preserved blocks.
   Adds metadata header.

---

## Limitations

- Requires ≥ 5 sentences (shorter payloads pass through automatically)
- Zipf word-length proxy is an approximation — semantic importance may differ from
  lexical rarity in edge cases
- Not suitable for content where exact phrasing is legally or contractually required
- Benford validation most reliable on 8+ sentence outputs
