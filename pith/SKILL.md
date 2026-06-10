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

---

## Quick Start

```bash
echo "<verbose agent output>" | python3 scripts/compress.py
python3 scripts/compress.py --payload "<text>" --ratio 0.6
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

raw = agent_a.run(task)
compressed, meta = pith(raw)
agent_b.run(compressed)
```

---

## What PITH Preserves vs Compresses

**Always preserved:** ` ```code blocks``` `, JSON, URLs, file paths, numbers.
**Compressed:** verbose reasoning, redundant repetition, transitional filler.

---

## The Benford Signal

| MAD | Interpretation |
|-----|----------------|
| < 4% | Highly natural |
| 4–6% | Normal |
| 6–9% | Moderate deviation |
| > 9% | ⚠ Check output |

---

## Limitations

- Requires ≥ 5 sentences (shorter = passthrough)
- Zipf word-length proxy is an approximation
- Not for legally sensitive exact-phrasing content
