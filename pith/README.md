# PITH — Inter-Agent Payload Compressor

> *"Why use many token when few do trick?"*
> — but make it mathematically principled.

---

## Origin

PITH was born from a conversation about compression, mathematics, and a gap nobody had filled.

Its creator — a developer with a deep interest in **game theory** and **Benford's Law** — was exploring why inter-agent communication in multi-agent AI systems was so wasteful. Caveman compressed what agents *say to users*. LLMLingua compressed what users *say to agents*. But the enormous payload exchanged *between agents* — tool results, reasoning traces, intermediate context — was being passed raw, untouched, token-heavy.

The insight came from game theory: in any multi-player system, the Nash equilibrium of communication is the strategy where each player transmits the minimum information necessary for the next player to act optimally. Every token above that minimum is a deviation from equilibrium — a pure cost with no strategic value.

The question became: *how do you find that equilibrium automatically, without destroying meaning?*

---

## The Mathematical Foundation

### Why Zipf?

George Kingsley Zipf observed in 1949 that in natural language, word frequency follows a power law: the most common word appears roughly twice as often as the second most common, three times as often as the third, and so on.

The consequence for compression is elegant: **rare words carry more information**. A sentence dense with unusual, technical, specific vocabulary is doing more work per token than a sentence full of common connectives and transitional phrases. PITH uses word length ≥ 7 characters as a zero-dependency proxy for Zipf rarity — rare words are systematically longer. No external corpus, no model call, no latency.

### Why Benford?

Frank Benford observed in 1938 that in naturally occurring datasets, the leading digit follows a logarithmic distribution: ~30% of numbers begin with 1, ~17% with 2, ~12% with 3, and so on decreasing to ~4.6% for 9.

What does this have to do with text? Sentence lengths in natural human writing follow this same distribution. Short sentences (1–9 words) are most common, then medium sentences, then long ones — and the distribution of their first digits approximates Benford's Law. This is a signature of *organic writing* — the natural rhythm of human thought.

AI-generated text and over-compressed text deviate from this signature. They tend toward uniform sentence lengths, producing a flatter distribution. The Mean Absolute Deviation (MAD) from the expected Benford distribution is therefore a structural integrity signal: low MAD = natural text, high MAD = artificial or damaged.

**Empirical validation (5 texts, 82 segments):**

| Text type | Benford MAD | Verdict |
|-----------|------------|---------|
| Darwin (1859) | 5.0% | ✓ natural |
| Melville (1851) | 3.1% | ✓ natural |
| AI scientific | 7.5% | ✗ artificial |
| AI narrative | 13.7% | ✗ artificial |

The gap between human and AI text is consistent and measurable. PITH uses this as its compression quality gate: if compression increases MAD beyond 2× the original, it relaxes the ratio and retries. The compressor cannot accidentally produce text more artificial than what it started with.

### The Game Theory Connection

In information-theoretic game theory, optimal communication strategies produce power-law distributions — this is not coincidence. Benford's Law and Zipf's Law are both manifestations of the same underlying principle: natural systems that have evolved toward efficiency follow logarithmic distributions. Language has been optimized over millennia. The distribution of sentence lengths and word frequencies reflects that optimization.

PITH's design hypothesis: **an agent communicating at its Nash equilibrium produces Benford-compliant text**. Deviation from Benford in the compressed output signals a departure from that equilibrium — either the compressor cut too much (over-compressed) or the original was already inflated (padding).

---

## What PITH Does

```
AGENT A — verbose output (487 tokens)
    ↓
┌──────────────────────────────────────────────┐
│  PITH Compression Pipeline                   │
│                                              │
│  1. PARSER                                   │
│     Extract: code, JSON, URLs, paths, nums   │
│     These are quarantined — never touched    │
│                                              │
│  2. ZIPF SCORER                              │
│     Score each sentence by vocabulary rarity │
│     Keep top 60% by density (default)        │
│                                              │
│  3. BENFORD GATE                             │
│     Compute MAD before and after             │
│     If MAD > 2× original → relax + retry    │
│     Max 3 attempts                           │
│                                              │
│  4. REASSEMBLER                              │
│     Restore original sentence order          │
│     Reinsert preserved blocks                │
│     Add metadata header                      │
└──────────────────────────────────────────────┘
    ↓
AGENT B — compressed payload (284 tokens, -42%)
[PITH | ✓ | -42% tokens | benford:4.3% | compressed]
```

---

## Installation

### As a Claude Code skill

Place the `pith/` directory in your skills folder or install the `.skill` file through Claude Code's skill manager.

### Standalone

```bash
# No dependencies required — pure Python stdlib
python3 scripts/compress.py --help
```

---

## Usage

```bash
# Basic compression
echo "<verbose agent output>" | python3 scripts/compress.py

# Explicit ratio
python3 scripts/compress.py --payload "<text>" --ratio 0.5

# JSON output for programmatic use
python3 scripts/compress.py --payload "<text>" --json
```

### In a Python pipeline

```python
import subprocess, json

def pith(payload: str, ratio: float = 0.6) -> tuple[str, dict]:
    """Compress an inter-agent payload with PITH."""
    result = subprocess.run(
        ["python3", "path/to/pith/scripts/compress.py",
         "--ratio", str(ratio), "--json"],
        input=payload, capture_output=True, text=True
    )
    data = json.loads(result.stdout)
    return data["compressed"], data["meta"]

# In your agent pipeline
raw_output = agent_research.run("Find information about X")
compressed, meta = pith(raw_output)
print(f"Saved {meta['saved_pct']:.0f}% ({meta['original_tokens']} → {meta['compressed_tokens']} tokens)")
agent_synthesis.run(compressed)
```

---

## Compression Modes

| Mode | Ratio | Best For |
|------|-------|----------|
| Conservative | `--ratio 0.8` | Sensitive reasoning traces |
| Default | `--ratio 0.6` | Most agent tool results |
| Aggressive | `--ratio 0.4` | Bulk search results, summaries |
| Maximum | `--ratio 0.3` | Context window critical |

---

## Benchmarks

| Payload type | Default ratio | Savings | Benford |
|---|---|---|---|
| Web search result (verbose) | 0.6 | 34% | ✓ |
| Web search result (aggressive) | 0.4 | 60% | ✓ |
| Code execution result + explanation | 0.6 | 30% | ✓ |
| Short payload (< 5 sentences) | — | 0% passthrough | ✓ |
| Pure JSON | — | 0% passthrough | ✓ |

---

## What Makes PITH Different

| Tool | What it compresses |
|------|--------------------|
| Caveman | Agent → User output |
| LLMLingua | User → Agent prompt |
| Selective Context | Retrieved documents |
| **PITH** | **Agent → Agent handoff payloads** |

PITH fills a specific gap: the payload exchanged *between* agents in a pipeline. This is where token waste compounds — each agent inherits the verbosity of the previous one, and over a 5-agent chain, this can mean thousands of wasted tokens before the final answer is produced.

---

## Limitations

- Requires ≥ 5 sentences for meaningful compression (shorter payloads pass through automatically)
- Zipf proxy (word length) is an approximation — semantic importance may differ from lexical rarity in edge cases
- Not suitable for legally sensitive content where exact phrasing is required
- Benford validation works best on text with 8+ sentences; shorter compressed outputs may show higher MAD

---

## Author

Created by **Albert** ([@VjAlbert](https://github.com/VjAlbert)) — developer, game theory enthusiast, and Benford's Law advocate. PITH emerged from the belief that AI multi-agent systems should communicate at their Nash equilibrium: minimum tokens, maximum information, validated by the mathematical signatures of natural language.

> *"Natural systems that evolve toward efficiency follow logarithmic distributions.
> Language did. Our agents should too."*

---

## License

MIT

## Related

- [video-analyzer](https://github.com/VjAlbert/video-analyzer) — another skill by the same author, bridging video files and Claude Projects
- [Anthropic Skills](https://github.com/anthropics/skills) — the official skills repository
