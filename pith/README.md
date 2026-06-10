# PITH — Inter-Agent Payload Compressor

> *"Why use many token when few do trick?"* — but make it mathematically principled.

---

## Origin

PITH was born from a conversation about compression, mathematics, and a gap nobody had filled.

Its creator — a developer with a deep interest in **game theory** and **Benford's Law** — was exploring why inter-agent communication in multi-agent AI systems was so wasteful. Caveman compressed what agents *say to users*. LLMLingua compressed what users *say to agents*. But the enormous payload exchanged *between agents* — tool results, reasoning traces, intermediate context — was being passed raw, untouched, token-heavy.

The insight came from game theory: in any multi-player system, the Nash equilibrium of communication is the strategy where each player transmits the minimum information necessary for the next player to act optimally. Every token above that minimum is a deviation from equilibrium — a pure cost with no strategic value.

---

## The Mathematical Foundation

### Why Zipf?

Rare words carry more information. A sentence dense with unusual, technical, specific vocabulary does more work per token than a sentence full of common connectives. PITH uses word length ≥ 7 characters as a zero-dependency proxy for Zipf rarity — no external corpus, no model call, no latency.

### Why Benford?

Sentence lengths in natural human writing follow Benford's Law distribution. Short sentences are most common, then medium, then long — and the distribution of their first digits approximates the expected logarithmic curve. AI-generated and over-compressed text deviate from this signature.

**Empirical validation (82 segments, 5 text types):**

| Text | Benford MAD | Verdict |
|------|------------|---------|
| Darwin, 1859 (human) | 5.0% | ✓ natural |
| Melville, 1851 (human) | 3.1% | ✓ natural |
| AI scientific | 7.5% | ✗ artificial |
| AI narrative | 13.7% | ✗ artificial |

PITH's Benford gate prevents compression from crossing the naturalness threshold.

### The Game Theory Connection

Optimal communication strategies produce power-law distributions. Benford's Law and Zipf's Law are both manifestations of the same underlying principle: natural systems that evolve toward efficiency follow logarithmic distributions. Language has been optimized over millennia. PITH's hypothesis: **an agent communicating at its Nash equilibrium produces Benford-compliant text**.

---

## What PITH Does

```
AGENT A — verbose output (487 tokens)
    ↓
┌──────────────────────────────┐
│  1. PARSER                   │
│     Extract code/JSON/URLs   │
│  2. ZIPF SCORER              │
│     Rank by word density     │
│  3. BENFORD GATE             │
│     Validate + retry if over │
│  4. REASSEMBLER              │
│     Restore order + blocks   │
└──────────────────────────────┘
    ↓
AGENT B — compressed (284 tokens, -42%)
[PITH | ✓ | -42% tokens | benford:4.3% | compressed]
```

---

## What Makes PITH Different

| Tool | What it compresses |
|------|--------------------|
| Caveman | Agent → User output |
| LLMLingua | User → Agent prompt |
| Selective Context | Retrieved documents |
| **PITH** | **Agent → Agent handoff payloads** |

---

## Benchmarks

| Payload type | Ratio | Savings | Benford |
|---|---|---|---|
| Web search result (verbose) | 0.6 | 34% | ✓ |
| Web search result (aggressive) | 0.4 | 60% | ✓ |
| Code execution result + explanation | 0.6 | 30% | ✓ |
| Short payload (< 5 sentences) | — | 0% passthrough | ✓ |

---

## Author

Created by **Albert** ([@VjAlbert](https://github.com/VjAlbert)) — developer, game theory enthusiast, and Benford's Law advocate.

> *"Natural systems that evolve toward efficiency follow logarithmic distributions.
> Language did. Our agents should too."*

---

## License

MIT

## Related

- [video-analyzer](https://github.com/VjAlbert/video-analyzer) — bridges video files and Claude Projects
- [Anthropic Skills](https://github.com/anthropics/skills) — the official skills repository
