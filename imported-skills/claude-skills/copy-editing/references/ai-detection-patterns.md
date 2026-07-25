# AI Content Detection Patterns

Reference for `ai_content_detector.py`. Explains the three detection methods and how to humanize flagged content.

## Method 1: Burstiness (sentence length variance)

**What it measures:** The coefficient of variation (CV) of sentence lengths across the text.

**Why it works:** Human writers naturally vary between short punchy sentences (4-8 words) and longer explanatory ones (20-35 words). AI tends to produce consistently medium-length sentences (12-20 words), creating a "flat" rhythm.

| CV Range | Interpretation | AI Probability |
|---|---|---|
| 0.50+ | High variance — natural human rhythm | 0-30% |
| 0.35-0.49 | Moderate variance — could be either | 30-50% |
| 0.20-0.34 | Low variance — suspiciously uniform | 50-80% |
| < 0.20 | Very flat — strong AI signal | 80-100% |

**How to fix flagged text:**
- Deliberately insert short sentences. "This matters." "Here's why."
- Break one long sentence into two short ones, then follow with a 25+ word sentence
- Use fragments where tone allows. "Not always. But often enough."
- Vary paragraph length too: alternate 1-sentence and 3-4 sentence paragraphs

## Method 2: Vocabulary diversity (Type-Token Ratio)

**What it measures:** The ratio of unique words to total words in sliding 200-word windows.

**Why it works:** AI models tend to reuse the same "safe" vocabulary — common verbs, generic adjectives, standard connectors. Human writers use more domain-specific terminology, colloquialisms, and varied word choices.

| TTR Range | Interpretation | AI Probability |
|---|---|---|
| 0.60+ | Rich vocabulary — likely human | 0-25% |
| 0.45-0.59 | Average — could be either | 25-50% |
| 0.35-0.44 | Repetitive — AI-like | 50-75% |
| < 0.35 | Very repetitive — strong AI signal | 75-100% |

**How to fix flagged text:**
- Replace generic verbs ("use", "make", "get") with specific ones ("wield", "craft", "extract")
- Add domain jargon where your audience expects it
- Vary connectors: instead of always "however", try "still", "yet", "that said", "then again"
- Remove filler phrases that inflate word count without adding meaning

## Method 3: Known AI phrases

30 phrases that appear disproportionately in LLM-generated text. These aren't wrong individually — some are perfectly fine in context — but high density signals AI origin.

**Density thresholds:**
| Density (per 1K words) | Interpretation |
|---|---|
| 0-2 | Normal range |
| 3-5 | Elevated — review flagged phrases |
| 6+ | High — likely AI-generated |

**The 10 most common AI phrases to watch:**

1. "In today's digital landscape" — replace with specific context
2. "It's worth noting that" — just state the fact
3. "Leverage" — use "use" unless specifically about financial leverage
4. "Delve into" — use "explore", "examine", or "look at"
5. "Game-changer" — use a specific description of impact
6. "Comprehensive guide" — be specific about what's covered
7. "Seamlessly integrate" — describe the actual integration
8. "Robust solution" — describe what makes it robust
9. "Cutting-edge" — name the specific advancement
10. "Empower you to" — just say what it enables

**The fix:** Replace generic AI phrases with specific, concrete language. "In today's digital landscape" → "Since Google's March 2025 core update". "Leverage AI tools" → "Use GPT-4 for first-draft outlines".

## Composite scoring

```
Composite = Burstiness × 0.35 + Vocabulary × 0.30 + Phrases × 0.35

0-20:  LIKELY_HUMAN  — no action needed
21-50: MIXED         — review flagged passages, humanize selectively
51-100: LIKELY_AI    — significant rewriting recommended
```

## Important caveats

- This is heuristic, not proof. Technical documentation often has low burstiness and TTR naturally.
- Some AI phrases are perfectly appropriate in context. Don't mechanically remove them all.
- The goal is to make content SOUND human, not to prove it IS human.
- Run this tool AFTER writing, not during — it's an editing pass, not a writing constraint.
