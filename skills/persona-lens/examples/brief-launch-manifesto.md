# Example brief — Pour-over kettle launch manifesto, through the Steve Jobs lens

## Input brief

> We're launching a new pour-over kettle. Need a 200-word manifesto for the
> announcement page. Tone: calm conviction. Target reader: a coffee enthusiast
> who already owns a basic kettle.

## Lens body (excerpt from `patterns/lenses/founders/steve-jobs.md`)

```yaml
slug: steve-jobs
bucket: founders
patterns:
  signature_moves: ["one-more-thing reveal", "less but better", "demos > slides"]
  pillars: ["focus", "simplicity", "vertical integration"]
  vocabulary: ["insanely great", "magical", "delight"]
  voice: "calm conviction, demos > claims, second-person ('you')"
  anti_patterns: ["committee design", "speeds-and-feeds marketing", "fear-of-missing-out tactics"]
```

## CLI

```bash
bash scripts/lens-apply.sh \
  --lens steve-jobs \
  --brand-dna examples/brand-dna-sample.md \
  --use-case manifesto \
  --user-input "We're launching a new pour-over kettle for coffee enthusiasts."
```

## What the script composes

The output is a structured prompt with these sections (sent to your LLM of choice):

```
You are writing in the voice and frame of {lens.slug}.
Voice rule: {lens.patterns.voice}
Pillars: {lens.patterns.pillars}
Signature moves: {lens.patterns.signature_moves}
Anti-patterns to avoid: {lens.patterns.anti_patterns}
Vocabulary to favor: {lens.patterns.vocabulary}

Brand DNA: {brand-dna body}

Use-case: manifesto (200 words, announcement page, calm conviction).

Brief: {user-input}

Now write the manifesto.
```

## Why this composition works

- **Voice rule + signature moves + anti-patterns** prime the LLM to mimic the lens's *form*, not just topic.
- **Brand DNA** anchors the manifesto to *your* product, not a hypothetical Apple product.
- **Use-case scaffold** ("manifesto", 200 words) gives the LLM a strict shape.
- **First-principles digest** (run `persona-lens.sh digest --bucket founders` if you have ≥5 founder lenses) gives you the meta-template that's stronger than any single lens.

## Fusion variant

```bash
bash scripts/persona-lens.sh fuse --a steve-jobs --b rick-rubin --slug jobs-rubin
bash scripts/lens-apply.sh --lens jobs-rubin --use-case manifesto --user-input "..."
```

The hybrid lens body merges patterns from both parents — Jobs's `calm conviction + demos > slides` meets Rubin's `minimalism + receptive > assertive`. Useful when neither lens alone captures the voice you want.
