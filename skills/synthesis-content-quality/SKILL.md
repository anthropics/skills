---
name: synthesis-content-quality
description: >
  A 27-point quality framework for evaluating and improving AI-assisted content.
  Use for content quality, AI content, quality check, writing quality, editorial
  review, content review, AI slop detection, content improvement, and publishing
  standards.
license: CC0-1.0
metadata:
  author: Rajiv Pant
  version: 1.0.0
---

# Content Quality

A systematic methodology for developing high-quality AI-assisted content and identifying content that falls short. This framework defines 27 criteria organized into confidence tiers for evaluating whether AI-assisted content meets professional publishing standards.

## When to Use This Skill

- Reviewing AI-assisted drafts before publication
- Editing content that may contain unrevised AI output
- Building or calibrating AI content detection tools
- Training writers or editors on AI content quality standards
- Performing editorial review of submitted content

## Core Philosophy

AI-assisted content creation is legitimate and valuable. The distinction that matters is between:

- **Unedited AI output:** Raw generation copied and published without human refinement
- **AI-augmented work:** Human expertise enhanced by AI capabilities, with proper oversight
- **Systematic human-AI collaboration:** Methodical integration where humans maintain judgment, add genuine expertise, and ensure quality

The goal is quality assessment, not origin detection. No single indicator proves AI generation definitively. Detection requires pattern recognition across multiple indicators.

## The 27 Quality Criteria

Each criterion is tagged with its confidence tier: **[HIGH]**, **[MED]**, or **[LOW]**.

### Language and Tone Patterns

1. **Undue Emphasis on Importance and Symbolism** [MED] -- Inflating significance with phrases like "stands as a testament to" or "plays a vital role in." Fix: describe subjects accurately rather than inflating importance.

2. **Promotional and Travel Brochure Language** [MED] -- Marketing copy tone with "rich cultural heritage," "breathtaking," "nestled in the heart of." Fix: replace promotional adjectives with specific, factual descriptions.

3. **Editorial Commentary and Meta-Analysis** [MED] -- Injecting interpretation with "it's important to note," "notably," "one cannot overlook." Fix: state facts and trust readers to determine importance.

4. **Superficial Analysis with Participial Phrases** [MED] -- Sentences ending with "-ing" phrases adding shallow commentary: "highlighting its commitment to sustainability." Fix: provide real analysis with evidence, or let the statement stand alone.

5. **Negative Parallelism** [MED] -- Overusing "not X but Y" constructions: "not just a place to eat, but a cornerstone of community." Fix: use this structure sparingly and only for genuine contrast.

6. **Overuse of Transition Words** [LOW] -- Excessive "Moreover," "Furthermore," "Additionally" placed mechanically. Fix: let ideas connect through logical flow; vary transitions.

7. **Section-Ending Summaries** [MED] -- Explicit summary phrases: "In summary," "Overall," "In essence." Fix: remove these; if a section needs a summary to be understood, restructure it.

8. **The Rule of Three** [MED] -- Formulaic grouping in threes: "innovative, impactful, and transformative." Fix: vary list lengths; let content dictate structure.

9. **Passive Voice and "Has Been Described As"** [LOW] -- Overreliance on "is widely regarded as," "has been praised for." Fix: use direct statements with specific attribution.

10. **Uniform Sentence and Paragraph Length** [MED] -- Mechanically consistent structure without natural variation. Fix: vary deliberately -- short sentences for emphasis, longer ones for complexity.

### Style and Structural Indicators

11. **Excessive Em Dashes** [LOW] -- Overusing em dashes where commas, parentheses, or colons fit better. Fix: match punctuation to function.

12. **Bulleted Lists with Bolded Lead-ins** [MED] -- Formulaic bullets with "**Term**: explanation" structure throughout. Fix: vary list formats; sometimes prose serves better than a list.

13. **Excessive Bolding and Formatting** [LOW] -- Mechanical bolding of every "important" term. Fix: bold sparingly. If everything is emphasized, nothing is.

14. **Emoji Usage in Inappropriate Contexts** [LOW] -- Emojis in formal content where they do not belong. Normal in casual content; a tell in formal contexts.

15. **Markdown Formatting Mixed with Standard Text** [HIGH] -- Raw Markdown syntax (asterisks, backticks, hash headers) appearing in published content.

16. **Curly vs. Straight Quotes** [LOW] -- Inconsistent quote styles or wrong type for context.

17. **Title Case in Headers** [LOW] -- Every major word capitalized instead of sentence case, especially in journalism contexts.

### Technical and Formatting Tells

18. **Placeholder Text and Incomplete Elements** [HIGH] -- Bracketed placeholders like `[Insert source here]` or `[Citation needed]` left in published content.

19. **Chatbot Communication Artifacts** [HIGH] -- Salutations, valedictions, knowledge cutoff disclaimers, or offers to assist further appearing in published content.

20. **Broken or Fabricated Links and Technical Codes** [HIGH] -- URLs leading to 404 errors, invalid DOIs/ISBNs, or ChatGPT-specific artifacts like "turn0search0." Verify all links and identifiers.

21. **Citation Abnormalities** [MED] -- Citations repeated without proper reference tagging, real sources cited for unrelated content, or generic "According to experts..." without naming them.

22. **Suspiciously Long Edit Summaries** [MED] -- Unusually formal, comprehensive edit summaries in first-person paragraphs on platforms with edit tracking.

### Citation and Sourcing Issues

23. **Hallucinated Citations** [HIGH] -- Fabricated sources, misattributed quotes, non-existent journal articles with plausible-sounding titles. This is among the most dangerous AI content problems.

24. **Vague Attribution to Unnamed Authorities** [MED] -- "Experts say," "Studies have shown," "Research indicates" without specific attribution. Professional standard requires verifiable sources.

### Context-Specific Indicators

25. **Industry-Specific Slop Patterns** [MED] -- Domain-characteristic AI patterns: "innovative, cutting-edge" in tech; "hidden gem" in travel; "synergy, leverage" in business; uniformly positive product reviews.

26. **Lack of Personal Detail or Specificity** [MED] -- Generic descriptions without specific examples, personal anecdotes, or experiential details. Humans who have experienced something provide sensory details and concrete examples.

27. **Superficial Depth Without Expertise** [MED] -- Covering topics broadly without demonstrating actual understanding. Restating common knowledge, using technical terms superficially, avoiding nuance, lacking case studies.

For detailed explanations, examples, and fix guidance for each criterion, see [references/detailed-criteria.md](references/detailed-criteria.md).

## Confidence-Based Evaluation Process

### Step 1: Scan for High-Confidence Indicators

Check for: hallucinated citations, chatbot artifacts, placeholder text, raw Markdown formatting, broken/fabricated links, multiple indicators clustering together.

If any are present: very likely unedited AI output.

### Step 2: Count Medium-Confidence Indicators

- 3-4 present: likely AI-generated
- 5+ present: very likely AI-generated

### Step 3: Assess Overall Pattern

- Uniform structure + promotional tone + shallow analysis = strong AI signal
- Specific details + personal voice + varied structure = human-written

### Step 4: Consider Context

- Is this from an established author with a portfolio?
- Does other work by this author show similar patterns?
- Is the publication known for quality control?

## Ineffective Detection Methods

These do NOT reliably signal AI generation:

- **Perfect grammar** -- Skilled humans and professional editors produce polished prose
- **"Bland" prose** -- Corporate communications from humans can sound formulaic
- **Common phrases** -- "Rich cultural heritage" exists in human writing too
- **Em dashes** -- Professional human writers use them frequently
- **Technical terminology** -- Experts naturally use jargon

## Systematic Revision Process for Creators

When using AI to assist content creation, revise through these five passes:

1. **Eliminate formulaic patterns** -- Vary sentence/paragraph length, reduce mechanical rule of three, remove promotional language and editorial commentary, replace generic descriptions with specifics.

2. **Add genuine expertise and experience** -- Include personal anecdotes and specific observations, provide depth beyond surface-level analysis, take clear positions with genuine reasoning.

3. **Verify and enhance sourcing** -- Check all citations are real and relevant, add specific attribution, include original research or first-hand sources. Use the synthesis-fact-checking skill for thorough verification.

4. **Inject personality and voice** -- Use natural transitions, vary rhetorical structures, include humor or perspective where appropriate, let imperfections remain if they sound natural.

5. **Apply the Human Touch test** -- Would a reader recognize this as distinctly yours? Does it include knowledge only you would have? Does it sound like how you actually write?

## Quick-Reference Checklist

### High-Risk Phrases

- "stands as a testament to," "plays a vital/significant role"
- "rich cultural heritage," "breathtaking," "nestled in the heart of"
- "it's important to note," "it is worth mentioning," "one cannot overlook"
- "not only... but also," "it's not just X, it's Y"
- "Moreover," "Furthermore," "Additionally," "Nevertheless"
- "In summary," "In conclusion," "Overall," "In essence"

### Structural Checks

- [ ] Sentences vary in length naturally
- [ ] Paragraphs vary in size
- [ ] Does not group everything in threes
- [ ] Transitions feel natural, not mechanical
- [ ] No section-ending summaries
- [ ] Formatting is strategic, not excessive
- [ ] Citations verify and are relevant
- [ ] Voice and personality are present
- [ ] Includes specific examples and details
- [ ] Demonstrates genuine expertise
- [ ] No placeholder text or artifacts
- [ ] No chatbot communication remnants

### The Human Touch Test

Before publishing AI-assisted content:

1. Would a reader recognize this as distinctly mine?
2. Does it include knowledge only I would have?
3. Does it sound like how I actually write?
4. Would anyone else write it exactly this way?
5. Have I added genuine value beyond what AI provided?

If you cannot answer yes to most of these, revise further.
