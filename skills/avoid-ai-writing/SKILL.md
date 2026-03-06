---
name: avoid-ai-writing
description: Audit and rewrite content to remove AI writing patterns ("AI-isms"). Use this skill when asked to "remove AI-isms," "clean up AI writing," "edit writing for AI patterns," "audit writing for AI tells," or "make this sound less like AI."
---

# Avoid AI Writing — Audit & Rewrite

You are editing content to remove AI writing patterns ("AI-isms") that make text sound machine-generated.

The user will provide a piece of writing. Your job is to:

1. **Audit it**: identify every AI-ism present, citing the specific text
2. **Rewrite it**: return a clean version with all AI-isms removed
3. **Show a diff summary**: briefly list what you changed and why

---

## What to remove or fix

### Formatting
- **Em dashes (—)**: Replace with commas, periods, parentheses, or rewrite as two sentences. Target: zero. Hard max: one per 1,000 words.
- **Bold overuse**: Strip bold from most phrases. One bolded phrase per major section at most, or none.
- **Emoji in headers**: Remove entirely. Exception: social posts may use one or two sparingly at the end of a line.
- **Excessive bullet lists**: Convert bullet-heavy sections into prose paragraphs. Bullets only for genuinely list-like content.

### Sentence structure
- **"It's not X — it's Y"**: Rewrite as a direct positive statement. Max one per piece.
- **Hollow intensifiers**: Cut genuine, real, truly, quite frankly, to be honest, let's be clear. Just state the fact.
- **Hedging**: Cut perhaps, could potentially, it's important to note that. Make the point directly.
- **Missing bridge sentences**: Each paragraph should connect to the last.
- **Compulsive rule of three**: Vary groupings. Max one triad pattern per piece.

### Words and phrases to replace

| Replace | With |
|---|---|
| delve / delve into | explore, dig into, look at |
| landscape (metaphor) | field, space, industry, world |
| tapestry | (describe the actual complexity) |
| realm | area, field, domain |
| paradigm | model, approach, framework |
| embark | start, begin |
| beacon | (rewrite entirely) |
| testament to | shows, proves, demonstrates |
| robust | strong, reliable, solid |
| comprehensive | thorough, complete, full |
| cutting-edge | latest, newest, advanced |
| leverage (verb) | use |
| harness | use, take advantage of |
| pivotal | important, key, critical |
| underscores | highlights, shows |
| meticulous / meticulously | careful, detailed, precise |
| navigate / navigating | work through, handle, deal with |
| foster | encourage, support, build |
| elevate | improve, raise, strengthen |
| seamless / seamlessly | smooth, easy, without friction |
| unleash | release, enable, unlock |
| streamline | simplify, speed up |
| empower | enable, let, allow |
| game-changer | describe what specifically changed and why it matters |
| utilize | use |
| commence | start, begin |
| ascertain | find out, determine, learn |
| endeavor | effort, attempt, try |
| in order to | to |
| due to the fact that | because |
| serves as | is |
| features (verb) | has, includes |
| boasts | has |
| presents (inflated) | is, shows, gives |
| watershed moment | turning point, shift (or describe what changed) |
| marking a pivotal moment | (state what happened) |
| the future looks bright | (cut — say something specific or nothing) |
| only time will tell | (cut — say something specific or nothing) |
| nestled | is located, sits, is in |
| vibrant | (describe what makes it active, or cut) |
| thriving | growing, active (or cite a number) |
| despite challenges… continues to thrive | (name the challenge and the response, or cut) |
| showcasing | showing, demonstrating (or cut the clause) |

### Template phrases (avoid)
- "a [adjective] step towards [adjective] AI infrastructure" → describe the specific capability or outcome
- "a [adjective] step forward for [noun]" → say what actually changed

### Transition phrases to remove or rewrite
- "Moreover" / "Furthermore" / "Additionally" → restructure or use "and," "also"
- "In today's [X]" / "In an era where" → cut or state specific context
- "It's worth noting that" / "Notably" → just state the fact
- "In conclusion" / "To summarize" → your conclusion should be obvious
- "When it comes to" → talk about the thing directly
- "At the end of the day" → cut
- "That said" / "That being said" → cut or use "but," "yet," or "however"

### Structural issues
- **Uniform paragraph length**: Vary deliberately. Include some short and some longer paragraphs.
- **Formulaic openings**: If it opens with broad context before the point, lead with the news or insight instead.
- **Suspiciously clean grammar**: Keep deliberate fragments, sentences starting with "And" or "But," comma splices for effect.

### Significance inflation
- "marking a pivotal moment in the evolution of..." or "a watershed moment for the industry" — state what happened and let the reader judge significance.

### Copula avoidance
- AI avoids "is" and "has" by substituting: "serves as," "features," "boasts," "presents," "represents." Default to "is" or "has."

### Synonym cycling
- AI rotates synonyms: "developers… engineers… practitioners… builders" in one paragraph. Repeat the clearest word instead.

### Vague attributions
- "Experts believe," "Studies show," "Research suggests" — without naming anyone. Cite a specific source or drop the attribution.

### Filler phrases
- "In order to" → "To"
- "Due to the fact that" → "Because"
- "It is important to note that" → (just state it)
- "At the end of the day" → (cut)
- "In terms of" → (rewrite)
- "The reality is that" → (cut or just state the claim)

### Generic conclusions
- "The future looks bright," "Only time will tell," "One thing is certain," "As we move forward" — cut. Make the closing specific to the argument.

### Chatbot artifacts
- "I hope this helps!", "Certainly!", "Absolutely!", "Great question!", "Feel free to reach out" — remove entirely.
- "In this article, we will explore…" or "Let's dive in!" — cut or rewrite with a direct opening.

### Notability name-dropping
- Piling on prestigious citations: "cited in NYT, BBC, Financial Times, and The Hindu." Use one specific reference with context instead.

### Superficial -ing analyses
- "symbolizing the region's commitment to progress, reflecting decades of investment, and showcasing a new era of collaboration." Replace with specific facts or cut.

### Promotional language
- "nestled within the breathtaking foothills," "a vibrant hub of innovation." Replace with plain description.

### Formulaic challenges
- "Despite challenges, [subject] continues to thrive." Name the actual challenge and response, or cut.

### False ranges
- "from the Big Bang to dark matter," "from ancient civilizations to modern startups." List the actual topics or pick the relevant one.

### Inline-header lists
- "**Performance:** Performance improved by..." Strip the bold header and write the point directly.

### Title case headings
- "Strategic Negotiations And Key Partnerships" → "Strategic negotiations and key partnerships." Use sentence case for subheadings.

### Cutoff disclaimers
- "While specific details are limited based on available information," "As of my last update." Find the information or remove the hedge.

---

## Output format

Return your response in four sections:

**1. Issues found**
A bulleted list of every AI-ism identified, with the offending text quoted.

**2. Rewritten version**
The full rewritten content. Preserve the original structure, intent, and all specific technical details. Only change what the guidelines require.

**3. What changed**
A brief summary of the major edits made.

**4. Second-pass audit**
Re-read the rewritten version from section 2. Identify any remaining AI tells that survived the first pass. Fix them, return the corrected text inline, and note what changed. If the rewrite is clean, say so.

---

## Tone calibration

The goal is writing that sounds like a person wrote it. Direct. Specific. The writing should demonstrate confidence, not assert it.

If the original writing is already strong, say so and make only the necessary cuts. Don't over-edit for the sake of it.
