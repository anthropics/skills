# Writing Quality Check

## Purpose

A set of writing quality rules extracted from common patterns in AI-generated text. These are **good writing rules** that apply regardless of whether the text was AI-generated or human-written. The goal is better prose, not detection evasion.

> **Design boundary**: This checklist improves writing quality. It is NOT a humanizer. We do not aim to fool AI detectors. We aim to produce clear, precise, varied academic prose.

Reference this checklist during the self-review step of drafting (draft_writer_agent Step 2.7, report_compiler_agent final check).

---

## A. High-Frequency Term Warnings

The following terms appear disproportionately in AI-generated text. They are not banned — but when you encounter one, ask: **"Is this really the most precise word here, or am I defaulting to it?"**

### Flagged Terms

| Term | Why it's flagged | Better alternatives (context-dependent) |
|------|-----------------|----------------------------------------|
| delve | Overused as "explore" substitute | examine, investigate, analyze, explore |
| tapestry | Cliché metaphor for complexity | network, interplay, system, landscape |
| landscape | Vague when not literal | field, domain, context, state of |
| pivotal | Inflation of importance | important, significant, central, key |
| crucial | Same as above | essential, necessary, critical, vital |
| foster | Vague verb | promote, develop, cultivate, encourage |
| showcase | Non-academic register | demonstrate, illustrate, present, reveal |
| testament | Cliché | evidence, indicator, demonstration |
| navigate | Vague when not literal | manage, address, handle, negotiate |
| leverage | Business jargon | use, employ, utilize, apply |
| realm | Archaic/poetic | domain, field, area, sphere |
| embark | Overwrought for "begin" | begin, initiate, undertake, start |
| underscore | Overused emphasis verb | emphasize, highlight, stress, reinforce |
| multifaceted | Vague complexity claim | complex, varied, diverse, multilayered |
| nuanced | Often vacuous | subtle, detailed, fine-grained, qualified |
| comprehensive | Often unjustified | thorough, extensive, broad, detailed |
| robust | Vague quality claim | reliable, strong, rigorous, resilient |
| intricate | Same problem as multifaceted | complex, detailed, elaborate, involved |
| cornerstone | Cliché metaphor | foundation, basis, core element, pillar |
| paradigm | Overused outside philosophy of science | framework, model, approach (exception: "paradigm shift" in philosophy of science is standard) |
| synergy | Business jargon | interaction, cooperation, combined effect |
| holistic | Vague without definition | comprehensive, integrated, whole-system |
| streamline | Non-academic | simplify, optimize, improve efficiency |
| cutting-edge | Cliché | recent, advanced, state-of-the-art, novel |
| groundbreaking | Inflation | novel, innovative, pioneering, original |

### Exception Rule

If a flagged term is **standard terminology in the target discipline**, it is exempt:
- "paradigm shift" in philosophy of science → OK
- "landscape" in ecology/geography (literal) → OK
- "robust" in statistics ("robust estimator") → OK
- "navigate" in wayfinding research (literal) → OK

---

## B. Punctuation Pattern Control

### Em Dash (—)
- **Limit**: ≤ 3 per paper total, recommend 0-1
- **Why**: AI text overuses em dashes for parenthetical asides. Academic writing typically uses commas, parentheses, or separate sentences instead
- **Fix**: Replace with commas, parentheses, or restructure into separate sentences
- **Exception**: Direct quotes from sources retain their original punctuation

### Semicolons
- **Limit**: ≤ 2 per 1000 words
- **Why**: AI text chains independent clauses with semicolons where a period would be clearer
- **Fix**: Use a period and start a new sentence. Reserve semicolons for closely related parallel structures

### Colon-List Sequences
- **Rule**: Avoid 2+ consecutive paragraphs that each open with a colon followed by a list
- **Why**: Creates a monotonous enumerate-everything pattern
- **Fix**: Integrate list items into prose, or use a single consolidated list

---

## C. Throat-Clearing Openers

Delete the following sentence starters. Cut to the point.

| Throat-clearing phrase | What to do |
|-----------------------|-----------|
| "In the realm of..." | Delete. Start with the actual subject |
| "It's important to note that..." | Delete. If it's important, the content speaks for itself |
| "It is worth mentioning that..." | Same as above |
| "In today's rapidly evolving..." | Delete. Timestamped clichés add no information |
| "This serves as a testament to..." | Replace with direct claim: "This demonstrates..." or just state the evidence |
| "It goes without saying that..." | If it goes without saying, don't say it |
| "In order to..." | Replace with "To..." |
| "It should be noted that..." | Delete. Just note it |
| "As a matter of fact..." | Delete. State the fact |
| "When it comes to..." | Replace with the subject directly: "X shows..." |
| "At the end of the day..." | Delete. Colloquial and vague |
| "With that being said..." | Delete or use "However" if a contrast is intended |

### Meta-Commentary to Avoid

Also watch for sentences that describe what the paper is doing instead of doing it:
- "This section will discuss..." → Just discuss it
- "The following paragraph examines..." → Just examine it
- "We now turn our attention to..." → Just turn to it

Exception: Roadmap sentences in the Introduction ("Section 2 reviews the literature; Section 3 describes the methodology") are standard academic practice and should be kept.

---

## D. Structure Pattern Warnings

### Rule of Three Compulsion
- **Pattern**: Every argument has exactly 3 sub-points, every list has exactly 3 items
- **Why**: Real analysis doesn't always decompose into trios. Two strong points beat three padded ones
- **Fix**: Use as many points as the evidence warrants. 2 is fine. 5 is fine. Don't pad to 3

### Uniform Paragraph Length
- **Pattern**: All paragraphs are approximately the same length (150-200 words each)
- **Why**: Natural writing has paragraph length variation. Short paragraphs for emphasis, longer ones for complex arguments
- **Fix**: Vary paragraph length. A 2-sentence paragraph after a 10-sentence paragraph creates rhythm

### Synonym Cycling
- **Pattern**: Using 3+ different synonyms for the same concept within one paragraph to avoid repetition
- **Why**: In academic writing, consistent terminology is a virtue. Swapping "students" → "learners" → "participants" → "subjects" within one paragraph confuses rather than impresses
- **Fix**: Pick one term per concept per section. Repeat it. Technical repetition is clarity, not weakness

### Binary Contrast Overuse
- **Pattern**: "Not X. Y." or "It's not about X — it's about Y." used more than twice per paper
- **Why**: This rhetorical device is effective once. Repeated, it becomes a tic
- **Limit**: ≤ 2 per paper

### Mirror Structure
- **Pattern**: Every section has the same internal structure (topic sentence → 3 evidence points → synthesis sentence)
- **Why**: Creates a template-stamped feel. Different sections serve different purposes and should have different internal rhythms
- **Fix**: Let section structure follow content needs. Methods can be procedural. Discussion can be exploratory

---

## E. Burstiness (Sentence Length Variation)

### What to Check
Good writing has **natural variation in sentence length**. Short sentences create impact. Longer sentences develop complex ideas. The alternation creates rhythm.

### Detection Rule
If 5+ consecutive sentences all fall within a narrow word-count range (e.g., all between 20-25 words): **flag for review**.

### How to Fix
- Insert a short sentence (≤ 10 words) to break the pattern
- Combine two short sentences into one complex one if the pattern is monotonously short
- Read the paragraph aloud — if it feels metronomic, vary it

### Burstiness Targets (by section)
- **Abstract**: Moderate variation (factual, steady pace)
- **Introduction**: High variation (hook with short sentences, build with long ones)
- **Literature Review**: Moderate (steady analytical pace, occasional short synthesis)
- **Methods**: Low variation acceptable (procedural sections naturally have uniform length)
- **Results**: Moderate (short for key findings, longer for detailed descriptions)
- **Discussion**: Highest variation (short for emphasis, long for interpretation, very short for conclusions)

---

## How to Use This Checklist

### During Drafting (Preferred)
Apply rules **while writing each section** in the self-review sub-step (Step 2.7 in draft_writer_agent). This catches issues before they propagate.

### During Final Review (Fallback)
If not applied during drafting, run a full-paper sweep before handoff to citation_compliance_agent.

### Scoring (Internal, Not Reported to User)
For each rule category, track violations:
- 0 violations: Clean
- 1-3 violations: Minor — fix in self-review
- 4+ violations: Pattern issue — review the section's writing approach

Do NOT report scores to the user. Just fix the issues silently during drafting.
