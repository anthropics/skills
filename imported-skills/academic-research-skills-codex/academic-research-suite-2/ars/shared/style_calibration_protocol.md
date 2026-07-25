# Style Calibration Protocol

## Purpose

Learns the author's natural writing voice from past writing samples and applies it as a soft guide during paper drafting. The goal is **personalization**, not de-AI-ification — the author's voice should come through in the final text, within the boundaries of discipline conventions.

> **Design boundary**: This is NOT a humanizer. We do not aim to evade AI detectors. We aim to produce text that sounds like the author wrote it, because the author's judgment and style are part of scholarly identity.

---

## When to Use

- **Primary entry point**: `academic-paper/agents/intake_agent` Step 10 (optional)
- **Pipeline carry**: `academic-pipeline` Material Passport carries the Style Profile across all stages
- **Consumers**: `academic-paper/agents/draft_writer_agent`, `deep-research/agents/report_compiler_agent`

---

## Calibration Flow

### Step 1: Sample Collection

Ask the user:
> "Do you have past papers or writing samples you'd like me to learn your style from? Providing 3+ samples helps me match your natural voice. This is optional."

**Requirements**:
- Minimum 3 samples recommended (1-2 samples produce unreliable profiles)
- Samples should be the user's own writing (not co-authored sections they didn't write)
- Same language as the target paper preferred
- Same discipline preferred but not required

**Acceptable formats**: PDF, DOCX, Markdown, plain text, pasted excerpts

### Step 2: Dimension Extraction

Analyze each sample across 6 dimensions:

#### Dimension 1: Sentence Length Distribution
- Mean word count per sentence
- Standard deviation (captures variability)
- Rhythm pattern: does the author alternate short-long, or maintain steady length?
- Example profile: `{mean: 22, stddev: 8, rhythm: "variable — mixes 8-word punchy sentences with 35-word complex ones"}`

#### Dimension 2: Paragraph Length Distribution
- Mean sentences per paragraph
- Variation across sections (e.g., shorter paragraphs in Methods, longer in Discussion)
- Example profile: `{mean_sentences: 5, variation: "moderate — 3-7 sentences, shorter in Methods"}`

#### Dimension 3: Vocabulary Preferences
- **Hedging patterns**: which hedging words does the author prefer? ("suggests" vs "indicates" vs "implies")
- **Transition words**: preferred connectives ("However" vs "Nevertheless" vs "Yet")
- **Preferred verbs**: reporting verbs for citations ("found" vs "demonstrated" vs "showed")
- **Formality level**: where on the spectrum from conversational academic to highly formal
- Example profile: `{hedging: ["suggests", "appears to", "may"], transitions: ["However", "In contrast", "Yet"], reporting: ["found", "argued", "noted"], formality: "moderate-formal"}`

#### Dimension 4: Citation Integration Style
- Narrative ratio: how often does the author use "Smith (2024) found..." vs "(Smith, 2024)"
- Citation density: average citations per paragraph
- Citation placement: beginning of paragraph (context-setting) vs end (evidence-backing)
- Example profile: `{narrative_ratio: 0.4, density: 2.3, placement: "mixed — narrative for key claims, parenthetical for supporting"}`

#### Dimension 5: Modifier Style
- Minimal vs elaborate: does the author use many adjectives/adverbs, or keep it lean?
- Abstract vs concrete: preference for abstract concepts or concrete examples?
- Example profile: `{modifier_density: "minimal — lean prose, few adjectives", abstraction: "concrete — prefers specific examples over generalizations"}`

#### Dimension 6: Register Shifts
- How does tone change across paper sections?
- Typically: Methods (neutral/procedural) → Results (descriptive) → Discussion (interpretive/assertive)
- Does the author maintain consistent register or shift noticeably?
- Example profile: `{shifts: "noticeable — cautious in Methods, increasingly assertive in Discussion, most personal voice in Conclusion"}`

### Step 3: Profile Synthesis

Combine the 6 dimensions into a **Style Profile** artifact (see `shared/handoff_schemas.md` Schema 10).

Report to the user:
> "I've analyzed your writing style from [N] samples. Key traits:
> - [1-sentence summary of most distinctive trait]
> - [1-sentence summary of second distinctive trait]
> I'll use this as a soft guide — discipline conventions always take priority."

---

## Consumption Rules — Priority System

When the Style Profile is consumed during writing, apply the following priority hierarchy:

```
Priority 1 (HARD): Discipline conventions
  → Cannot be violated. E.g., if the discipline requires third-person,
    the author's preference for first-person is overridden.

Priority 2 (STRONG): Target journal conventions
  → If the user has specified a target journal, its style norms take precedence.
    E.g., Nature requires short paragraphs; author's preference for long paragraphs is overridden.

Priority 3 (SOFT): Author's personal style
  → Applied only where it does not conflict with Priority 1 or 2.
    E.g., the author's preferred transition words, hedging patterns,
    citation integration ratio — these are safe to apply.
```

### Conflict Resolution

When personal style conflicts with discipline or journal norms:

1. **Use the norm** (Priority 1 or 2 wins)
2. **Log the conflict** in Draft Metadata:
   ```
   Style conflict: Author prefers passive voice (72% in samples),
   but target discipline (Engineering) conventions favor active voice.
   → Using active voice per discipline convention.
   ```
3. **Notify the user** (once per draft, not per instance):
   > "Note: Your typical use of [trait] differs from [discipline/journal] convention. I've followed the convention, but you can adjust manually if you prefer your style here."

### Safe Dimensions (always applicable)

These dimensions rarely conflict with norms and can be applied freely:
- Preferred transition words (within academic register)
- Hedging word choices
- Reporting verb preferences
- Citation integration ratio (narrative vs parenthetical)
- Modifier density (as long as precision is maintained)
- Sentence length variability patterns

### Risky Dimensions (check before applying)

These dimensions may conflict with discipline/journal norms:
- Voice (active vs passive) — discipline-dependent
- Paragraph length — journal-dependent
- Person (first vs third) — discipline-dependent
- Formality level — journal-dependent

---

## Edge Cases

### Insufficient Samples
If user provides < 3 samples: generate a partial profile with a warning.
> "I have a preliminary style profile from [N] sample(s), but it may not be fully representative. I'll apply it cautiously."

### Mismatched Language
If samples are in a different language than the target paper: extract transferable dimensions only (paragraph structure, citation style, modifier density). Skip vocabulary preferences.

### Co-authored Samples
If user indicates samples are co-authored: ask which sections they wrote. Analyze only those sections.

### Style Evolution
If samples span many years: weight recent samples more heavily (2x weight for samples within 2 years).
