# Translation Workflow Details

This file provides detailed guidelines for each workflow step. Steps are shared across modes:

- **Quick**: Translate only (no steps from this file)
- **Normal**: Step 1 (Analysis) → Translate
- **Refined**: Step 1 (Analysis) → Step 2 (Draft) → Step 3 (Review) → Step 4 (Revision) → Step 5 (Polish)
- **Normal → Upgrade**: After normal mode, user can continue with Step 3 → Step 4 → Step 5

All intermediate results are saved as files in the output directory.

## Step 1: Content Analysis

Before translating, analyze the source material. Save analysis to `01-analysis.md` in the output directory.

### 1.1 Content Summary

- What is this content about? What is the core argument?
- Author background, stance, and writing context
- Purpose and intended audience of the original

### 1.2 Terminology

- List technical terms, proper nouns, brand names, acronyms
- Cross-reference with loaded glossaries
- For terms not in glossary, determine standard translations
- Record in a terminology table

### 1.3 Tone & Style

- Formal or conversational? Humor, metaphor, cultural references?
- What register is appropriate for the translation given the target audience?

### 1.4 Translation Challenges

Identify what may cause difficulty in translation:

- **Comprehension gaps**: Terms or references that target readers may not understand — note what explanation is needed
- **Figurative language**: Metaphors, idioms, expressions that don't translate literally — note intended meaning and target-language approach (interpret / substitute / retain)
- **Structural challenges**: Long complex sentences, wordplay, puns, or humor that needs creative adaptation

**Save `01-analysis.md`** with:
```
## Content Summary
[Core argument, author, context, purpose]

## Terminology
[term → translation, ...]

## Tone & Style
[assessment]

## Translation Challenges
- [term/passage] → [challenge type] → [suggested approach]
- ...
```

## Step 2: Assemble Translation Prompt

Main agent reads `01-analysis.md` and assembles a complete translation prompt using [references/subagent-prompt-template.md](subagent-prompt-template.md). Inline the following from analysis:

- **Target style**: Resolved style preset + source voice assessment from §1.3
- **Content background**: Summary from §1.1
- **Glossary**: Merged glossary with analysis-extracted terms from §1.2
- **Translation challenges**: All challenges from §1.4

Save to `02-prompt.md`. This prompt is used by the subagent (chunked) or by the main agent itself (non-chunked).

## Step 3: Initial Draft

Save to `03-draft.md` in the output directory.

For chunked content, the subagent produces this draft (merged from chunk translations). For non-chunked content, the main agent produces it directly.

Translate the full content following `02-prompt.md`. Apply all **Translation principles** from SKILL.md.

## Step 4: Critical Review

The main agent critically reviews the draft against the source. Save review findings to `04-critique.md`. This step produces **diagnosis only** — no rewriting yet.

### 4.1 Accuracy

- Compare each paragraph against the original
- Verify facts, numbers, dates, proper nouns
- Flag content accidentally added, removed, or altered
- Check terminology consistency with glossary

### 4.2 Native Voice

- Flag sentences that read as "translated" rather than "written" — unnatural word order, calques, stiff phrasing
- For CJK targets: check for unnecessary connectives (因此/然而/此外), passive voice abuse (被/由/受到), noun pile-ups, over-nominalization
- Flag metaphors translated literally that sound unnatural in the target language
- Check emotional connotations are preserved, not flattened
- Note where sentence restructuring would improve readability

### 4.3 Notes & Adaptation

- Are translator's notes accurate, concise, and genuinely helpful?
- Flag missed comprehension challenges that need notes, and over-annotations on obvious terms
- Were translation strategies from `02-prompt.md` followed?
- Do cultural references work in the target language?

**Save `04-critique.md`** with:
```
## Accuracy
- [issue]: [location] — [description]

## Native Voice
- [issue]: [example] → [suggested fix]

## Notes & Adaptation
- [add/remove/revise]: [term/passage] — [reason]

## Summary
[Overall assessment: X critical issues, Y improvements]
```

## Step 5: Revision

Apply all findings from `04-critique.md` to produce a revised translation. Save to `05-revision.md`.

Read `03-draft.md` and `04-critique.md`, fix all accuracy issues, rewrite unnatural expressions, adjust notes, and improve flow.

## Step 6: Polish

Save final version to `translation.md`.

Final pass on `05-revision.md` for publication quality:

- Read the entire translation as a standalone piece — does it flow as native content?
- Smooth remaining rough transitions
- Ensure consistent narrative voice and style throughout
- Final terminology consistency check
- Verify formatting is preserved correctly

## Subagent Responsibility

Each subagent (one per chunk) is responsible **only** for producing the initial draft of its chunk (Step 3). The main agent assembles the shared prompt (Step 2), spawns all subagents in parallel, then takes over for critical review (Step 4), revision (Step 5), and polish (Step 6).

## Chunked Refined Translation

When content exceeds the chunk threshold and uses refined mode:

1. Main agent runs analysis (Step 1) on the **entire** document first → `01-analysis.md`
2. Main agent assembles translation prompt → `02-prompt.md`
3. Split into chunks → `chunks/`
4. Spawn one subagent per chunk in parallel (each reads `02-prompt.md` for shared context) → merge all results into `03-draft.md`
5. Main agent critically reviews the merged draft → `04-critique.md`
6. Main agent revises based on critique → `05-revision.md`
7. Main agent polishes → `translation.md`
8. Final cross-chunk consistency check: terminology, narrative flow, transitions at chunk boundaries
