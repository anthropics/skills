# Studio Output Custom Prompts — Why Defaults Are Mediocre

This reference answers exactly one decision: **why does the notebooklm skill always open the Studio customization menu and write a detailed custom prompt, and what does a good custom prompt look like per output type?**

## The Core Claim

NotebookLM's Studio generates multiple output types from your notebook's sources. As of the last verification (2026-06):

- Audio Overview (podcast-style)
- Video Overview (narrated visual explainer; customizable format and visual style)
- Mind Map
- Reports — Briefing Doc, Study Guide, FAQ, Timeline, and custom report formats
- Flashcards
- Quiz
- Infographic
- Slides (slide deck)

The UI evolves quickly — always discover the actual inventory from the live Studio panel screenshot rather than this list, and update this doc when it drifts.

**The default prompts produce mediocre output.** They are written to work across all possible source materials → they are generic by design. Generic prompts produce generic output.

The mediocre-output failure mode:
- **Audio Overview default:** generic two-host summary, 12-15 min, undifferentiated voice
- **Infographic default:** title-and-bullet panels, no decision logic, generic palette
- **Study Guide default:** definition list + bland questions, no audience calibration

**Sharp custom prompts produce dramatically better output.** The customization menu (chevron next to the main Studio button) opens a text field where you describe: angle / audience / length / style / specific structure.

## When to Use Custom Prompts

**Always.** This is non-negotiable in the notebooklm skill.

The mandatory workflow for Action 3 (Studio output):

1. Locate the specific output button (find by text — e.g., `find(text="Audio Overview")`)
2. **Open the customization menu** — the chevron/dropdown arrow next to the main button (NOT the main button itself)
3. **Write a detailed custom prompt** in the text field
4. Submit Generate

Skipping step 2-3 (clicking the main button directly) uses the default prompt. The skill refuses to do this.

## Custom Prompt Anatomy

A good custom prompt specifies:

| Element | Why |
|---|---|
| **Audience** | Drives jargon level + assumed background |
| **Angle** | What perspective / lens to apply (e.g., business vs technical) |
| **Length** | Prevents bloat or thinness |
| **Structure** | Specific layout (panels, slides, sections) |
| **Style** | Tone, voice, formality |
| **Examples / counter-examples** | Concrete anchors |

A weak prompt has 1-2 of these. A strong prompt has 4-5.

## Per-Output-Type Custom Prompt Templates

### Audio Overview

**Default fails because:** generic two-host conversational tone, undefined audience, often 12-15 min (too long), surface-level coverage.

**Good custom prompt:**

> "Two-host conversation between a researcher and an experienced practitioner. Audience: [non-technical executive | technical lead | undergraduate student | general public]. Length: 8-10 minutes. Focus on [business implications | technical mechanism | historical evolution | practical applications]. Include one concrete example per major point. Acknowledge counter-arguments briefly. End with one specific takeaway, not a generic summary."

**Pattern:**
- Two-host setup (specify roles, not just "two hosts")
- Audience explicit
- Length tight
- Focus angle picked
- Concrete-example requirement
- Counter-argument requirement
- Specific closing instruction

### Infographic

**Default fails because:** generic title-and-bullets, no decision logic, oversize panel count, neutral palette.

**Good custom prompt:**

> "Decision-tree style. Action-oriented (each panel ends with a decision or action the viewer takes). 6 panels max. Monochrome navy with amber highlight on the action line. Each panel has: title (4-6 words), 1-2 sentence body explaining the situation, decision/action line in amber. No filler panels. Last panel: 'next step' with specific URL/contact/resource."

**Pattern:**
- Style (decision-tree vs storytelling vs comparison vs process)
- Action-orientation
- Panel count cap (6 is the sweet spot; 8+ becomes unreadable)
- Color palette
- Per-panel structure
- Closing call-to-action

### Study Guide

**Default fails because:** definition list + bland recall questions, no audience calibration, no Bloom higher-order discipline.

**Good custom prompt:**

> "[Undergraduate | Graduate | Professional] level — define every technical term if undergrad, assume fluency if grad. Structure: [N] concepts, each with 4 elements: (1) one-paragraph definition, (2) why this matters in practice (concrete example), (3) one worked problem, (4) 3 practice questions Bloom-higher-order (apply / analyze / evaluate; NO recall questions). Discussion questions tied to a specific learning outcome listed at the start of each section."

**Pattern:**
- Audience explicit (drives jargon + question complexity)
- Concept count specific
- Per-concept structure rigid
- Bloom-level discipline
- Learning-outcome anchoring

### Slides (Slide Deck)

**Default fails because:** dense slides, bullet-heavy, no presenter notes, generic structure.

**Good custom prompt:**

> "12 slides max. 1-2 sentences per slide body — NO bullet points in slide bodies (prose only). Per slide: include presenter notes with (a) one concrete example, (b) one likely audience objection, (c) how to address it. Title slide + 10 content slides + closing call-to-action slide. Closing slide: specific next step (not 'thank you')."

**Pattern:**
- Slide count cap (12 max for executive audience)
- Body density rule (1-2 sentences, no bullets)
- Presenter notes mandatory + structured
- Title + content + close structure
- Closing call-to-action (not generic 'thank you')

### Briefing Doc

**Default fails because:** generic memo structure, no key-decisions section, undifferentiated length.

**Good custom prompt:**

> "Audience: [executive / board / investor / partner]. Length: [1 page / 2 pages / 5 pages]. Structure: (1) BLUF (bottom line up front, 2 sentences max), (2) Key findings (3-5 numbered), (3) Decisions needed from this audience (numbered, with options + recommendation), (4) Open questions (3 max), (5) Suggested next step (1 specific action). Tone: [neutral analytical / persuasive / cautionary]."

### Timeline

**Default fails because:** chronological dump with no significance annotation.

**Good custom prompt:**

> "Milestone-focused (not event-dump). [N] milestones max. Per milestone: date, milestone (one phrase), significance (one sentence — why this changed the field). Order: reverse-chronological [or chronological if historical narrative]. Group into 3-4 eras with era-level summary at each boundary. Exclude minor events that don't shift the trajectory."

### FAQ

**Default fails because:** generic Q&A pairs, no audience-calibrated answer depth.

**Good custom prompt:**

> "Audience: [internal team / customer / external stakeholder]. 8-12 questions. Each answer: 2-3 sentences max. Question phrasing: how the audience would actually ask it (not how the topic owner would write it). Group into 3 categories. Include 2-3 'difficult question' entries (objections / concerns) — handle them directly, not evasively."

### Mind Map

**Default fails because:** generic radial spread with no priority hierarchy.

**Good custom prompt:**

> "Central concept: [name]. 3-5 primary branches (the major dimensions). Each branch: 2-4 sub-branches. Max depth: 3 levels (central → branch → sub-branch). Use noun phrases for branches (not full sentences). Mark 2-3 sub-branches as 'critical' (the highest-leverage points). Skip details that don't connect back to a critical sub-branch."

### Table of Contents (legacy — folded into Reports in current UI)

**Default fails because:** literal section dump, no annotation.

**Good custom prompt:**

> "Structure: section number + section title + 1-sentence summary of what the section covers. Length: 8-15 sections. Group into 2-3 parts with part-level summary at each boundary. Mark 2-3 sections as 'start here' for newcomers."

## Anti-Patterns

### Click the main Studio button (default prompt)

The most common skill failure. Always open customization menu.

### Generic custom prompt

> "Make a good infographic about my notebook."

This is a default prompt with extra words. Specify audience / angle / length / structure / style.

### Over-detailed custom prompt

> "Use exactly the color #1A3A5C for headers, then #E8F0F8 for table headers, with Arial 12pt body, then..."

NotebookLM's Studio engine doesn't honor pixel-precise design specs. Stay at the level of "monochrome navy with amber highlight," not exact hex codes.

### Custom prompt for the wrong output type

> Asked for Audio Overview, wrote a custom prompt about visual design.

Match prompt content to output type. Audio prompt → audio direction; visual prompt → visual direction.

### Custom prompt that contradicts source material

> "Generate an infographic showing my notebook's positive findings about X" — when the notebook has mixed findings.

Studio outputs source-grounded content. Custom prompts shape **how** content is presented, not what content exists. Force-skew via custom prompt produces inaccurate output.

## Operational Checklist (Per Studio Output Generation)

- [ ] Q4 (custom prompt direction) collected from user
- [ ] Studio panel located via find() (not pixel coordinates)
- [ ] Specific output button located (not the panel header)
- [ ] **Customization menu opened** (chevron, NOT main button)
- [ ] Custom prompt written: audience + angle + length + structure + style
- [ ] Custom prompt run through `scripts/custom_prompt_template_generator.py` for starter if needed
- [ ] Generate button clicked
- [ ] Confirmation screenshot taken
- [ ] User notified: "Generation in progress — NotebookLM will notify you when ready" (for slow ops)

## Citations (7 sources)

1. **Google NotebookLM documentation + product blog posts (2024-2026).** Source for the Studio output catalog and the customization menu existence. Google has progressively added customization since Audio Overview launched.

2. **Anthropic's prompt engineering guide — docs.anthropic.com.** Source for the audience-angle-length-structure-style anatomy of effective prompts. The pattern transfers from Claude prompting to NotebookLM Studio prompting.

3. **Refactoring UI — Adam Wathan & Steve Schoger (2018).** Source for visual-output design discipline (panel-count caps, palette restraint, action-orientation). The Infographic and Slides templates apply this discipline.

4. **Carmine Gallo, *Talk Like TED* (2014).** Source for the slide-deck structure (12-max, 1-2 sentences per slide, presenter notes with examples + objections). Gallo's analysis of top TED talks formalizes the discipline.

5. **Patrick Lencioni, *The Five Dysfunctions of a Team* (2002).** Source for the BLUF (bottom line up front) discipline used in Briefing Doc template. Executive briefings front-load the decision.

6. **Bloom's revised taxonomy — Anderson & Krathwohl (2001).** Source for the Study Guide's Bloom-higher-order discipline (apply / analyze / evaluate / create). Connects to research-pack's discussion question canon.

7. **Edward Tufte, *Visual Display of Quantitative Information* (1983, 2001 2nd ed.).** Source for the data-ink ratio discipline applied to Infographic + Timeline templates. Tufte's "small multiples" and "milestone discipline" inform the per-panel and per-milestone structures.
