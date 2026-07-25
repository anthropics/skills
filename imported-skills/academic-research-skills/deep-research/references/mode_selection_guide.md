# Mode Selection Guide

## Overview

deep-research provides 8 modes suited to different research stages and needs. This guide helps users select the most appropriate mode.

---

## Decision Flowchart

```
User Input
    │
    ├── Have a clear research question?
    │   ├── Yes ──→ Have a text to review?
    │   │            ├── Yes ──→ review mode
    │   │            └── No ───→ Need PRISMA-compliant systematic review / meta-analysis?
    │   │                         ├── Yes ──→ systematic-review mode
    │   │                         └── No ───→ Need a complete report?
    │   │                                     ├── Yes ──→ full mode
    │   │                                     └── No ───→ Only need literature?
    │   │                                                 ├── Yes ──→ Need rapid paper comparison?
    │   │                                                 │            ├── Yes ──→ three-way-scan mode
    │   │                                                 │            └── No ───→ lit-review mode
    │   │                                                 └── No ───→ quick mode
    │   │
    │   └── No ──→ Want guided thinking?
    │              ├── Yes ──→ socratic mode
    │              └── No ───→ full mode
    │                          (Phase 1 interactive RQ clarification)
    │
    ├── Only need to verify specific facts?
    │   └── Yes ──→ fact-check mode
    │
    └── Not sure what you need?
        └── Describe your situation → System auto-recommends a mode
```

---

## Detailed Mode Information

### full mode (Complete Research)

| Item | Description |
|------|------|
| **Applicable Scenario** | Need to conduct complete academic research from scratch, producing a citable research report |
| **Not Applicable** | Just need a quick understanding of a topic; already have complete research and only need review; only need a bibliography |
| **Typical Users** | Graduate students preparing thesis proposals, policy researchers writing analysis reports, scholars exploring new fields |
| **Expected Output** | Complete APA 7.0 report (3,000-8,000 words), including literature review, methodology, analysis, conclusions |
| **Expected Dialogue Rounds** | 2-5 rounds (Phase 1 interaction + checkpoints) |
| **Agents Activated** | All 9 |
| **Time Required** | Longer; suitable for in-depth research without time pressure |

**Trigger Examples**:
```
"Research the impact of AI on higher education quality assurance"
"Deep research on the impact of declining birth rates on Taiwan's higher education"
"Research the current state of SDGs implementation in Asian universities"
```

---

### quick mode (Quick Research)

| Item | Description |
|------|------|
| **Applicable Scenario** | Need a quick understanding of a topic's core viewpoints and key literature, under time constraints |
| **Not Applicable** | Need complete methodology design; need in-depth critical analysis; need publication-quality reports |
| **Typical Users** | Administrative staff preparing meeting background materials, researchers needing a quick literature scan, preliminary exploration before writing a proposal |
| **Expected Output** | Research brief (500-1,500 words), including key summary, major literature, preliminary viewpoints |
| **Expected Dialogue Rounds** | 0-1 round (typically direct output) |
| **Agents Activated** | 4 (RQ + Biblio + Verification + Report) |
| **Time Required** | Shorter |

**Trigger Examples**:
```
"Quick research on blockchain in education"
"Quick research on the latest trends in educational technology"
```

---

### review mode (Text Review)

| Item | Description |
|------|------|
| **Applicable Scenario** | Already have a paper/report/draft that needs professional review and feedback |
| **Not Applicable** | No text to review yet; need to write research from scratch; need literature search |
| **Typical Users** | Graduate students who finished a paper and need peer review feedback, self-check before journal submission, peer review |
| **Expected Output** | Review report with Editorial Verdict (Accept/Revise/Reject), specific revision suggestions, ethics review |
| **Expected Dialogue Rounds** | 0-1 round |
| **Agents Activated** | 3 (Editor + Devil's Advocate + Ethics) |
| **Time Required** | Medium, depends on text length |

**Trigger Examples**:
```
"Review this paper"
"Help me review this paper's methodology"
"Check this manuscript before submission"
```

---

### lit-review mode (Literature Review)

| Item | Description |
|------|------|
| **Applicable Scenario** | Need systematic literature search and synthesis analysis, but not a complete research report |
| **Not Applicable** | Need a complete report with original analysis; only need to verify a few facts; need methodology design |
| **Typical Users** | Graduate students writing the literature review chapter of their thesis, research teams conducting systematic reviews, coursework assignments |
| **Expected Output** | Annotated bibliography + synthesis analysis (1,500-4,000 words), including thematic classification, evidence matrix, research gaps |
| **Expected Dialogue Rounds** | 1-2 rounds (confirm search scope) |
| **Agents Activated** | 3 (Biblio + Verification + Synthesis) |
| **Time Required** | Medium |

**Trigger Examples**:
```
"Literature review on SDGs in higher education"
"Literature review: the evolution of quality assurance in Taiwan's higher education"
"Systematic review of AI-assisted assessment"
```

---

### three-way-scan mode (WHY / HOW / WHAT paper comparison)

| Item | Description |
|------|------|
| **Applicable Scenario** | Need a disciplined shortlist of papers compared in a stable WHY/HOW/WHAT frame, lighter than a full literature review |
| **Not Applicable** | Need a complete evidence matrix, thematic synthesis, or PRISMA-like coverage (escalate to `lit-review` / `systematic-review`); need to verify specific facts (`fact-check`) |
| **Typical Users** | Researchers scoping a new area, students triaging a reading list, anyone deciding which papers to read in depth |
| **Expected Output** | Per-paper WHY/HOW/WHAT shortlist + cross-paper synthesis (common WHY, divergent HOW, strongest WHAT, unresolved gap) (800-2,000 words) |
| **Expected Dialogue Rounds** | 1-2 rounds (confirm candidate set) |
| **Agents Activated** | 2 (Biblio + Verification, retrieval + compact extract) |
| **Time Required** | Low-Medium |

**Trigger Examples**:
```
"Compare these papers in WHY/HOW/WHAT format"
"Quick 3W scan of recent LLM-evaluation papers"
"Which of these should I read first?"
```

---

### fact-check mode (Fact-Checking)

| Item | Description |
|------|------|
| **Applicable Scenario** | Need to verify the truthfulness and source quality of specific factual claims |
| **Not Applicable** | Need complete research analysis; need literature synthesis; need to produce a research report |
| **Typical Users** | Verifying data cited in meetings, checking factual accuracy in reports, checking policy claims |
| **Expected Output** | Verification report (300-800 words), including source rating, factual accuracy assessment, credibility determination |
| **Expected Dialogue Rounds** | 0 rounds (direct output) |
| **Agents Activated** | 1 (Source Verification) |
| **Time Required** | Shortest |

**Trigger Examples**:
```
"Fact-check these claims about Taiwan's university enrollment"
"Fact-check: Is the number of universities in Taiwan really declining?"
"Verify: 'OECD countries average 50% tertiary attainment rate'"
```

---

### socratic mode (Guided Research)

| Item | Description |
|------|------|
| **Applicable Scenario** | Interested in a topic but unsure how to start research; want to clarify thinking through dialogue; need research guidance |
| **Not Applicable** | Already have a clear research question and methodology; need quick report output; only need literature or fact-checking |
| **Typical Users** | Master's students encountering research for the first time, scholars transitioning research fields, doctoral students brainstorming research proposals |
| **Expected Output** | Research Plan Summary with extracted INSIGHTs, research question direction, methodology suggestions |
| **Expected Dialogue Rounds** | 8-15 rounds (multi-round dialogue is the core feature) |
| **Agents Activated** | 2-3 (socratic_mentor + research_question + devils_advocate as needed) |
| **Time Required** | Longer, but the focus is on the thinking process rather than output speed |

**Trigger Examples**:
```
"Guide my research on higher education topics"
"Guide my research on educational technology"
"Help me think through my thesis direction"
"Help me think through my research topic"
「引導我的研究：高教品保」
「幫我釐清我的研究方向」
「幫我想想，我對少子化議題有興趣但不確定要研究什麼」
「我有個模糊的想法，想找研究題目」
「帶我做研究」
```

---

### systematic-review mode (Systematic Review / Meta-Analysis)

| Item | Description |
|------|------|
| **Applicable Scenario** | Need a PRISMA-compliant systematic review, potentially with meta-analysis; evidence synthesis for policy or clinical decisions |
| **Not Applicable** | Exploratory research without a focused PICOS question; narrative literature review; quick overview of a topic |
| **Typical Users** | Researchers conducting Cochrane-style reviews, doctoral students writing systematic review chapters, policy teams synthesizing evidence for guidelines |
| **Expected Output** | PRISMA 2020 report: protocol, flow diagram, risk of bias assessment, forest plot data (if meta-analysis), GRADE evidence table, full reference list |
| **Expected Dialogue Rounds** | 3-6 rounds (protocol review + screening decisions + synthesis decisions) |
| **Agents Activated** | 8-10 (RQ + Architect + Biblio + Verification + RoB + Meta-Analysis/Synthesis + Report + Editor + Ethics) |
| **Time Required** | Longest; systematic reviews are inherently comprehensive |

**Trigger Examples**:
```
"Systematic review of AI-assisted assessment in higher education"
"Meta-analysis of the effect of active learning on STEM outcomes"
"PRISMA review of quality assurance frameworks in Asian universities"
"Evidence synthesis on the impact of accreditation on institutional improvement"
```

---

## Common Misselection Scenarios

| What the User Says | What They Probably Need | Recommended Mode | Reason |
|-----------|------------------|---------|------|
| "Help me do a complete literature review" | Complete report (with analysis and conclusions) | `full`, not `lit-review` | lit-review only produces bibliography and synthesis, no original analysis |
| "Quickly check the situation with X" | Fact-checking | `fact-check`, not `quick` | If only needing to verify specific facts, fact-check is more precise |
| "I want to research X" / 「我想研究X」(but can't articulate what they want to know) | Research thinking clarification | `socratic`, not `full` | full mode's Phase 1 also offers interaction, but socratic goes deeper |
| "Help me fix this paper" | Paper revision guidance | `review`, not `full` | Already has text, needs review not research from scratch |
| "I need APA-formatted references" | Reference formatting | `lit-review`, not `full` | If only a reference list and formatting is needed, no complete research required |
| "Help me think of a research topic" / 「幫我想研究題目」 | Research direction exploration | `socratic` | Best suited for users without a clear direction |
| "Systematic review of X" | PRISMA-compliant review | `systematic-review`, not `lit-review` | lit-review is a narrative survey; systematic-review follows PRISMA protocol with risk of bias and optional meta-analysis |
| "I need a meta-analysis" | Quantitative evidence synthesis | `systematic-review` | Meta-analysis is a component of systematic review, not a standalone mode |
| "Literature review for my thesis chapter" | Narrative literature review | `lit-review`, not `systematic-review` | Thesis lit review chapters are typically narrative, not PRISMA-compliant |

---

## Mode Transitions

### Common Transition Paths

```
socratic → full              Continue with complete research after Socratic completion
socratic → academic-paper    Write paper directly after Socratic completion
lit-review → full            Want complete analysis after literature review
lit-review → systematic-review  Need formal PRISMA compliance after initial lit survey
fact-check → full            Need deeper research after fact-checking
quick → full                 Worth going deeper after quick research
review → full                Need to re-research after review
systematic-review → academic-paper  Write up systematic review as a paper
```

### deep-research to academic-paper Mode Mapping

| deep-research Mode | Output | Maps to academic-paper Mode | Description |
|-------------------|------|--------------------------|------|
| `full` | Complete research report | `full` or `revision` | Research complete, proceed to paper writing |
| `socratic` | Research Plan Summary | `plan` | Research direction determined, plan paper structure |
| `lit-review` | Annotated bibliography + synthesis | `full` (literature-based) | Literature review complete, start writing paper |
| `quick` | Research brief | `plan` (needs expansion) | Preliminary exploration complete, plan full paper |
| `review` | Review report | Does not map | Review concluded, revise original paper |
| `fact-check` | Verification report | Does not map | Fact-checking concluded |
| `systematic-review` | PRISMA report + forest plots + GRADE table | `full` (systematic review paper) | Systematic review complete, write as a journal article |

### deep-research vs academic-paper-reviewer Mode Mapping

| deep-research `review` mode | academic-paper-reviewer |
|------------------------------|------------------------|
| 3 agents (Editor + DA + Ethics) | Dedicated paper review skill |
| Suitable for quality review of any text | Designed specifically for academic paper review process |
| Produces Editorial Verdict | Produces structured review comments |
| Recommended for: initial draft screening, non-academic texts | Recommended for: formal pre-submission review |

---

## Complete Academic Research Pipeline

```
Step 1: deep-research (socratic/full)
          ↓ Research Plan / Full Report
Step 2: academic-paper (plan/full)
          ↓ Paper draft
Step 3: academic-paper-reviewer (full/guided)
          ↓ Review comments
Step 4: academic-paper (revision)
          ↓ Revised paper
Step 5: [Repeat Steps 3-4 until passed]
          ↓ Final paper
```

---

## Mode Transition Matrix

Rules for switching between modes mid-research. Not all transitions are safe.

### Transition: quick → full
- **When**: Quick brief reveals the topic is more complex than expected
- **Reusable**: RQ Brief (as-is), initial keyword list
- **Must Redo**: Full literature search (quick only uses 5-8 sources), synthesis, verification
- **Quality Delta**: Full mode requires 15+ sources, 3+ databases, formal methodology design

### Transition: lit-review → full
- **When**: Literature review reveals a gap worth investigating with original methodology
- **Reusable**: Complete bibliography, synthesis themes, evidence gap analysis
- **Must Redo**: Research design (methodology_patterns), data collection plan, ethics review (if primary research)
- **Quality Delta**: Full mode adds original research design; lit-review is secondary analysis only

### Transition: socratic → full
- **When**: Socratic dialogue produces a well-formed RQ and user wants autonomous research
- **Reusable**: RQ Brief (with socratic_insights), accumulated INSIGHTs, scope definition
- **Must Redo**: Everything after RQ formulation (bibliography, synthesis, verification, report)
- **Quality Delta**: socratic mode only produces RQ Brief; full mode executes the complete pipeline

### Transition: fact-check → full
- **When**: Fact-checking reveals a claim is part of a larger contested topic worth researching
- **Reusable**: Verified/debunked claims, source verification results
- **Must Redo**: RQ formulation (reframe from verification to inquiry), full bibliography, synthesis
- **Quality Delta**: Fact-check is binary (true/false/mixed); full mode produces nuanced analysis

### Transition: lit-review → systematic-review
- **When**: Literature review reveals the topic warrants formal PRISMA compliance (e.g., for publication in a journal that requires it)
- **Reusable**: Initial keyword strategy, some identified sources (need re-screening)
- **Must Redo**: Protocol registration, formal inclusion/exclusion criteria, dual screening, risk of bias assessment, meta-analysis feasibility assessment
- **Quality Delta**: systematic-review requires protocol, RoB assessment, GRADE; lit-review has none of these

### Transition: systematic-review → academic-paper
- **When**: Systematic review is complete and user wants to write it up as a journal article
- **Reusable**: Everything — PRISMA report is essentially the paper draft
- **Must Redo**: Formatting to target journal requirements, abstract restructuring
- **Quality Delta**: Minimal — systematic review output is already structured per PRISMA 2020

### Prohibited Transitions
- **full → quick**: Cannot downgrade a full research to quick brief (loss of rigor)
- **Any → socratic**: Socratic mode is an entry point only; cannot transition into it mid-pipeline
- **paper-review → full**: Paper review evaluates existing work; full mode creates new research. These are fundamentally different tasks
