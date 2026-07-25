# Orchestration Workflow — Phase Details

Detailed per-phase agent behavior and output descriptions for the 8-phase orchestration workflow.

---

## Phase 0: CONFIG (Interactive)

**Agent**: `intake_agent`
**Output**: Paper Configuration Record

- Paper type (IMRaD / Lit Review / Theoretical / Case Study / Policy Brief / Conference)
- Discipline and sub-field
- Target journal (optional)
- Citation format (APA 7 / Chicago / MLA / IEEE / Vancouver)
- Output format (LaTeX / DOCX / PDF / Markdown / Combined)
- Language (EN / zh-TW / bilingual sections)
- Bilingual abstract (Yes / EN-only / zh-TW-only)
- Word count target
- Existing materials (RQ, data, drafts, lit)

**Checkpoint**: User confirms configuration.

---

## Phase 1: RESEARCH

**Agent**: `literature_strategist_agent`
**Output**: Search Strategy + Source Corpus

- Database selection + search strings
- Inclusion/exclusion criteria
- Source screening + annotated bibliography
- Literature matrix (Source x Theme)
- Research gap mapping

**Checkpoint**: User reviews sources (optional add/remove).

---

## Phase 2: ARCHITECTURE

**Agent**: `structure_architect_agent`
**Output**: Paper Outline + Evidence Map

- Structure pattern selection (from paper_structure_patterns.md)
- Section-by-section outline with word count allocation
- Evidence-to-section assignment
- Transition logic between sections

**Checkpoint**: User approves outline.

---

## Phase 3: ARGUMENTATION

**Agent**: `argument_builder_agent`
**Output**: Argument Blueprint

- Central thesis + sub-arguments
- Claim-Evidence-Reasoning chains per section
- Counter-argument identification + rebuttal strategy
- Logical flow diagram

---

## Phase 4: DRAFTING

**Agent**: `draft_writer_agent`
**Output**: Complete Draft

- Section-by-section writing following outline
- Register adjustment for discipline
- In-text citations integrated
- Word count tracking per section
- Transition paragraphs between sections

---

## Phase 5a & 5b: CITATIONS + ABSTRACT (Parallel)

### Phase 5a: Citations

**Agent**: `citation_compliance_agent`
**Output**: Citation Audit Report

- In-text <-> reference list cross-check (zero orphans)
- Format compliance (per selected style)
- DOI/URL verification
- Self-citation ratio check
- Auto-correction of detected errors

### Phase 5b: Abstract

**Agent**: `abstract_bilingual_agent`
**Output**: Bilingual Abstract + Keywords

- English abstract (150-300 words, structured)
- Traditional Chinese abstract (300-500 characters, structured)
- EN keywords (5-7)
- zh-TW keywords (5-7)
- Independent writing (not mechanical translation)

---

## Phase 6: PEER REVIEW

**Agent**: `peer_reviewer_agent`
**Output**: Review Report + Revision Instructions

- 5-dimension scoring:
  Originality (20%) | Methodological Rigor (25%) | Evidence Sufficiency (25%)
  Argument Coherence (15%) | Writing Quality (15%)
- Verdict: Accept / Minor Revision / Major Revision / Reject
- Line-level feedback with suggested fixes
- Max 2 revision loops -> back to Phase 4 [draft_writer_agent] (limited to 1 round in academic-pipeline)

---

## Phase 7: FORMAT

**Agent**: `formatter_agent`
**Output**: Final Output Package

- Target format conversion (LaTeX + .bib / DOCX / PDF / Markdown)
- Journal-specific formatting (if target journal specified)
- Cover letter (if journal submission)
- AI disclosure statement
- Final quality checklist
