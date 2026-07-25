# Example: Exploratory Research — Full Pipeline

## User Request
```
Research the impact of AI on higher education quality assurance
```

## Phase 1: SCOPING

### research_question_agent Output

**Topic Area**: Artificial intelligence applications in higher education quality assurance

**Primary Research Question**:
> How are artificial intelligence technologies being integrated into higher education quality assurance processes, and what are the emerging benefits, risks, and institutional implications?

**FINER Assessment**:
| Criterion | Score | Justification |
|-----------|-------|---------------|
| Feasible | 4/5 | Growing literature base; accessible through academic databases |
| Interesting | 5/5 | Rapidly evolving area at intersection of two major sectors |
| Novel | 4/5 | Few comprehensive reviews exist; most studies are case-specific |
| Ethical | 4/5 | Raises important AI ethics questions but not inherently harmful |
| Relevant | 5/5 | Directly informs QA agency strategy and policy |
| **Average** | **4.4/5** | |

**Scope Boundaries**:
- In scope: AI/ML applications in institutional/program accreditation, learning analytics for QA, automated assessment, AI in self-evaluation
- Out of scope: AI in teaching/learning (unless directly connected to QA), AI plagiarism detection (separate literature), specific vendor products
- Key assumptions: Focus on post-secondary education; "quality assurance" includes both internal QA and external accreditation

**Sub-questions**:
1. What AI technologies are currently being applied or piloted in HE quality assurance?
2. What benefits and risks do stakeholders report from AI integration in QA?
3. What institutional and policy implications arise from AI-augmented QA processes?

### research_architect_agent Output

**Research Paradigm**: Pragmatist (mixed evidence types, applied orientation)
**Method**: Systematic literature review with thematic synthesis
**Data Strategy**: Secondary data (academic literature + grey literature from QA agencies)
**Analytical Framework**: Thematic analysis organized by sub-questions
**Validity Criteria**: Comprehensive search, transparent inclusion criteria, PRISMA reporting

### devils_advocate_agent — CHECKPOINT 1

**Verdict**: PASS (with minor notes)
- Minor: RQ is broad — consider whether "emerging" limits to recent literature only
- Minor: Define "quality assurance" explicitly (internal vs. external, process vs. outcome)
- Observation: Fast-moving field means any review may be quickly outdated

## Phase 2: INVESTIGATION

### bibliography_agent Output

**Search Strategy**: 4 databases (Scopus, Web of Science, ERIC, Google Scholar), keywords: "artificial intelligence" AND "quality assurance" AND "higher education", date range: 2019-2025, English and Chinese languages.

**PRISMA Flow**: 847 identified -> 612 after dedup -> 89 screened -> 31 full-text -> 22 included

**Annotated Bibliography** (excerpt):
1. **Zawacki-Richter, O., et al. (2019). Systematic review of research on artificial intelligence applications in higher education. *International Journal of Educational Technology in Higher Education*, *16*(1), 39. https://doi.org/10.1186/s41239-019-0171-0**
   - Relevance: Foundational mapping of AI in HE
   - Key Findings: AI predominantly used in profiling/prediction, assessment, adaptive learning
   - Quality: Level V (systematic review of descriptive studies)

2. **Sanchez-Prieto, J.C., et al. (2024). AI-enhanced quality assurance: A framework for European higher education. *Quality in Higher Education*, *30*(1), 45-62.**
   - Relevance: Directly addresses AI+QA intersection
   - Key Findings: Proposed framework with 4 dimensions; stakeholder acceptance varies
   - Quality: Level VI (framework paper with case illustrations)

[... 20 more sources ...]

### source_verification_agent Output

**Sources Reviewed**: 22 | **Verified**: 20 | **Flagged**: 2 | **Rejected**: 0

**Flagged**:
1. Source #14 — Moderate COI (author is CTO of an AI-QA startup)
2. Source #19 — Currency concern (2019 review may not reflect post-GPT developments)

## Phase 3: ANALYSIS

### synthesis_agent Output

**Key Themes**:
1. **AI Application Typology** (Strong evidence, 15 sources): Categorization, analytics, automation, prediction
2. **Benefits: Efficiency & Scale** (Moderate evidence, 9 sources): Reduced reviewer burden, faster turnaround, larger data processing
3. **Risks: Bias & Transparency** (Moderate evidence, 8 sources): Algorithmic bias, black-box decisions, accountability gaps
4. **Institutional Readiness** (Emerging evidence, 5 sources): Capacity building, infrastructure, cultural resistance
5. **Policy Frameworks** (Emerging evidence, 4 sources): Regulation, standards, governance models

**Key Contradiction**: Sources disagree on whether AI reduces or amplifies bias in QA — resolution depends on implementation design and oversight mechanisms.

**Knowledge Gaps**: Limited evidence from Global South; few longitudinal studies; no studies on student perception of AI in QA.

### devils_advocate_agent — CHECKPOINT 2

**Verdict**: PASS
- Minor: Technology-positive framing detected — ensure risks are given equal weight
- Observation: Most evidence comes from European/North American contexts

## Phase 4: COMPOSITION

### report_compiler_agent Output

[Full APA 7.0 report, ~5,200 words]

Title: Artificial Intelligence in Higher Education Quality Assurance: A Systematic Review of Applications, Benefits, Risks, and Institutional Implications

[Abstract, Introduction, Literature Review, Methodology, Findings (organized by 5 themes), Discussion, Limitations, Conclusion, References (22 sources)]

## Phase 5: REVIEW

### editor_in_chief_agent Output

**Verdict**: Minor Revision (Score: 3.7/5.0)
- Strength: Comprehensive search, well-organized themes
- Major: Discussion section needs stronger connection between findings and existing QA theory
- Minor: Some inconsistency in citation format (3 references)
- Minor: Abstract exceeds 250-word limit

### ethics_review_agent Output

**Verdict**: CLEARED
- AI disclosure present and accurate
- All references spot-checked (5/22 = 23%) — all verified
- Dual-use risk: Low
- Fair representation: Adequate (noted geographic limitation)

### devils_advocate_agent — CHECKPOINT 3

**Verdict**: PASS
- Observation: Conclusion recommendation #3 ("QA agencies should adopt AI tools") is stronger than evidence warrants — suggest hedging
- "So what?" test: Passed — clear implications for QA practice

## Phase 6: REVISION

### report_compiler_agent (Revision 1)

**Changes**:
1. Discussion section expanded with QA theory connections (Major, Editor)
2. 3 citation format errors corrected (Minor, Editor)
3. Abstract trimmed to 248 words (Minor, Editor)
4. Recommendation #3 hedged: "should consider piloting" (Observation, Devil's Advocate)

**Final Word Count**: 5,450 words
**Revision Loops Used**: 1 of 2

---

## Final Output Summary
- Full APA 7.0 report: 5,450 words
- 22 cited sources (Levels I-VII)
- 5 thematic findings
- 3 recommendations
- Ethics cleared
- 1 revision loop completed
