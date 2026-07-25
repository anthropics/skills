# Handoff Example: deep-research → academic-paper

This example demonstrates how deep-research full mode, after completing research, hands off to academic-paper to begin paper writing.

---

## Scenario Setup

The user has completed deep-research full mode on the topic "AI-Assisted Quality Assurance in Higher Education: A Comparative Analysis of Implementation Strategies in East Asian Universities." Below is a summary of the research outputs.

---

## deep-research Output Summary

### 1. Research Question Brief (from research_question_agent)

```markdown
### Primary Research Question
How do East Asian universities (Taiwan, Japan, South Korea) differ in their
implementation strategies for AI-assisted quality assurance, and what factors
explain the variation in adoption patterns?

### FINER Assessment
| Criterion   | Score | Justification |
|-------------|-------|---------------|
| Feasible    | 4/5   | Public data + policy documents available |
| Interesting | 5/5   | Timely: AI policy divergence across similar systems |
| Novel       | 4/5   | Few cross-national comparisons in this space |
| Ethical     | 5/5   | No human subjects; public policy analysis |
| Relevant    | 5/5   | Directly informs HEEACT and peer agencies |
| **Average** | **4.6/5** | |

### Sub-questions
1. What AI-QA tools and frameworks have been adopted by accreditation agencies
   in Taiwan, Japan, and South Korea?
2. What institutional and policy factors facilitate or hinder AI-QA adoption?
3. To what extent do implementation outcomes align with stated policy objectives?
```

### 2. Methodology Blueprint (from research_architect_agent)

```markdown
- Paradigm: Pragmatist (comparative policy analysis)
- Method: Qualitative comparative analysis (QCA) + document analysis
- Data sources:
  - Policy documents (3 countries' QA frameworks)
  - Accreditation agency reports (HEEACT, JUAA/NIAD-QE, KCUE)
  - Published case studies and conference proceedings
- Analytical framework: Diffusion of Innovation (Rogers) +
  Institutional Isomorphism (DiMaggio & Powell)
- Validity: Triangulation across document types + member checking
  with QA practitioners
```

### 3. Annotated Bibliography (from bibliography_agent)

```markdown
23 sources identified, 18 retained after quality screening:
- 6 peer-reviewed articles (Level II-III evidence)
- 4 accreditation agency reports (Level IV)
- 3 policy documents (Level IV)
- 3 conference proceedings (Level V)
- 2 institutional case studies (Level V)

Key themes identified:
- AI adoption maturity gap (Taiwan > Korea > Japan in QA applications)
- Regulatory divergence (Japan's cautious approach vs Korea's top-down push)
- Data infrastructure as prerequisite (not just technology)
```

### 4. Synthesis Report (from synthesis_agent)

```markdown
## Core Findings

1. **Adoption patterns cluster into 3 models**:
   - Taiwan: bottom-up experimentation (agency-led pilots)
   - South Korea: top-down mandate (ministry-driven framework)
   - Japan: cautious incrementalism (voluntary guidelines)

2. **Critical success factors** (converging evidence across all 3 countries):
   - Data infrastructure maturity
   - Accreditation agency technical capacity
   - University willingness to share data
   - Clear governance framework for AI decisions

3. **Key tension**: efficiency gains vs transparency concerns
   - All 3 countries report resistance from faculty regarding "black box" decisions
   - Only Korea has attempted regulatory response (AI Ethics in Education Act 2025)

4. **Evidence gap**:
   - No rigorous outcome studies yet (all countries < 3 years into implementation)
   - Student/faculty experience data almost entirely absent

## Contradictions Identified
- Taiwan HEEACT reports "high adoption" but academic literature suggests
  most universities are still in pilot phase → definition of "adoption" varies

## Knowledge Gaps
- Impact on accreditation outcomes (pass/fail rates)
- Cost-effectiveness analysis
- Faculty perceptions and behavioral changes
```

---

## Handoff Instruction

After completing deep-research, the user inputs:

```
Now help me write a paper based on this research
```

---

## academic-paper intake_agent Auto-Detection

**intake_agent Detection Process**:

```
Scanning available materials...

[DETECTED] Research Question Brief
  - Source: deep-research / research_question_agent
  - Status: Complete (FINER 4.6/5)
  - Action: SKIP academic-paper Phase 1 (topic scoping)

[DETECTED] Methodology Blueprint
  - Source: deep-research / research_architect_agent
  - Status: Complete (pragmatist QCA + document analysis)
  - Action: SKIP academic-paper Phase 2 (methodology design)
  - Note: Will integrate into Method section directly

[DETECTED] Annotated Bibliography (18 sources, APA 7.0)
  - Source: deep-research / bibliography_agent
  - Status: Complete, quality-screened
  - Action: SKIP academic-paper literature search
  - Note: Will use as foundation for Literature Review section

[DETECTED] Synthesis Report
  - Source: deep-research / synthesis_agent
  - Status: Complete (3 core findings + 1 contradiction + 2 gaps)
  - Action: SKIP academic-paper analysis phase
  - Note: Will structure Findings and Discussion sections around synthesis

Materials Assessment: COMPREHENSIVE
Recommended academic-paper mode: full (with accelerated pipeline)
Estimated sections already covered: 60-70%
Remaining work: Writing, formatting, argumentation, and polish
```

---

## Skipped Steps and Reasons

| academic-paper Step | Normal Workflow | After Handoff | Reason |
|---------------------|---------|-----------|------|
| Phase 1: Topic Scoping | intake_agent clarifies from scratch | SKIPPED | RQ Brief is complete |
| Phase 2: Structure Planning | outline_agent designs structure | PARTIAL | Has Blueprint but needs conversion to paper structure |
| Phase 3: Literature Search | literature_agent searches | SKIPPED | Bibliography is complete |
| Phase 4: Literature Review Writing | review_writer_agent writes | ACTIVE | Has Synthesis but needs conversion to paper tone |
| Phase 5: Methodology Writing | method_writer_agent writes | ACTIVE | Has Blueprint but needs expansion to full paragraphs |
| Phase 6: Findings Writing | findings_writer_agent writes | ACTIVE | Has Synthesis but needs expanded argumentation |
| Phase 7: Discussion Writing | discussion_writer_agent writes | ACTIVE | Needs original discourse (not direct copy of Synthesis) |
| Phase 8: Intro + Conclusion | bookend_agent writes | ACTIVE | Needs to be written based on full text |
| Phase 9: Abstract + Formatting | format_agent processes | ACTIVE | Needs full text completion first |
| Phase 10: Self-Review | review_agent reviews | ACTIVE | Must be executed |

---

## Post-Handoff academic-paper Actual Workflow

```
=== academic-paper: Accelerated Pipeline ===

Step 1: STRUCTURAL MAPPING
  [outline_agent]
  - Input: RQ Brief + Methodology Blueprint + Synthesis Report
  - Output: Complete paper outline, each section tagged with corresponding deep-research materials
  - Output example:

    I. Introduction
       - Context: AI in HE QA (from Synthesis background)
       - Problem: Cross-national variation unexplained
       - Purpose: Compare 3 East Asian models
       - RQ: [Directly cite RQ Brief]

    II. Literature Review
       - 2.1 AI in Quality Assurance (from Bibliography themes)
       - 2.2 Diffusion of Innovation framework (from Blueprint)
       - 2.3 Institutional Isomorphism (from Blueprint)
       - 2.4 East Asian HE systems comparison

    III. Methodology
       - 3.1 Research design: QCA + document analysis (from Blueprint)
       - 3.2 Case selection and data sources
       - 3.3 Analytical framework
       - 3.4 Validity and limitations

    IV. Findings
       - 4.1 Three adoption models (from Synthesis Finding 1)
       - 4.2 Critical success factors (from Synthesis Finding 2)
       - 4.3 Efficiency vs transparency tension (from Synthesis Finding 3)

    V. Discussion
       - 5.1 Theoretical implications
       - 5.2 Policy implications for accreditation agencies
       - 5.3 Practical recommendations
       - 5.4 Limitations (from Synthesis gaps + Blueprint validity)

    VI. Conclusion
       - Summary + Future research directions

Step 2: SECTION WRITING (Parallel)
  [review_writer_agent] → Literature Review
    - Based on Annotated Bibliography and Synthesis, transform into a fluent literature review
    - Not sequential summaries, but thematic integration

  [method_writer_agent] → Methodology
    - Expand the Blueprint into complete methodology paragraphs
    - Add technical details and procedural explanation for QCA

  [findings_writer_agent] → Findings
    - Expand the Synthesis's 3 core findings into evidence-supported arguments
    - Each finding accompanied by specific cases and data
    - Address contradictions flagged in the Synthesis

Step 3: DISCUSSION + BOOKENDS
  [discussion_writer_agent] → Discussion
    - Original discourse: dialogue between findings and theory
    - Does not repeat Findings; instead explains "why"
    - Integrates deep-research Knowledge Gaps as Future Research

  [bookend_agent] → Introduction + Conclusion
    - Introduction: from macro context to specific RQ
    - Conclusion: no new information, echoes RQ and looks to the future

Step 4: ABSTRACT + FORMAT
  [format_agent]
    - Abstract: 150-250 words, IMRAD structure
    - APA 7.0 full-text formatting
    - Reference list cleanup (based on Bibliography + newly added citations)

Step 5: SELF-REVIEW
  [review_agent]
    - Internal consistency check (RQ → Method → Findings → Discussion logic chain)
    - Citation completeness (every claim has a citation)
    - Format compliance
    - Verdict: Ready for submission / Needs revision
```

---

## User-Facing Handoff Experience

**academic-paper's Opening Message**:

> I've read your complete outputs from the deep-research stage, including:
> - Research Question Brief (FINER 4.6/5)
> - Methodology Blueprint (QCA + document analysis)
> - Annotated Bibliography (18 quality-screened sources)
> - Synthesis Report (3 core findings + 2 knowledge gaps)
>
> Based on these materials, I've completed a preliminary plan for the paper outline. Here is the planned paper structure:
> [Display outline]
>
> I have two questions that need your confirmation:
> 1. What is your target journal? (This affects word limits and formatting requirements)
> 2. Should the paper language be English or bilingual?
>
> Once confirmed, I'll begin writing. Because the research foundation is already comprehensive, I can skip the early exploration stages and proceed directly to paper writing.

---

## Notes

1. **Not copy-paste**: academic-paper does not directly copy deep-research outputs, but transforms them into the tone and format of an academic paper
2. **May discover new issues**: During the writing process, academic-paper agents may discover points missed by deep-research and will proactively supplement them
3. **Still requires user confirmation**: Target journal, language preference, specific formatting requirements still require user input
4. **Review recommendation auto-connects**: After paper completion, the user can continue with `academic-paper-reviewer` for formal review
