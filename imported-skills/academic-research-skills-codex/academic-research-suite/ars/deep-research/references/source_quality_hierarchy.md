# Source Quality Hierarchy — Evidence Grading Framework

## Purpose
Systematic framework for grading evidence quality, used by the source_verification_agent and bibliography_agent.

## Evidence Pyramid (7 Levels)

```
         ╱╲
        ╱ I ╲        Systematic Reviews / Meta-Analyses
       ╱──────╲
      ╱  II    ╲     Randomized Controlled Trials
     ╱──────────╲
    ╱   III      ╲   Controlled Studies (non-randomized)
   ╱──────────────╲
  ╱    IV          ╲  Case-Control / Cohort Studies
 ╱──────────────────╲
╱     V              ╲  Systematic Reviews of Descriptive Studies
╱──────────────────────╲
╱      VI                ╲  Single Descriptive / Qualitative Studies
╱──────────────────────────╲
╱       VII                  ╲  Expert Opinion / Committee Reports
╱──────────────────────────────╲
```

## Detailed Level Descriptions

### Level I: Systematic Reviews & Meta-Analyses
**Weight**: Highest
**Description**: Rigorous synthesis of all available evidence using predefined, systematic methods.
**Characteristics**:
- Pre-registered protocol (PROSPERO or similar)
- Comprehensive search across multiple databases
- Explicit inclusion/exclusion criteria
- Quality assessment of included studies
- Statistical pooling (meta-analysis) when appropriate
- PRISMA reporting guidelines followed

**Trusted Sources**: Cochrane Library, Campbell Collaboration, JBI Evidence Synthesis

**Caveats**: Quality depends on included studies ("garbage in, garbage out"); may be outdated if field moves fast.

### Level II: Randomized Controlled Trials (RCTs)
**Weight**: Very High
**Description**: Experimental studies with random allocation to intervention/control groups.
**Characteristics**:
- Random assignment
- Control/comparison group
- Blinding (single, double, or triple)
- Pre-registered protocol
- Adequate sample size
- Intention-to-treat analysis

**Caveats**: Not always feasible (especially in social science/education); ethical constraints; external validity concerns.

### Level III: Controlled Studies Without Randomization
**Weight**: High
**Description**: Quasi-experimental designs with comparison groups but no randomization.
**Characteristics**:
- Comparison group present
- Pre-post measurements
- Attempts to control confounds
- Larger samples than case studies

**Examples**: Difference-in-differences, propensity score matching, regression discontinuity.

**Caveats**: Selection bias risk; confounding variables harder to control.

### Level IV: Case-Control & Cohort Studies
**Weight**: Moderate-High
**Description**: Observational studies tracking groups over time or comparing cases to controls.
**Characteristics**:
- Longitudinal (cohort) or retrospective (case-control)
- Natural variation, no researcher intervention
- Large samples possible
- Real-world context

**Caveats**: Cannot establish causation; confounders possible; recall bias (case-control).

### Level V: Systematic Reviews of Descriptive/Qualitative Studies
**Weight**: Moderate
**Description**: Rigorous synthesis of qualitative or descriptive research.
**Characteristics**:
- Systematic search and selection
- Quality appraisal of included studies
- Meta-synthesis or meta-ethnography techniques
- Transparent methods

**Caveats**: Quality limited by included studies; interpretive layer adds subjectivity.

### Level VI: Single Descriptive or Qualitative Studies
**Weight**: Low-Moderate
**Description**: Individual case studies, ethnographies, surveys, descriptive analyses.
**Characteristics**:
- In-depth, context-rich
- Exploratory or descriptive purpose
- Small samples typical
- Thick description

**Caveats**: Limited generalizability; researcher subjectivity; no causal claims warranted.

### Level VII: Expert Opinion & Committee Reports
**Weight**: Lowest
**Description**: Position papers, editorials, committee reports, guidelines based on expert consensus.
**Characteristics**:
- Based on expertise and experience
- Often integrates multiple evidence types informally
- May reflect institutional or ideological positions

**Caveats**: Not empirically tested; potential bias; "authority" ≠ "evidence."

## Grading Rubric

Each source is assessed on **two distinct axes** that the columns below combine. Conflating them caps strong interpretive and qualitative work at a low overall grade no matter how excellent it is within its own tradition.

- **Study-design level** — where the design sits on the experimental-to-descriptive ladder (the 7-level pyramid above). This is absolute and field-neutral: a single qualitative case study is Level VI whether it appears in medicine or history.
- **Fitness for claim within a discipline** — whether the source is excellent *by its field's norms for the specific claim being made*. A primary archival source can be Level VI design evidence and at the same time the gold-standard evidence its field offers for an interpretive claim.

The **Evidence Level** criterion below grades *fitness*, not raw design level. A source earns Grade A on Evidence Level when its study-design level meets or exceeds **its own field's gold standard** (see the Field-Specific Adjustments table below), not only when it reaches Level I-II. So humanities work at Level VI, where Level VI *is* the field's gold standard, can score Grade A on this criterion. The other five criteria are field-neutral.

| Criterion | Grade A (Excellent) | Grade B (Good) | Grade C (Adequate) | Grade D (Weak) | Grade F (Unacceptable) |
|-----------|-------|-------|-------|-------|-------|
| Evidence Level | Meets/exceeds the field's gold standard for the claim | One level below the field's gold standard | Two levels below | Well below field norm | Unclassifiable or fundamentally unfit for the claim |
| Peer Review | Rigorous peer review | Standard peer review | Editorial review | No formal review | Self-published |
| Methodology | Exemplary, replicable | Sound, described | Adequate | Questionable | Absent/flawed |
| Sample/Data | Large, representative | Adequate | Limited but justified | Small, convenience | Unspecified |
| Currency | < 3 years | 3-5 years | 5-10 years | > 10 years | Outdated for topic |
| Conflicts | None declared or detected | Minor, disclosed | Moderate, disclosed | Undisclosed potential | Clear undisclosed conflict |

> "Currency" is claim-relative: a foundational or historical source is not penalized for age when the claim is about that source itself or its period. Apply the age bands only when recency bears on the claim (e.g., empirical state-of-the-field assertions).

### Overall Source Grade

The overall grade reflects **fitness for the claim**, not raw study-design level. A source whose design level is low (e.g., a Level VI primary source) can still earn an overall Grade A when it is excellent by its field's norms for the claim it supports.

**Aggregation rule.** Grade the six criteria above (each A-F), then combine:

1. **Integrity floor.** If **Conflicts** is F (clear undisclosed conflict), or **Peer Review** is F in a field whose Field-Specific Adjustments row (below) treats formal review as the norm, the overall grade is capped at D regardless of the other criteria. Integrity failures are not outweighed by strength elsewhere.
2. **Base grade.** Otherwise the overall grade is the **median** of the six criterion grades (on the A=4 … F=0 scale, rounding down on a tie between two adjacent grades).
3. **Fitness adjustment.** Raise the base grade by one step when **Evidence Level** (fitness) is Grade A — a source that is gold-standard for its field reaches overall A even when field-neutral criteria like Currency or Sample/Data sit lower. Do not apply this step if **Methodology** is F (a fundamentally flawed method is not rescued by field fit). Never raise past A.

So an interpretive study that is gold-standard within its discipline reaches overall Grade A, while an integrity-compromised (step 1) or methodologically broken (step 3 proviso) source does not, in any field.

**Overall grade meaning:**

- **A**: Use as primary evidence
- **B**: Use as supporting evidence
- **C**: Use with explicit caveats
- **D**: Use only if no better source; acknowledge weakness
- **F**: Do not use; cite only if critiquing

## Field-Specific Adjustments

Not all fields use the same evidence hierarchy. Adjust expectations:

| Field | Gold Standard | Common Level | Notes |
|-------|--------------|-------------|-------|
| Medicine/Health | Level I-II (RCTs, meta-analyses) | Level I-III | Evidence-based medicine tradition |
| Education | Level III-IV (quasi-experimental) | Level IV-VI | Randomization often impractical |
| Social Science | Level III-V | Level IV-VI | Mixed methods common |
| Policy | Level IV-V + VII (expert panels) | Level V-VII | Context-dependent; expert opinion valued |
| Humanities | Level VI (primary sources) | Level VI-VII | Different epistemology; "evidence" means different things |
| Technology | Level III + industry reports | Level V-VII | Fast-moving; peer review lags reality |

## Predatory Publication Indicators

### Red Flags Checklist
- [ ] Aggressive email solicitation to submit
- [ ] Acceptance within 72 hours of submission
- [ ] No identifiable editorial board (or fake names)
- [ ] Not indexed in Scopus, Web of Science, or PubMed
- [ ] Not member of COPE (Committee on Publication Ethics)
- [ ] Not listed in DOAJ (Directory of Open Access Journals)
- [ ] Excessively broad scope ("International Journal of Everything")
- [ ] Fake or inflated impact metrics
- [ ] Poor grammar/spelling on journal website
- [ ] APC (article processing charge) suspiciously low (< $200 for full OA)
- [ ] Editorial office in different country from stated location
- [ ] No retraction policy or ethics guidelines

### Verification Resources
- Beall's List (unofficial, but useful starting point)
- Cabell's Predatory Reports (subscription-based)
- DOAJ (whitelist of legitimate OA journals)
- COPE member directory
- Scopus Source List
- Journal Citation Reports (Clarivate)
- Think. Check. Submit. (thinkchecksubmit.org)
