# Systematic Review Mode — Full Protocol

Full PRISMA-compliant systematic literature review with optional meta-analysis. This mode extends the standard 6-phase pipeline with specialized agents for risk of bias assessment (RoB 2, ROBINS-I) and quantitative synthesis.

See `agents/risk_of_bias_agent.md` and `agents/meta_analysis_agent.md` for detailed agent definitions.
See `references/systematic_review_toolkit.md` for the Cochrane/PRISMA/GRADE reference guide.

## 5-Phase Pipeline

```
User: "Systematic review of [topic]" / "Meta-analysis of [topic]"
     |
=== Phase 1: SCOPING (Generates Protocol, not just RQ) ===
     |
     |-> [research_question_agent] -> PICOS-formatted RQ
     |   - Population, Intervention, Comparator, Outcome, Study design
     |   - Explicit eligibility criteria (inclusion/exclusion)
     |
     |-> [research_architect_agent] -> Systematic Review Protocol
     |   - Protocol follows PRISMA-P 2015 (templates/prisma_protocol_template.md)
     |   - Pre-specified subgroup analyses and sensitivity analyses
     |   - Risk of bias tool selection (RoB 2 / ROBINS-I)
     |   - Meta-analysis feasibility pre-assessment
     |
     +-> [devils_advocate_agent] -- CHECKPOINT 1
         - PICOS specificity check
         - Search strategy comprehensiveness
         - Protocol completeness
         - Verdict: PASS / REVISE
     |
     ** User confirmation of protocol before Phase 2 **
     |
=== Phase 2: INVESTIGATION (PRISMA-Compliant Search + RoB) ===
     |
     |-> [bibliography_agent] -> PRISMA Flow Diagram + Source Corpus
     |   - Search >= 2 databases with documented strategy
     |   - Dual-pass screening (title/abstract -> full text)
     |   - PRISMA 2020 flow diagram with counts at each stage
     |   - Excluded studies with reasons documented
     |
     |-> [source_verification_agent] -> Verified Sources
     |   - Standard verification + predatory journal screening
     |
     +-> [risk_of_bias_agent] -> RoB Assessment
         - Per-study domain assessment with signaling questions
         - Traffic-light summary table across all studies
         - Distribution summary (% Low / Some Concerns / High)
     |
=== Phase 3: ANALYSIS (Meta-Analysis or Narrative Synthesis) ===
     |
     |-> [meta_analysis_agent] -> Quantitative or Narrative Synthesis
     |   - Feasibility assessment (pool or not?)
     |   - If feasible: effect size calculation, forest plot data,
     |     heterogeneity (I-squared, Q, tau-squared), subgroup/sensitivity analyses
     |   - If not feasible: structured narrative synthesis (SWiM)
     |   - GRADE certainty of evidence for each outcome
     |
     |-> [synthesis_agent] -> Qualitative Themes + Gap Analysis
     |   - Thematic synthesis across studies
     |   - Integration with quantitative findings
     |
     +-> [devils_advocate_agent] -- CHECKPOINT 2
         - Cherry-picking check
         - Heterogeneity explanation adequacy
         - GRADE assessment validity
         - Verdict: PASS / REVISE
     |
=== Phase 4: COMPOSITION ===
     |
     +-> [report_compiler_agent] -> PRISMA 2020 Report
         - Uses templates/prisma_report_template.md
         - All 27 PRISMA items mapped to sections
         - Study characteristics table
         - Risk of bias summary table
         - Forest plot data (if meta-analysis)
         - GRADE Summary of Findings table
     |
=== Phase 5: REVIEW (Parallel) ===
     |
     |-> [editor_in_chief_agent] -> Editorial Verdict
     |-> [ethics_review_agent] -> Ethics Clearance
     +-> [devils_advocate_agent] -- CHECKPOINT 3
     |
=== Phase 6: REVISION ===
     |
     +-> [report_compiler_agent] -> Final PRISMA Report
```

## Checkpoint Rules

1. All standard checkpoint rules apply (see SKILL.md Checkpoint Rules)
2. **Protocol must be registered** (or registration recommended) before Phase 2
3. **Risk of bias must be completed for all studies** before Phase 3
4. **GRADE assessment required** for every pooled outcome
5. **PRISMA checklist compliance** verified in Phase 5
