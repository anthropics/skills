# IMRaD Example — Higher Education Domain

This example demonstrates a complete IMRaD paper structure in the higher education field, showing how each agent's output integrates into the final paper.

---

# AI-Assisted Quality Assurance in Taiwanese Higher Education: Effects on Evaluation Consistency and Institutional Self-Assessment Practices

**Author:** [Example Author]
**Affiliation:** Center for Higher Education Research, [Example University]
**Date:** 2026

---

## Abstract

Quality assurance (QA) in higher education increasingly relies on standardized evaluation frameworks, yet inter-evaluator variance remains a persistent challenge. This study examines the effects of AI-assisted tools on evaluation consistency and institutional self-assessment practices in Taiwanese higher education. Using a quasi-experimental design, this study compared evaluation outcomes across 24 institutional accreditation cases—12 using traditional methods and 12 using AI-augmented evaluation protocols during the 2024-2025 accreditation cycle. Results indicated that AI-augmented evaluations reduced inter-evaluator variance by 28% (Cohen's *d* = 0.74) and improved alignment between self-assessment reports and site visit findings (*r* = .82 vs. .63 for traditional). Institutions reported that AI tools enhanced their self-assessment processes by identifying data gaps earlier in the preparation cycle. However, evaluators expressed concerns about potential homogenization of qualitative judgment. These findings suggest that AI tools can meaningfully improve QA consistency while highlighting the need for balanced integration that preserves expert judgment in accreditation processes.

**Keywords**: quality assurance, artificial intelligence, higher education accreditation, evaluation consistency, Taiwan

---

## Chinese Abstract

Higher education quality assurance increasingly relies on standardized evaluation frameworks, yet the issue of inter-evaluator consistency has persisted. This study aims to investigate the effects of AI-assisted tools on evaluation consistency and institutional self-assessment practices in Taiwanese higher education. A quasi-experimental design was employed, comparing evaluation outcomes across 24 institutional accreditation cases during the 2024-2025 accreditation cycle — 12 using traditional methods and 12 using AI-augmented evaluation protocols. Results showed that AI-augmented evaluations reduced inter-evaluator variance by 28% (Cohen's *d* = 0.74) and improved the alignment between self-assessment reports and site visit findings (*r* = .82 vs. .63 for traditional methods). Evaluated institutions also reported that AI tools helped identify data gaps earlier during the preparation phase. However, evaluators expressed concerns about the potential homogenization of qualitative judgment. These findings suggest that AI tools can effectively improve quality assurance consistency, but integration must be balanced to preserve expert professional judgment in the accreditation process.

**Keywords**: quality assurance, artificial intelligence, higher education accreditation, evaluation consistency, Taiwan

---

## 1. Introduction

### 1.1 Context and Background

Higher education quality assurance (QA) has undergone significant transformation globally over the past two decades (Stensaker & Harvey, 2023). In Taiwan, the Higher Education Evaluation and Accreditation Council of Taiwan (HEEACT) has administered institutional and program accreditation since 2005, evolving through three cycles of refinement (HEEACT, 2023). The current third cycle (2023-2025) emphasizes outcome-based evaluation, institutional self-governance, and evidence-informed decision-making.

Despite these advancements, inter-evaluator consistency remains a persistent challenge in accreditation processes worldwide (Leiber et al., 2022). Evaluators bring diverse disciplinary backgrounds, institutional experiences, and interpretive frameworks, which can lead to significant variance in evaluation outcomes even when using standardized rubrics (Martin & Parikh, 2024).

### 1.2 Problem Statement

The emergence of artificial intelligence tools offers potential solutions to the consistency challenge. AI-powered text analysis, data verification, and pattern recognition could complement human judgment by providing standardized baseline assessments (Chen & Wang, 2024). However, the integration of AI into QA processes remains understudied, particularly in East Asian higher education contexts where cultural norms of deference and consensus may interact differently with algorithmic recommendations.

### 1.3 Research Questions

1. **RQ1**: To what extent does AI-assisted evaluation reduce inter-evaluator variance in institutional accreditation?
2. **RQ2**: How does AI assistance affect the alignment between institutional self-assessment reports and site visit findings?
3. **RQ3**: What are evaluators' and institutional administrators' perceptions of AI-assisted QA tools?

### 1.4 Significance

This study contributes to the growing literature on AI in higher education governance by providing empirical evidence from an actual accreditation cycle—moving beyond simulation studies to real-world implementation.

---

## 2. Literature Review

### 2.1 Theoretical Framework

This study draws on two complementary frameworks: the theory of judgment aggregation (List & Pettit, 2011) and the technology acceptance model (TAM) adapted for expert systems (Venkatesh & Davis, 2021). Together, these frameworks explain both the structural effects of AI on group decision-making and the individual-level factors that determine adoption.

### 2.2 Evaluation Consistency in QA

Inter-evaluator reliability has been a central concern in higher education accreditation since the pioneering work of Stake and Cisneros-Cohernour (2000) on evaluator judgment variation. In the European context, the European Standards and Guidelines (ESG 2015) explicitly address the need for consistent application of evaluation criteria, yet empirical studies consistently reveal substantial variance. A meta-analysis by Martin and Parikh (2024) across 42 accreditation studies found that average inter-rater agreement (measured by ICC) ranged from .55 to .72 — well below the .80 threshold considered acceptable for high-stakes decisions in psychometric literature.

Calibration training has been the primary intervention to address this variance. QA agencies typically conduct pre-evaluation workshops where evaluators practice applying rubrics to sample cases and discuss divergent ratings. Leiber et al. (2022) evaluated the effectiveness of calibration training across five European QA agencies and found that while training improved agreement by approximately 12% in the short term, the effects diminished significantly within six months. The authors attributed this decay to the dominance of individual disciplinary norms over standardized criteria — a phenomenon they termed "disciplinary drift."

In the Taiwanese context, HEEACT has implemented a structured evaluator training system since 2012, requiring all evaluators to complete a two-day workshop before their first evaluation assignment (HEEACT, 2023). Lin and Huang (2023) studied evaluator agreement patterns across the second cycle of institutional accreditation (2017-2022) and found that agreement was highest for quantitative indicators (e.g., student-faculty ratios, graduation rates) and lowest for qualitative judgments (e.g., institutional culture, governance effectiveness). This pattern aligns with international findings and suggests that the consistency challenge is most acute precisely where expert judgment is most valuable.

A recurring debate in the literature concerns whether consistency should be pursued at the expense of evaluative depth. Stensaker and Harvey (2023) argue that excessive standardization may produce "procedural agreement" — evaluators converging on safe, middle-of-the-road ratings — while suppressing the nuanced, context-sensitive judgments that characterize expert evaluation. This tension between reliability and validity is central to the AI integration debate examined in this study.

### 2.3 AI in Higher Education Assessment

Artificial intelligence applications in educational assessment have expanded rapidly over the past decade, though most research focuses on student-level assessment rather than institutional evaluation. Automated essay scoring (AES) systems represent the most mature application, with systems like e-rater achieving human-level agreement rates above .85 for standardized writing assessments (Williamson et al., 2022). While AES operates at a fundamentally different level than institutional accreditation, the underlying principles — pattern recognition, consistency, and scalability — offer transferable insights.

Learning analytics and institutional research dashboards represent a more directly relevant application domain. Predictive analytics platforms now enable institutions to monitor student success indicators in real-time, flagging at-risk populations and program-level performance anomalies (Baker & Inventado, 2023). Several QA agencies have begun exploring how such institutional analytics data could complement traditional site visit evidence. The UK's Quality Assurance Agency (QAA) piloted an "enhanced monitoring" approach in 2023 that incorporated automated data analysis of institutional metrics as a pre-screening tool, reducing the number of full site visits required by 25% (QAA, 2024).

Natural language processing (NLP) applications offer particular promise for QA contexts. Self-assessment reports (SARs) — typically documents of 100-200 pages — require evaluators to identify claims, locate supporting evidence, and assess alignment between stated goals and documented outcomes. Chen and Wang (2024) demonstrated that NLP models trained on historical SARs could identify unsupported claims with 78% accuracy and flag data-evidence mismatches with 82% accuracy, potentially reducing evaluator cognitive load during document review.

However, the literature also raises significant concerns about AI integration in evaluative contexts. Algorithmic bias — the tendency of AI systems to reproduce patterns in training data — poses particular risks in accreditation, where historical evaluation patterns may reflect systemic biases against certain institution types, regions, or demographic compositions (Bearman et al., 2023). Furthermore, the "black box" nature of many AI systems conflicts with the transparency requirements of fair evaluation processes.

### 2.4 Technology Adoption in QA Organizations

QA agencies have historically been cautious technology adopters, reflecting both the conservative culture of accreditation and the high stakes of evaluation decisions (Rosa et al., 2022). A survey of 34 QA agencies across the European Higher Education Area found that while 82% had digitized their administrative processes (e.g., document management, scheduling), only 18% had integrated technology into the core evaluation workflow (ENQA, 2023). The most common barriers cited were evaluator resistance, data privacy concerns, and lack of technical infrastructure.

Technology acceptance research in professional evaluation contexts draws heavily on the Technology Acceptance Model (TAM) and its extensions. Venkatesh and Davis (2021) found that perceived usefulness and perceived ease of use were necessary but insufficient conditions for adoption in expert judgment contexts — professionals also required assurance that technology would not diminish their professional autonomy or status. This finding is directly relevant to evaluator acceptance of AI tools, where concerns about "being replaced by algorithms" may override rational assessments of tool utility.

Successful technology integration in QA appears to follow a pattern of incremental adoption, beginning with administrative functions and gradually extending to analytical support roles. The Malaysian Qualifications Agency's (MQA) phased deployment of its MyQUEST online evaluation platform (2018-2023) offers an instructive case: by initially positioning the technology as a "data preparation tool" rather than an "evaluation tool," MQA avoided triggering evaluator resistance and achieved 94% adoption within three years (MQA, 2023). This framing strategy — technology as support rather than substitute — appears critical for QA contexts.

---

## 3. Methodology

### 3.1 Research Design

A quasi-experimental design with matched comparison groups was employed. Institutional accreditation cases were matched on institution type (public/private), size (student enrollment), and prior accreditation outcomes.

### 3.2 Sample

Twenty-four institutional accreditation cases from the 2024-2025 cycle were included: 12 in the AI-augmented group (intervention) and 12 in the traditional group (comparison). Each case involved 4-6 evaluators, yielding evaluation data from 116 evaluators.

### 3.3 AI-Augmented Evaluation Protocol

The intervention group used an AI-assisted platform that provided: (a) automated SAR completeness checks, (b) data verification against MOE institutional databases, (c) cross-institutional benchmarking dashboards, and (d) preliminary alignment analysis between SAR claims and supporting evidence.

### 3.4 Data Collection

- Evaluation rubric scores (standardized 4-point scale across E1-E4 criteria)
- Inter-evaluator agreement metrics (per evaluation team)
- SAR-site visit alignment scores (researcher-coded)
- Post-evaluation surveys (evaluators, *n* = 116; institutional coordinators, *n* = 24)
- Semi-structured interviews (purposively selected, *n* = 18)

### 3.5 Data Analysis

Quantitative data were analyzed using independent-samples *t*-tests, ICC(2,k) for inter-evaluator reliability, and Pearson correlations. Qualitative data were analyzed using thematic analysis following Braun and Clarke (2022).

---

## 4. Results

### 4.1 Inter-Evaluator Consistency (RQ1)

The AI-augmented group demonstrated significantly higher inter-evaluator agreement across all four evaluation criteria (see Table 1).

**Table 1**

*Inter-Evaluator Reliability by Group and Evaluation Criterion*

| Criterion | AI-Augmented ICC(2,k) | Traditional ICC(2,k) | Difference |
|-----------|:--------------------:|:-------------------:|:----------:|
| E1: Governance | .89 | .71 | +.18 |
| E2: Teaching | .85 | .66 | +.19 |
| E3: Student Support | .82 | .63 | +.19 |
| E4: Social Responsibility | .79 | .61 | +.18 |
| **Overall** | **.84** | **.65** | **+.19** |

The overall difference was statistically significant (*t*(22) = 3.87, *p* < .001, *d* = 0.74).

### 4.2 SAR-Site Visit Alignment (RQ2)

Pearson correlation analysis revealed a significantly stronger alignment between SAR claims and site visit findings in the AI-augmented group (*r* = .82, *p* < .001) compared to the traditional group (*r* = .63, *p* < .01). The difference in correlation coefficients was statistically significant using Fisher's *z*-transformation (*z* = 2.14, *p* = .032).

Qualitative analysis of evaluator notes identified the primary mechanism: AI tools flagged 23 specific instances where SAR claims lacked adequate supporting evidence *before* site visits, enabling evaluators to prepare targeted verification strategies. In contrast, traditional evaluators typically identified evidence gaps only during site visits, when time constraints limited follow-up inquiry.

**Table 2**

*SAR-Site Visit Alignment by Evidence Type*

| Evidence Type | AI-Augmented (*r*) | Traditional (*r*) | Difference |
|--------------|:------------------:|:-----------------:|:----------:|
| Quantitative data claims | .91 | .78 | +.13 |
| Qualitative narrative claims | .75 | .54 | +.21 |
| Policy compliance claims | .88 | .72 | +.16 |
| Student outcome claims | .72 | .51 | +.21 |
| **Overall** | **.82** | **.63** | **+.19** |

The largest alignment improvements occurred in qualitative narrative claims and student outcome claims — precisely the areas where evaluators reported the greatest difficulty in traditional processes. AI tools appeared most valuable when assessing claims that required cross-referencing multiple data sources, a task where human working memory limitations typically constrain evaluator performance.

### 4.3 Stakeholder Perceptions (RQ3)

Survey results revealed differentiated perceptions between evaluators and institutional administrators. Among evaluators (*n* = 116), 68% agreed or strongly agreed that AI tools "helped me focus on important issues," while 54% expressed concern that AI recommendations "might unduly influence my independent judgment." The concern was significantly more prevalent among senior evaluators (>10 years experience; 71%) than junior evaluators (<5 years; 38%), *chi-square*(1) = 8.42, *p* = .004.

Institutional coordinators (*n* = 24) were more uniformly positive: 83% reported that AI-assisted SAR completeness checks helped them prepare better documentation, and 75% indicated that benchmarking dashboards improved their understanding of institutional positioning.

Thematic analysis of 18 semi-structured interviews identified four emergent themes:

1. **Efficiency gains with cognitive trade-offs**: Evaluators consistently reported that AI tools reduced the time required for document review (estimated 30-40% reduction), but several noted that this efficiency came at the cost of "deep reading" — the immersive engagement with institutional documents that sometimes yields unexpected insights. As one evaluator stated: "The AI highlights what's missing, but it can't tell me what I should be curious about."

2. **Homogenization anxiety**: Eight evaluators expressed concern that shared access to AI-generated analysis would converge evaluator perspectives prematurely, reducing the diversity of viewpoints that multi-evaluator teams are designed to provide. One evaluator described this as "everyone starting from the same page — literally the same AI-generated summary page."

3. **Calibration enhancement**: Six evaluators reported that AI benchmarking data provided a common factual reference point that improved team discussions. Rather than debating factual claims, teams could focus on interpretive differences, leading to what one evaluator called "higher-quality disagreements."

4. **Institutional gaming concerns**: Three institutional coordinators acknowledged that awareness of AI-assisted verification had changed their SAR writing strategies. One noted: "We now assume every number will be cross-checked automatically, so we're more careful with data accuracy. But we also know what patterns the AI looks for, which creates a temptation to optimize for the algorithm rather than for genuine improvement."

---

## 5. Discussion

### 5.1 Summary

AI-assisted evaluation tools significantly improved inter-evaluator consistency and SAR alignment, supporting the hypothesis that algorithmic assistance can address known variance issues in accreditation.

### 5.2 Interpretation

The substantial improvement in inter-evaluator consistency (ICC increase of .19) aligns with judgment aggregation theory's prediction that shared information structures reduce variance in group decisions (List & Pettit, 2011). When evaluators access AI-generated baseline analyses, they share a common informational foundation that constrains the range of plausible interpretations without eliminating individual judgment. This mechanism differs from calibration training, which attempts to align evaluator mental models directly — a more ambitious but less durable intervention, as Leiber et al. (2022) demonstrated.

The differential impact across evaluation criteria — with the smallest improvement observed in E4 (Social Responsibility) — suggests that AI tools are most effective for criteria with clearer operational definitions and more structured evidence bases. Social responsibility evaluation involves substantial value-based judgment and contextual interpretation, domains where current AI capabilities add less value. This finding resonates with Bearman et al.'s (2023) framework distinguishing "structured" from "unstructured" evaluation tasks, and suggests that AI integration strategies should be calibrated to criteria characteristics rather than applied uniformly.

The stakeholder perception findings illuminate a tension predicted by TAM for expert systems (Venkatesh & Davis, 2021): evaluators simultaneously valued the efficiency gains and feared the autonomy implications of AI assistance. The age-related difference in concern levels — senior evaluators were significantly more worried about AI influence — may reflect generational differences in technology comfort, but it may also reflect legitimate expertise-based concerns. Experienced evaluators have developed sophisticated heuristic strategies for document analysis that they perceive as threatened by algorithmic approaches. Whether these heuristics represent genuine expertise or idiosyncratic biases is an empirical question that this study cannot resolve, but it points to an important design consideration: AI tools for expert evaluators should augment rather than supplant existing analytical strategies.

### 5.3 Practical Implications

These findings suggest that QA agencies like HEEACT should consider phased integration of AI tools, beginning with data verification and benchmarking functions where the benefits are clearest and the risks of over-reliance are lowest.

### 5.4 Limitations

1. Quasi-experimental design limits causal claims
2. Single accreditation cycle; longitudinal effects unknown
3. Hawthorne effect possible in intervention group
4. Limited to Taiwanese institutional context

---

## 6. Conclusion

AI-assisted QA tools can meaningfully improve evaluation consistency in higher education accreditation. However, successful integration requires careful design that preserves expert judgment and contextual sensitivity. Future research should examine longitudinal effects and cross-national transferability.

---

## AI Disclosure

This paper was prepared with the assistance of AI-powered academic writing tools. The research pipeline included literature search assistance, statistical verification, and draft structuring. All content, research design, data analysis, and conclusions were directed and verified by the author. The author takes full responsibility for the accuracy and integrity of this work.

---

## References

*(This is an example — references are illustrative, not real citations)*

Braun, V., & Clarke, V. (2022). *Thematic analysis: A practical guide*. SAGE.

Chen, L., & Wang, Y. (2024). Artificial intelligence in educational quality assurance: A systematic review. *Quality in Higher Education*, *30*(1), 45-67. https://doi.org/10.xxxx

HEEACT. (2023). *Third cycle of institutional accreditation handbook (2023-2025)*. Higher Education Evaluation and Accreditation Council of Taiwan.

Leiber, T., Stensaker, B., & Harvey, L. (2022). Bridging theory and practice of impact evaluation of quality management in higher education institutions. *European Journal of Higher Education*, *12*(sup1), 8-28.

List, C., & Pettit, P. (2011). *Group agency: The possibility, design, and status of corporate agents*. Oxford University Press.

Martin, J., & Parikh, S. (2024). Inter-rater reliability in higher education accreditation: A meta-analysis. *Research in Higher Education*, *65*(3), 412-438.

Stensaker, B., & Harvey, L. (Eds.). (2023). *Accountability in higher education: Global perspectives on trust and power* (2nd ed.). Routledge.

Venkatesh, V., & Davis, F. D. (2021). A theoretical extension of the technology acceptance model: Four longitudinal field studies. *Management Science*, *46*(2), 186-204.
