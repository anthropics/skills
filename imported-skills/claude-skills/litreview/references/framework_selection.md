# Framework Selection — PICO, SPIDER, Decomposition, Hybrid

This reference answers exactly one decision: **which literature-review framework does litreview pick for a given research question, and how does each map sub-areas to search queries?**

Pair with `scripts/framework_recommender.py` for the deterministic heuristic.

## The Core Claim

A literature review's framework determines *what counts as a sub-area*. Pick the wrong framework → sub-areas don't map to actual research → searches return tangential papers → review is shallow.

The three primary frameworks plus hybrid:

| Framework | Best for | Components |
|---|---|---|
| **PICO** | ~70% of clinical questions; quantitative outcomes | Population / Intervention / Comparison / Outcome |
| **SPIDER** | Social / qualitative; experiential questions | Sample / Phenomenon / Design / Evaluation / Research-type |
| **Decomposition** | Technology-focused; design / engineering | Problem / Solution / Evaluation / Limitations |
| **Hybrid** | Cross-cutting topics (clinical + tech, etc.) | Pick components from multiple frameworks |

## PICO (default)

Most clinical and biomedical research questions map cleanly to PICO. Example:

> "How do LLMs perform on clinical reasoning tasks compared to physicians?"

| Component | Mapped to topic |
|---|---|
| **P**opulation | Clinical reasoning tasks (USMLE, MedQA, NEJM cases) |
| **I**ntervention | LLM-based reasoning (GPT-4, Claude, Med-PaLM) |
| **C**omparison | Physician baseline (specialists, residents, generalists) |
| **O**utcome | Diagnostic accuracy, reasoning quality, time-to-decision |

Each component becomes one or more sub-area searches.

**PICO weaknesses:**
- Maps poorly to qualitative research (no clear comparison)
- Maps poorly to technology evaluation (Population is fuzzy)
- Maps poorly to pure-theory questions (no Intervention)

When PICO doesn't fit cleanly → SPIDER or Decomposition.

## SPIDER (social / qualitative)

Designed for qualitative + mixed-methods research where PICO breaks. Example:

> "How do clinicians experience burnout in academic medicine?"

| Component | Mapped to topic |
|---|---|
| **S**ample | Clinicians in academic medical centers |
| **P**henomenon | Burnout (specifically: emotional exhaustion, depersonalization, reduced accomplishment) |
| **D**esign | Qualitative interviews, ethnography, phenomenology |
| **E**valuation | Lived experience, narrative themes |
| **R**esearch-type | Qualitative, mixed-methods |

Strong signal for SPIDER:
- Question contains "experience", "perception", "meaning", "lived"
- Outcome is hard to quantify
- Research methods involve interviews or observation

## Decomposition (technology / engineering)

Designed for design / build / evaluate questions. Example:

> "How are retrieval-augmented generation systems evaluated for clinical Q&A?"

| Component | Mapped to topic |
|---|---|
| **P**roblem | Clinical Q&A: high recall, factual accuracy, citation traceability |
| **S**olution | RAG architecture (retriever + generator combinations) |
| **E**valuation | Benchmarks (MMLU-clinical, MedMCQA, custom Q&A sets) |
| **L**imitations | Hallucination rates, latency, retrieval quality |

Strong signal for Decomposition:
- Question is about a *system* or *method*, not a population
- Question implicitly has "Problem → proposed Solution → how to test → known issues" structure
- Common in CS / ML / engineering research

## Hybrid (cross-cutting)

When no single framework fits, mix components. Example:

> "How effective is AI-assisted radiology workflow integration in community hospitals?"

| Component | Source framework | Mapping |
|---|---|---|
| Population | PICO | Community hospital radiology departments |
| Intervention | PICO | AI-assisted workflow integration (tool: vendor X) |
| Phenomenon | SPIDER | Workflow change, radiologist experience |
| Outcome | PICO | Read times, diagnostic accuracy, satisfaction |
| Limitations | Decomposition | Integration friction, false-positive rate |

Hybrid framing is more work but more accurate for questions that genuinely span disciplines.

## The Framework Recommender Heuristic

`scripts/framework_recommender.py` uses keyword signals to suggest a framework:

| Signal in research question | Suggests |
|---|---|
| "compared to", "vs", "versus", "better than" | PICO (Comparison) |
| "intervention", "treatment", "drug", "therapy" | PICO (Intervention) |
| "experience", "perception", "meaning", "narrative" | SPIDER (Phenomenon) |
| "qualitative", "interview", "ethnography" | SPIDER (Design) |
| "system", "model", "algorithm", "architecture" | Decomposition (Solution) |
| "benchmark", "evaluation", "metric" | Decomposition (Evaluation) |
| Multiple signals across frameworks | Hybrid |
| No strong signal | PICO (default) |

The recommender outputs:
- Recommended framework
- Confidence (high / medium / low)
- Rationale (which signals fired)
- 4-5 sub-area starter questions mapped to framework components

The skill then surfaces this in the post-Phase-2 checkpoint for user confirmation/override.

## When the User Says "You Pick"

Q2's "you pick" option triggers the recommender. The skill:

1. Runs Phase 1 recon search (using broad terminology from Q1)
2. After recon, runs the recommender heuristic against Q1 text
3. Surfaces in checkpoint: "I'm recommending {framework} because {rationale}. Override if you want."

User can override at checkpoint. Refusing to commit (just saying "go") → use recommender's pick.

## Anti-Patterns

### Defaulting to PICO without justification

PICO works for 70% but fails the other 30%. Defaulting to PICO for a SPIDER question wastes the search budget. The recommender prevents this; manual override should have justification.

### Hybrid for everything

Hybrid framing is more work and produces fuzzier sub-areas. Use only when a single framework genuinely fails. Default to non-hybrid; promote to hybrid only when checkpoint review surfaces real cross-cutting components.

### Forcing the framework to fit

If 3 of 5 components don't map naturally, the framework is wrong. Restart with a different framework rather than papering over the misfit.

### Picking framework before reading Q1

The recommender requires Q1 text. Asking Q2 before Q1 is answered loses signal.

### Ignoring the recommender's recommendation

If the recommender suggests SPIDER with high confidence and the user picks PICO anyway, gently challenge: "I see qualitative signals in your question. Want me to use SPIDER, or do you have a reason to insist on PICO?" Once. Honor user override after one push-back.

## Operational Checklist

- [ ] Q1 answered before Q2 (recommender needs Q1 text)
- [ ] Q2 forcing choice with "you pick" default
- [ ] `framework_recommender.py` run after Q1 (cached for checkpoint)
- [ ] Recommendation surfaced in checkpoint with rationale
- [ ] User can override at checkpoint
- [ ] Sub-areas mapped 1-to-1 with framework components
- [ ] Cross-cutting 5th sub-area added regardless of framework

## Citations (7 sources)

1. **Sackett, D. L. et al., *Evidence-Based Medicine: How to Practice and Teach EBM* (Churchill Livingstone, 1997, multiple eds.).** Origin of PICO as a clinical-question framing tool. The "PICO" acronym dates from this text. https://en.wikipedia.org/wiki/Evidence-based_medicine

2. **Cooke, A., Smith, D., & Booth, A., "Beyond PICO: The SPIDER Tool for Qualitative Evidence Synthesis" — *Qualitative Health Research* 22(10), 2012, pp. 1435-1443.** Origin of SPIDER as a PICO alternative for qualitative research. Documents the systematic failures of PICO on qualitative questions that motivated SPIDER's design.

3. **Booth, A., "Searching for qualitative research for inclusion in systematic reviews: a structured methodological review" — *Systematic Reviews* 5, 2016.** Comparative analysis of PICO vs SPIDER for qualitative work. Source for the "SPIDER for social/qualitative" guidance.

4. **PRISMA 2020 Statement — Page, M. J. et al., *BMJ* 372, 2021.** The systematic-review reporting standard. Section on "Eligibility criteria" formalizes the framework-driven approach to defining inclusion/exclusion criteria from sub-areas.

5. **Cochrane Handbook for Systematic Reviews of Interventions — Higgins, J. P. T. et al. (Wiley, 2019, online updates).** Authoritative source for PICO-driven systematic review methodology. Chapter 4 on "Searching for and selecting studies" formalizes the framework → sub-area → search-string mapping pattern.

6. **Hewitt-Taylor, J., "Use of constant comparative analysis in qualitative research" — *Nursing Standard* 15(42), 2001.** Source for the cross-cutting-theme pattern that litreview adds as a 5th sub-area regardless of framework. Constant comparative analysis surfaces themes that cross conventional framework boundaries.

7. **JBI Evidence Synthesis methodology — Joanna Briggs Institute manual (jbi.global).** Comprehensive framework comparison: PICO for quantitative effectiveness, PICo (lowercase 'o' for context) for qualitative, PEO for risk factors, CoCoPop for prevalence. The litreview skill simplifies to PICO/SPIDER/Decomposition + hybrid but the JBI manual catalogs ~12 framework variants for specialty cases.
