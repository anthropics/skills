# Audience Calibration — Undergrad vs Grad Summary Jargon + Question Complexity

This reference answers exactly one decision: **how does the syllabus skill calibrate summary jargon and discussion question complexity to the course's audience (Q2)?**

## The Core Rule

The same paper needs **different summaries** for different audiences:

- **Undergrad-intro**: define every technical term; assume zero prior knowledge
- **Undergrad-advanced**: assume foundational vocabulary; explain field-specific terms
- **Grad-Masters**: assume technical fluency; brief context for novel concepts
- **Grad-doctoral**: assume technical + methodological fluency; brief mention only of established context

Same paper, different summaries. Generic summaries miss the engagement target.

## Audience Buckets (Q2)

| Bucket | Vocabulary assumption | Method assumption | Discussion question complexity |
|---|---|---|---|
| Undergraduate (intro) | Zero specialized | Zero | Recall + comprehension + simple application |
| Undergraduate (advanced) | Foundational vocab | Common methods | Application + analysis |
| Graduate (Masters / early PhD) | Technical fluency | Common research methods | Analysis + evaluation |
| Graduate (doctoral / advanced) | Technical + methodological fluency | Methods specifics | Evaluation + critique + synthesis |
| Professional / continuing ed | Field-specific assumed | Methods context-dependent | Application to practice |
| Mixed | Lowest bucket present | Same | Same |

## Summary Calibration

### Undergrad-intro

Every technical term defined. Plain language. Connects to common experience.

| ❌ Too jargon | ✅ Calibrated |
|---|---|
| "This RCT compared lipidomic profiles across dietary interventions to assess cardiometabolic risk modulation." | "This randomized study compared what happens to fat molecules in the blood when people eat different diets — Mediterranean, Nordic, vegetarian — and looked at how those changes might affect heart disease risk." |
| "The phylogenetic analysis identified convergent evolution of toxin-resistant Na+ channels across reptilian lineages." | "Researchers compared sodium-channel genes across snake species and found that snakes from very different evolutionary branches independently developed similar resistance to toxic prey." |

### Undergrad-advanced

Foundational vocabulary assumed. Explain field-specific terms briefly.

| ❌ Too dumbed-down | ✅ Calibrated |
|---|---|
| "This randomized study compared what happens to fat molecules in the blood..." | "This RCT (n=240) tracked lipidomic shifts across three dietary patterns — Mediterranean, Nordic, vegetarian — over 12 weeks. Cardiometabolic markers improved most in the Mediterranean arm." |
| "Researchers compared sodium-channel genes..." | "Phylogenetic analysis across 47 reptilian lineages identifies convergent evolution of Na+ channel modifications conferring resistance to neurotoxic prey." |

### Grad (Masters or doctoral)

Technical fluency assumed. Brief context for novel concepts. Method specifics if relevant.

| ❌ Too verbose | ✅ Calibrated |
|---|---|
| "This RCT (n=240) tracked lipidomic shifts across three dietary patterns over 12 weeks. Cardiometabolic markers improved most in Mediterranean." | "RCT (n=240, 12-week, parallel-arm) comparing Mediterranean / Nordic / vegetarian. Mediterranean → 14% lower LDL-particle count, 22% lower oxidized LDL; differences plausibly mediated by MUFA:SFA ratio." |
| "Phylogenetic analysis across 47 reptilian lineages identifies convergent evolution..." | "Bayesian phylogenetic analysis (47 lineages, BEAST 2.7) supports independent emergence of Na+ channel S6-domain modifications in 6 lineages; convergence rate inconsistent with neutral drift (PP > 0.95)." |

### Professional / continuing ed

Field-specific terms assumed. Emphasize practice implications.

| ❌ Too academic | ✅ Calibrated |
|---|---|
| "RCT (n=240, 12-week)... LDL-particle count down 14%..." | "12-week RCT shows Mediterranean diet improves LDL-particle metrics 14-22% vs comparators. Practice implication: nutritional counseling for cardiovascular-risk patients should emphasize MUFA-rich foods specifically, not just 'low-fat'." |

## Discussion Question Calibration

Use Bloom's revised taxonomy (Anderson & Krathwohl 2001):

| Level | Action verbs | Question pattern |
|---|---|---|
| Remember | identify, list, recall | "What is X?" "Name the components" |
| Understand | explain, summarize, classify | "Why does X happen?" "How would you describe Y?" |
| Apply | use, apply, demonstrate | "How could this method be applied to...?" "What would happen if we used X for Y?" |
| Analyze | compare, contrast, examine | "What patterns connect X and Y?" "Why do X and Y produce different results?" |
| Evaluate | judge, critique, defend | "Is this study's conclusion warranted by its methods?" "Which approach better serves goal Z, and why?" |
| Create | design, propose, construct | "Design a study that would test the limits of X." "Propose a novel application of Y to Z." |

### Calibration by audience

| Audience | Question levels | Avoid |
|---|---|---|
| Undergrad-intro | Remember + Understand + simple Apply | Pure recall ("what did authors find?") |
| Undergrad-advanced | Understand + Apply + simple Analyze | Sophisticated Evaluate / Create |
| Grad-Masters | Apply + Analyze + Evaluate | Pure recall (insulting) |
| Grad-doctoral | Analyze + Evaluate + Create | Anything below Apply |

### Examples per audience

#### Undergrad-intro

| ❌ Recall only | ✅ Calibrated |
|---|---|
| "What did the authors find?" | "If you wanted to lower your heart disease risk through diet, what does this study suggest you should change?" (Apply) |

#### Grad-doctoral

| ❌ Below level | ✅ Calibrated |
|---|---|
| "What did this RCT show?" | "How would you redesign this RCT to test whether MUFA:SFA ratio specifically (vs total fat composition) drives the lipidomic shift?" (Create) |

## Discussion Question Validator

`scripts/discussion_question_validator.py` flags:

- **Recall-only questions** (any audience): "what did authors find?", "summarize", "describe"
- **Below-audience questions**: undergrad-intro questions in grad course → flag
- **Above-audience questions**: doctoral-level questions in undergrad-intro → flag

Validator suggests upgrades by replacing verbs with audience-appropriate Bloom verbs.

## Tying Discussion Questions to Learning Outcomes

Beyond audience calibration, each question should **explicitly tie to a learning outcome**:

| Without LO tie | With LO tie |
|---|---|
| "How could this approach be applied to...?" | "Course outcome 3 says students should be able to design enzymatic processes. How would the kinetics described in this paper inform a process design for cheese ripening?" |

The LO tie:
- Reinforces course goals
- Shows students why the reading matters
- Creates assessable discussion behaviors

If learning outcomes were inferred (`[inferred]`), still tie discussion questions to them — flag both as inferred.

## Anti-Patterns

### "Same summary for all audiences"

The biggest engagement killer. Undergrad summaries that read like graduate abstracts produce blank stares; graduate summaries that read like K-12 explainers feel patronizing.

### "Add jargon to look academic in undergrad summaries"

Engagement signal: students underline / highlight content. Jargon-heavy summaries get less highlighting in undergrad classes. Plain-language summaries get more.

### "Generic discussion questions"

"What did the authors find?" works for any audience — and serves none. The discussion question is the engagement hook; generic questions waste it.

### "All discussion questions at the highest Bloom level"

In a grad-doctoral course, even one Create-level question per paper is taxing. Mix Analyze, Evaluate, Create. Don't make every reading require students to design a follow-up study.

## Operational Checklist

- [ ] Q2 audience parsed → calibration bucket selected
- [ ] All summaries calibrated to bucket
- [ ] All discussion questions calibrated to bucket's Bloom range
- [ ] Each discussion question tied to a learning outcome (explicit or inferred)
- [ ] Validator (`discussion_question_validator.py`) run on all questions
- [ ] Recall-only questions rejected
- [ ] Below-audience or above-audience questions reworked

## Citations (7 sources)

1. **Bloom, B. S. (1956); Anderson, L. W. & Krathwohl, D. R. (2001), *A Taxonomy for Learning, Teaching, and Assessing*.** The revised Bloom's taxonomy. Source for the 6-level question hierarchy + action verb lexicon.

2. **Marzano, R. J. & Kendall, J. S., *The New Taxonomy of Educational Objectives* (Corwin, 2007).** Modern alternative to Bloom; emphasizes meta-cognitive and self-system levels. Source for the validator's "below-level vs above-level" distinction.

3. **Hattie, J., *Visible Learning* (Routledge, 2008/2023 update).** Meta-meta-analysis of educational interventions. Effect size 0.6+ for "teacher clarity" justifies the audience-calibrated summary discipline (clarity is audience-relative).

4. **Bain, K., *What the Best College Teachers Do* (Harvard, 2004).** Source for the "tied to learning outcome" discipline. Bain's research found great teachers connect every reading explicitly to course-level goals; generic readings produce engagement drop.

5. **Walvoord, B. E. & Anderson, V. J., *Effective Grading* (Jossey-Bass, 2nd ed. 2010).** Source for the "discussion question is assessable behavior" framing. Each discussion question = an opportunity to assess whether learning outcomes are being met.

6. **Brookfield, S. D. & Preskill, S., *Discussion as a Way of Teaching* (Jossey-Bass, 2nd ed. 2005).** Source for the engagement-vs-jargon trade-off in summary writing. Brookfield's research: students engage with content they can paraphrase; jargon-heavy summaries reduce paraphrase capability.

7. **Bjork, R. A. & Bjork, E. L., "Making Things Hard on Yourself, but in a Good Way" — *Psychology and the Real World* (FABBS Foundation, 2011).** Source for the "desirable difficulty" framing. Discussion questions should be challenging at the audience's edge, not below it (insulting) or above it (defeating).
