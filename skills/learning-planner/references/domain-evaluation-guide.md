# Domain Evaluation Guide

`evaluation` entries are what turn a roadmap into something that actually
validates mastery, rather than a reading list. This guide is **illustrative,
not exhaustive** -- it exists to calibrate judgment, not to be looked up as a
closed table. Many disciplines aren't listed below; extrapolate using the
"How to Choose" framework.

## How to Choose Evaluation Methods

For each module, ask:

1. **How do practitioners in this field actually demonstrate competence?**
   Not "how would a school test this," but "what would a mentor or hiring
   manager ask this person to *do* to prove they've got it?"
2. **Match the method to the content type.** Conceptual understanding often
   needs explanation/derivation; procedural skill needs production/practice;
   creative work needs a produced artifact; analytical skill needs critique
   of an example.
3. **Prefer methods that produce something assessable** -- a written proof,
   a working program, a recording, an essay, a completed lab -- something
   that can be checked against the module's `expected_competence`, ideally
   by the learner themselves (self-assessment) when no instructor is
   available.
4. **Combine a "produce/perform" method with an "explain/critique" method**
   where it makes sense. The `evaluation` field is an array specifically so a
   module can have, e.g., both a problem set *and* an oral explanation --
   doing the work and being able to explain the work are different
   competencies.
5. **Raise the bar for `category: advanced` and `is_milestone: true`
   modules.** These should favor open-ended, integrative methods (projects,
   research tasks, case studies) over narrow drills.

## Illustrative Mappings by Discipline Cluster

These are starting points. A real module's evaluation should be specific to
its content -- "implement X" or "prove Y," not just the bare method name.

### Software Engineering / Programming
- **exercise-set** -- algorithmic/data-structure problems (the kind of
  practice associated with platforms like LeetCode or Codeforces -- treat
  these as a *category* of practice, not a specific problem to solve, since
  specific problems shouldn't be invented)
- **implementation** -- build a feature or data structure from scratch
- **debugging exercise** -- given broken/failing code, diagnose and fix it
- **project** -- a small-to-large end-to-end build
- **code review** -- critique a piece of code against stated criteria

### Mathematics
- **derivation** -- derive a result from first principles
- **proof** -- prove a stated theorem or property
- **problem-set** -- computational/applied problems
- **oral-explanation** -- explain a proof or concept without notes

### Physics / Natural Sciences
- **problem-set** -- quantitative problem solving
- **experiment** / **lab** -- physical or virtual experiment with analysis
- **simulation** -- build or run a computational model and interpret results
- **derivation** -- derive governing equations or approximations

### Machine Learning / Data Science
- **project** -- train and evaluate a model on a dataset (the user's own
  data, or a dataset they specify -- don't invent dataset names)
- **paper reproduction** -- reproduce a result from a paper the user has
  identified
- **model evaluation/critique** -- analyze a model's failure modes, biases,
  or limitations on given data
- **literature review** -- survey and synthesize a set of papers

### Cybersecurity
- **lab exercise** -- hands-on lab in a contained environment
- **attack scenario** -- red-team-style exercise against a defined target
- **threat modeling** -- produce a threat model / risk analysis for a system
- **incident response simulation** -- walk through detection and response to
  a described incident

### Languages
- **speaking** -- recorded conversation or oral exam
- **writing** -- composition/essay in the target language
- **listening comprehension** -- respond to audio material
- **reading comprehension / translation** -- work with written material

### History / Humanities
- **essay** -- argument-driven writing on a question or thesis
- **source analysis** -- critique a primary source (provenance, bias, context)
- **timeline construction** -- build and justify a causal/chronological account
- **debate / argument** -- construct and defend a position

### Business / Strategy / Product
- **case study analysis** -- analyze a business situation and recommend action
- **presentation / pitch** -- present a plan or recommendation
- **strategy memo** -- written strategic recommendation with justification
- **simulation** -- negotiation, market, or operational scenario

### Music
- **performance** -- recorded performance of a piece or exercise
- **ear training** -- aural identification/transcription exercises
- **composition / arrangement** -- produce an original or arranged piece
- **theory analysis** -- analyze the harmonic/structural content of a piece

### Law
- **case brief** -- summarize and analyze a case's reasoning and holding
- **legal memo** -- written legal argument or analysis
- **moot court / oral argument** -- argue a position orally
- **statutory analysis** -- interpret and apply a statute to facts

### Research (any field)
- **literature review** -- synthesize existing work on a question
- **reproduction study** -- reproduce a known result
- **research proposal** -- propose a study design addressing an open question
- **peer-review critique** -- critique a paper (the user's own or another's)
  against field standards

## When the Discipline Isn't Listed

Find the closest analog along these axes, then adapt:
- **Performance-based** disciplines (music, sport, public speaking, surgery,
  trades) -> recorded/observed performance + critique.
- **Argument-based** disciplines (law, philosophy, debate, policy) -> written
  or oral argument + critique against counterarguments.
- **Construction-based** disciplines (engineering, design, programming,
  composition) -> build something + explain/justify design decisions.
- **Analysis-based** disciplines (history, literary criticism, finance,
  research) -> analyze a given artifact/case/dataset + produce a written
  judgment.
- **Procedural/quantitative** disciplines (math, physics, chemistry,
  economics modeling) -> solve problems + derive/prove + explain reasoning.

Most real subjects are a mix -- combine accordingly.

## Anti-Patterns to Avoid

- **Defaulting to multiple-choice quizzes** regardless of discipline. These
  rarely demonstrate the kind of competence described in `expected_competence`.
- **Defaulting to programming-style exercises** for non-programming subjects
  (e.g., "implement a function" for a music theory module).
- **Using a single narrow drill as the only evaluation** for an `advanced` or
  `is_milestone` module -- these warrant integrative, open-ended evaluation.
- **Naming specific external resources** (specific problem sets, specific
  papers, specific datasets, specific past exam papers) in an `evaluation`
  description unless the user supplied them. Refer to categories ("a past
  exam paper for this course," "a small tabular dataset") and let the user
  supply or confirm specifics -- consistent with the resource policy in
  `SKILL.md`.
