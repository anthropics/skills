# Page Formats

Every wiki page has the same skeleton: YAML frontmatter + a section structure that matches its category. Below are the five canonical formats. Templates live in `assets/page-templates/`.

## 1. Entity page

For a person, organization, place, product, or dataset.

```markdown
---
title: Anthropic
category: entity
summary: AI safety company, developer of Claude; major contributor to interpretability research
tags: [company, ai-safety, anthropic]
sources: 4
updated: 2026-04-10
---

# Anthropic

## What it is
One-paragraph definition. What kind of entity, founded when, by whom, active in what.

## Why it matters (to this wiki)
Why this entity shows up across sources. What role does it play in the narrative?

## Key facts
- Founded YYYY by [[people]]
- Known for [[concepts]]
- Related [[entities]]

## Appears in
- [[sources/monosemanticity]] — primary work on sparse autoencoders
- [[sources/constitutional-ai]] — alignment methodology
- [[concepts/rlhf]] — contributor to training method

## Open questions
- Questions the sources don't yet answer; good prompts for new source hunts.
```

## 2. Concept page

For an idea, theory, method, framework.

```markdown
---
title: Sparse Autoencoder
category: concept
summary: Dictionary-learning method for decomposing polysemantic neurons into monosemantic features
tags: [interpretability, sparse-autoencoders, dictionary-learning]
sources: 3
updated: 2026-04-10
---

# Sparse Autoencoder

## Definition
Precise, one-paragraph definition. The canonical form used across your sources.

## Origin
Who proposed it, when, in what paper/context. Link [[entities]] and [[sources]].

## Key claims
- Claim 1 — cited from [[sources/xxx]]
- Claim 2 — cited from [[sources/yyy]]

## Contrasts with
- [[concepts/probing]] — see [[comparisons/sae-vs-probing]]

## Open questions / disagreements
- Unresolved questions across sources.
- ⚠️ Contradiction: [[sources/a]] claims X but [[sources/b]] claims ~X.

## Used in
- [[synthesis/interpretability-overview]]
```

## 3. Source summary page

One per ingested source. This is the **single place the raw source's content is summarized**; other pages cite it.

```markdown
---
title: "Towards Monosemanticity: Decomposing Language Models With Dictionary Learning"
category: source
summary: Anthropic 2024 paper using sparse autoencoders to extract interpretable features from a one-layer transformer
tags: [interpretability, sparse-autoencoders, anthropic]
source_path: raw/papers/monosemanticity.pdf
source_date: 2024-10
authors: [Bricken et al.]
ingested: 2026-04-10
updated: 2026-04-10
---

# Towards Monosemanticity

## TL;DR
Two sentences max. What did they do, what did they find.

## Key claims
1. Claim, with a page/section pointer if available
2. ...

## Methods
How the work was done. Data, model, training, evaluation.

## Evidence cited
- Figure 3 shows ...
- Table 1 ...

## Surprises / contradictions
- Where this source conflicts with [[sources/other]] or [[concepts/xxx]].

## Connections
- Extends [[concepts/sparse-autoencoder]]
- Builds on [[entities/anthropic-interpretability-team]]'s prior work
- Related: [[sources/superposition-2022]]

## Where it's cited
Pages in this wiki that cite this source:
- [[concepts/sparse-autoencoder]]
- [[entities/anthropic]]
- [[synthesis/interpretability-overview]]
```

## 4. Comparison page

For explicit cross-source or cross-concept analysis.

```markdown
---
title: "SAE vs Probing"
category: comparison
summary: How sparse autoencoders differ from linear probing as interpretability methods
tags: [interpretability, comparison]
sources: 4
updated: 2026-04-10
---

# Sparse Autoencoders vs Linear Probes

## What they share
Both look for human-interpretable structure inside trained models.

## Where they diverge
| Dimension | SAE | Probe |
|---|---|---|
| Supervision | unsupervised | supervised |
| Output | dictionary of features | single-label classifier |
| Scalability | model-dependent | cheap |
| Typical use | feature discovery | feature verification |

## Which sources take which side
- [[sources/monosemanticity]] — pro-SAE
- [[sources/probing-survey]] — pro-probes

## Open questions
- When should you prefer one over the other?
```

## 5. Synthesis page

High-level views that draw on many sources and concepts.

```markdown
---
title: Interpretability Overview
category: synthesis
summary: The field of interpretability research — goals, methods, open problems, key players
tags: [interpretability, overview]
sources: 12
updated: 2026-04-10
---

# Interpretability Overview

## Thesis
Two or three sentences capturing the current synthesis across all sources read so far. Revised as new sources come in.

## The landscape
- Sub-area A — pursued by [[entities]], papers [[sources]]
- Sub-area B — ...

## Current open problems
Short list with [[concepts]] and [[sources]] pointers.

## How this synthesis has changed
- **2026-04-10** — added [[sources/monosemanticity]]; shifted emphasis toward SAE.
- **2026-03-28** — initial synthesis after first 5 sources.

## Related
- [[synthesis/alignment-overview]]
- [[comparisons/mechinterp-vs-behavioral-interp]]
```
