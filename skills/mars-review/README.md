# mars-review

`/mars-review` — a Claude skill that runs a holistic, panel-style peer review of a research
paper. It distills the methodology of **[MARS: Multi-Agent Review System for Academic
Papers](https://www.kunpai.space/assets/papers/MARS.pdf)** (Pai & Shetty, UC Davis) into a
protocol a single Claude session can execute: independent persona reviewers, grounded
specialist checks, deliberation, and a meta-review — with explicit coverage accounting so
nothing in the paper gets skimmed.

## What it does

Given a paper (PDF, LaTeX project, or Markdown) and optionally a venue/CFP URL, the skill runs:

1. **Desk check** — scope fit against the actual CFP topics (gates the review, as in MARS's desk reviewer)
2. **Holistic map** — section inventory plus a claims–evidence table, including an internal-consistency audit (numbers reported differently in two places, abstract overclaiming vs. body)
3. **Independent panel** — three fixed, function-matched reviewer personas (domain expert, methodologist, informed outsider) reviewing the *whole* paper, each producing a decision plus quality/novelty/soundness/clarity scores
4. **Grounded specialist passes** — novelty checked against retrieved related work (arXiv + Semantic Scholar), load-bearing citations resolved and verified via Crossref, clarity notes kept advisory (non-voting)
5. **Socratic Q&A probe** — open-ended questions answered strictly from the paper's own text; the unanswerable residue becomes findings (MARS's questioner, repurposed as a completeness instrument)
6. **Board-room deliberation** — reviews meet, revisions are recorded, meeting-style minutes are written, and the panel decision is computed by explicit arithmetic
7. **Coverage audit** — a final self-check table proving every section was addressed

## Contents

```
SKILL.md                  the review protocol (Claude skill definition)
scripts/paper_search.py   arXiv + Semantic Scholar retrieval (stdlib only, no API keys)
scripts/bib_resolve.py    BibTeX parsing + Crossref citation verification (stdlib only)
```

The bundled scripts run with the Python standard library only:

```bash
python scripts/paper_search.py "your related-work query" --max 5
python scripts/bib_resolve.py parse refs.bib somekey2024
python scripts/bib_resolve.py verify "Some Paper Title" --author "Surname"
```

## Relation to MARS

MARS orchestrates multiple local LLMs (Mistral, Llama 3.2, Qwen2.5, DeepSeek-R1) as
sequential reviewers with specialist agents for desk review, novelty, grammar, Socratic
questioning, and insight fetching. This skill keeps that methodology — persona-driven
multi-perspective review, CFP-grounded desk checking, retrieval-grounded novelty, Socratic
questioning, and meta-review summarization — while adapting it for a single-model setting:
whole-paper (rather than section-wise) judgment, deterministic decision aggregation, and a
coverage audit as the success criterion.

## Citation

If you use this skill or build on the methodology, please cite the MARS paper:

```bibtex
@article{pai2025mars,
  title   = {{MARS}: Multi-Agent Review System for Academic Papers},
  author  = {Pai, Kunal and Shetty, Saisha},
  year    = {2025},
  note    = {Equal contribution},
  url     = {https://www.kunpai.space/assets/papers/MARS.pdf}
}
```

Original MARS implementation: [github.com/kunpai/MARS](https://github.com/kunpai/MARS)
Original standalone skill: [github.com/kunpai/MARS-Claude](https://github.com/kunpai/MARS-Claude)
