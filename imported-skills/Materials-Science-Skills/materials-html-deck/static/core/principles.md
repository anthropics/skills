# Core principles (materials-html-deck)

## Purpose

Transform a materials-science paper, notes, or outline into a complete Chinese, figure-integrated HTML academic deck.

The skill must not stop at an outline or script. The expected end product is a retained HTML deck directory with `index.html`, independent `slides/*.html`, shared design tokens, screenshots, QA reports, and an asset manifest.

## Core principle

Use the paper's scientific argument as the presentation spine. The default slide logic should help the audience answer, in order:

1. Why does this problem matter for materials science or engineering?
2. What gap or bottleneck does the work address?
3. What did the authors do (design, synthesis, characterization, test)?
4. What is the key evidence (performance, microstructure, mechanism)?
5. Why should we trust the result (controls, repeatability, standards)?
6. What is new, reusable, or broadly meaningful?
7. What are the engineering boundaries and open questions?

This is more important than copying the paper section order.

## Lean operating mode

Default to the lowest-overhead workflow that still produces a verified HTML deck.

Do:
- read only the source material needed to understand the paper's argument,
- extract only figures/tables that will actually appear in the deck,
- create the HTML deck as the primary deliverable,
- design slides with varied, evidence-led composition rather than rigid AI-looking card templates,
- prevent text overflow by writing shorter on-slide copy, using larger text boxes, and splitting slides when needed,
- run strict Playwright verification on the generated deck,
- inspect screenshot evidence and fix blank, clipped, hidden, or broken-media slides,
- write a short QA report.

Avoid by default:
- exhaustive extraction of every figure, page, image, table, or supplement,
- full OCR unless normal text extraction fails or the PDF is scanned,
- saving full raw extracted paper text unless it is needed for debugging or reuse,
- installing new dependencies when an existing tool can complete the task,
- launching GUI apps or desktop automation just to render previews,
- generating long markdown scripts when the user only needs a deck,
- delivering the deck when Playwright verification cannot run.

## Accepted inputs

The skill may receive: a full paper, supplementary figures or tables, Word or markdown converted paper text, abstract + results + figure legends, structured reading notes, manually pasted article content, an `input/source.md` file, brand-neutral visual preferences, or a JSON/Markdown outline for the fast path.

Default output language is simplified Chinese unless the user requests otherwise. Preserve important technical terms, abbreviations, material names, test standards, model names, dataset names, equations, and statistical terms in English when needed, and keep them consistent via the Terminology Ledger.
