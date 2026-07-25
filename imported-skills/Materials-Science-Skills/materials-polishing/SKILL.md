---
name: materials-polishing
version: "1.3.0"
stability: stable
description: >-
  Polish, restructure, proofread, or translate materials-science and
  engineering manuscript prose while preserving data, units, evidence
  strength, and author meaning. Use for academic or SCI writing, section
  polishing, Chinese-to-English translation, claim calibration, grammar,
  clarity, and journal tone. Also trigger on Chinese requests such as
  论文润色、学术写作、科研写作、英文论文润色、中译英、降重、检查语法、检查句式、修改句式.
---

# Materials Science Polishing

Use this file as the router. Reusable rules live in `static/` and
`references/`; [manifest.yaml](manifest.yaml) declares the routing axes and
paths. Keep this router short and read guidance from disk rather than applying
it from memory.

## Routing Protocol

1. Read [manifest.yaml](manifest.yaml), then load the five files under
   `always_load`.
2. Apply profile precedence: explicit request, saved `.materials/profile.yaml`,
   then neutral/general fallback.
3. Choose the **fast path** for a bounded sentence, title, short paragraph, or
   direct translation. Choose the **deep path** for document-scale work,
   structural repair, terminology consistency, risky claims, citation review,
   or paper-production handoffs. If depth is ambiguous, use the deep path.
4. Detect only relevant manifest axes. Load mapped files for selected axes and
   applicable `references.on_demand` entries. Read each selected path once.
5. Follow [static/core/workflow.md](static/core/workflow.md), validate the
   contract, and emit [static/core/output-format.md](static/core/output-format.md).

## Loading Rules

- Section and language guidance load when they change the requested edit.
- Paper-type guidance loads when research-versus-review logic matters.
- Journal guidance loads only for a stated or required journal family.
- Material-family and domain guidance load when terminology or evidence norms
  affect the text.
- Evidence, claim-strength, terminology, ethics, failure-mode, and
  weakness-routing files are conditional, not defaults.

## Blocking Gates

- Preserve data, units, test conditions, standards, citations, notation,
  uncertainty, limitations, and author meaning.
- Do not invent experiments, evidence, mechanisms, statistics, novelty,
  applicability, journal facts, or citations.
- Do not make weak evidence sound strong.
- Keep unsupported claims visible through revision or a claim-risk note.
- Do not run a full manuscript workflow for a bounded local edit.
