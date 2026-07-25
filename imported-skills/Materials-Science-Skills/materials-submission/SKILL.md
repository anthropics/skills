---
name: materials-submission
version: "1.1.0"
stability: beta
description: Use when assembling a journal submission package for the supported materials journals declared in journal-templates.
---

# Materials Submission

`materials-submission` assembles a submission package from manuscript,
figure, FAIR-data, and reviewer artifacts. It loads the selected journal
template, validates the requested article route, and emits a cover letter,
checklist, declarations, and source-tracing stubs.

`manifest.yaml` defines the task, journal, and article-type axes used to route
the request to the selected template and supporting guidance.

## When to use

- Assemble a package for CBM, CCC, RMPD, JBE, Building and Environment,
  Energy and Buildings, Ceramics International, Acta Materialia, JMCA, or
  Nature Materials.
- Draft a cover letter with the publisher-facing article label.
- Generate Elsevier highlights where the selected template requires them.
- Produce a journal-specific checklist with declarations and required
  submission or revision artifacts.
- Emit `submission-package.yaml` for downstream package consumers.

## Rules

- The selected journal template controls accepted article types.
- Do not fabricate funding, conflicts, reviewers, data availability, or code
  availability.
- Preserve all live-verification markers until the user verifies the current
  publisher guide.
- Treat initial-submission and revision artifacts as separate checklist stages.

## When not to use

- Use `materials-writing` for manuscript prose.
- Use `materials-figure` for figures and graphical abstracts.
- Use `materials-data` for FAIR packages.
- Use `materials-reviewer` for reviewer simulation.
