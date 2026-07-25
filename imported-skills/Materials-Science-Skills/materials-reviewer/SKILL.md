---
name: materials-reviewer
version: "1.1.0"
stability: stable
description: Use when simulating peer review, auditing manuscript risk, or stress-testing claims for materials science and engineering research.
---

# Materials Science Reviewer

Simulate 2-3 independent reviewer reports with a cross-review synthesis.

## Layered architecture

This skill is split into two layers:

- A **static layer** under `static/` that holds reusable content fragments.
- A **dynamic layer** (this file plus [manifest.yaml](manifest.yaml)) that detects the request's axes and loads only the fragments needed for the current job.

## Protocol

1. Read [manifest.yaml](manifest.yaml), then load every `always_load` file.
2. Apply profile-first routing from `.materials/profile.yaml`; on first use, ask for direction once and save it locally.
3. Detect `review_depth`, `journal_family`, `review_scope`, `material_family`, and `domain`.
4. Load matching fragments, then named shared contracts or criteria on demand.
5. Evaluate claim-evidence alignment, method robustness, and journal fit.
6. Produce distinct reviewer perspectives + synthesis, including weakness-routing rows when the review is part of a paper-production loop.

## Gates

- Never invent experiments, citations, or data to support a critique.
- Distinguish certain claims from speculative ones.
- Flag overclaim and missing evidence specifically.
