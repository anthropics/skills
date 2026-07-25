---
name: materials-citation
version: "1.1.0"
stability: stable
description: Use when searching, screening, organizing, or mapping literature and citations for materials science and engineering manuscripts.
---

# Materials Science Citation

Build source-grounded literature search plans and claim-citation maps for materials manuscripts.

## Layered architecture

This skill is split into two layers:

- A **static layer** under `static/` that holds reusable content fragments.
- A **dynamic layer** (this file plus [manifest.yaml](manifest.yaml)) that detects the request's axes and loads only the fragments needed for the current job.

## Protocol

1. Read [manifest.yaml](manifest.yaml), then load every `always_load` file.
2. Apply profile-first routing from `.materials/profile.yaml`; on first use, ask for direction once and save it locally.
3. Detect `task`, `journal_family`, and `material_domain`.
4. Load only the matching fragment files.
5. Produce: search strategy, citation matrix, claim-source map, reference gap audit, or journal-specific source plan.
6. Do not invent papers, DOIs, impact factors, journal rules, or citation counts.

## Gates

- Prefer primary research and authoritative review articles over generic web summaries.
- Separate mechanism citations from performance citations.
