---
name: materials-reader
version: "1.3.0"
description: Use when reading, translating, extracting, or organizing full papers for materials science and engineering research.
---

# Materials Science Reader

Read and organize materials papers into structured bilingual notes with source anchors.

## Layered architecture

This skill is split into two layers:

- A **static layer** under `static/` that holds reusable content fragments.
- A **dynamic layer** (this file plus [manifest.yaml](manifest.yaml)) that detects the request's axes and loads only the fragments needed for the current job.

## Protocol

1. Read [manifest.yaml](manifest.yaml), then load every `always_load` file.
2. Apply profile-first routing from `.materials/profile.yaml`; on first use, ask for direction once and save it locally.
3. Detect `source_format` and `output_type` from the user input.
4. Load matching source and output fragments. For each paper reading, load the terminology ledger before drafting outputs; load ethics only for attribution or AI-boundary work.
5. For each paper, produce: bilingual Markdown notes, source_map.json, terminology ledger, figure grounding.
6. Never interpret microstructure or mechanism claims without explicit evidence.

## Gates

- Source anchor every claim to page, paragraph, or figure.
- Distinguish what the paper says from what you infer.
- Flag overclaim risks in the confidence note.
