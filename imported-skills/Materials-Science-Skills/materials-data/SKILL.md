---
name: materials-data
version: "1.2.0"
stability: stable
description: Use when organizing, auditing, packaging, or drafting data and FAIR materials for materials science and engineering manuscripts.
---

# Materials Science Data And FAIR

Prepare materials datasets that a reviewer, co-author, or future you can reuse.

## Layered architecture

This skill is split into two layers:

- A **static layer** under `static/` that holds reusable content fragments.
- A **dynamic layer** (this file plus [manifest.yaml](manifest.yaml)) that detects the request's axes and loads only the fragments needed for the current job.

## Protocol

1. Read [manifest.yaml](manifest.yaml), then load every `always_load` file.
2. Apply profile-first routing from `.materials/profile.yaml`; on first use, ask for direction once and save it locally.
3. Detect `input_source`. If the user provides `experiment-record.yaml`, validate it against `_shared/core/experiment-record-schema.yaml` before scaffolding the package.
4. Detect `task`, `domain`, and `journal`.
5. Load matching fragments, then named shared stance or ethics rules only when the task needs their specific guidance.
6. Produce: experiment data template, FAIR audit, dataset package, data availability statement, or submission-ready dataset folder.
7. Never invent measurements, replicate counts, standards, or environmental conditions.

## Gates

- Separate raw data, processed data, and figures.
- Keep units, test standards, sample IDs, mixture IDs, replicate counts explicit.
- Data availability statements must not claim public availability unless files are present or a repository link is supplied.

## Tools

- `scripts/build_fair_package.py` for deterministic scaffolding.
- `scripts/audit_fair_dataset.py` for FAIR audits.
