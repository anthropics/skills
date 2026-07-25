---
title: Academic Research Skills
description: AI-augmented academic research pipeline with integrity verification
version: 3.14.0
license: CC BY-NC 4.0
---

# Academic Research Skills for GitHub Copilot

AI-augmented research pipeline for academic writing, literature review, and peer review.

**Core principle:** AI is your copilot, not the pilot. Humans focus on substantive decisions; AI handles grunt work (references, formatting, verification).

## Quick Start

Try `/ars-plan` — describe your paper, get Socratic structure guidance.

**Key commands:** `/ars-lit-review`, `/ars-outline`, `/ars-full`, `/ars-reviewer`, `/ars-citation-check`

## Setup & Installation

→ **[SETUP.md](../docs/SETUP.md)** for plugin, local symlink, API keys, and optional tools

## Architecture & Components

- **Deep Research** — 13-agent team, PRISMA support, intent detection
- **Paper Writing** — 12-agent pipeline, style calibration, citation verification
- **Peer Review** — 7-agent multi-perspective review, quality rubrics
- **Pipeline** — 10-stage orchestration, claim verification, material passports

→ **[ARCHITECTURE.md](../docs/ARCHITECTURE.md)** for full flow diagrams and dependency graph

## Integrity & Safety

Addresses AI research failure modes (Kong et al. 2026, arXiv:2605.18661):
- 7-mode blocking checklist for common AI failures
- Claim-level audits with locator anchors
- Trust-chain frontmatter for provenance
- FNR/FPR calibration on custom measures

⚠️ **Permission modes:** for unattended pipeline runs, Auto mode is the recommended setting (a server-side classifier still gates dangerous escalations). `--dangerously-skip-permissions` removes all safety checks and is only appropriate for isolated, no-internet sandboxes. See [PERFORMANCE.md](../docs/PERFORMANCE.md#recommended-claude-code-settings) for full context before changing modes.

## Contributing

→ **[CONTRIBUTING.md](../CONTRIBUTING.md)** for PR workflow, acceptance criteria, development guidelines

## Docs

| Topic | Link |
|-------|------|
| **Setup & Installation** | [SETUP.md](../docs/SETUP.md) |
| **Architecture** | [ARCHITECTURE.md](../docs/ARCHITECTURE.md) |
| **Performance & Costs** | [PERFORMANCE.md](../docs/PERFORMANCE.md) |
| **Design Philosophy** | [POSITIONING.md](../POSITIONING.md) |
| **Contributing** | [CONTRIBUTING.md](../CONTRIBUTING.md) |
| **Citation** | [CITATION.cff](../CITATION.cff) |

## License

CC BY-NC 4.0 (non-commercial use) • DOI: [10.5281/zenodo.20696614](https://doi.org/10.5281/zenodo.20696614)

---

**This tool helps you write *better*, not helps you hide that you used AI. Integrity is non-negotiable.**
