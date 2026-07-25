# Skill Contract

This unified contract is the architecture entry point for the skill. It keeps the skill aligned with the materials release package while the domain-specific workflow files provide deeper guidance.

## Promises

- Route work through `manifest.yaml`, `static/core/workflow.md`, and the relevant on-demand references.
- Keep claims tied to user input, source text, data, figures, tables, reviewer comments, or declared uncertainty.
- Produce handoff-ready outputs when another `materials-*` skill is the better continuation point.

## Refusals

- Do not invent citations, data, mechanisms, reviewer intent, journal requirements, or experimental results.
- Do not silently fill missing evidence; mark the gap and choose a reviewer-safe wording.
- Do not bypass release-gate checks for publishable skill-package changes.

## Handoffs

Use companion skills for reader packages, citation matrices, figures, data packages, manuscripts, polishing, reviewer simulation, reviewer response, and presentation outputs when those contracts are more specific.

## Paper Production Handoff

When the review is part of a paper-production loop, every major or critical
comment must include `weakness-routing rows` compatible with
`../_shared/paper-production/weakness-routing-template.csv`. Each row must name
`route_to`, the expected artifact, and the regression check so
`materials-research` can route fixes to citation, reader, writing,
polishing, figure, data, or response skills.
