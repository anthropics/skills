---
name: vibe-ui
description: Use when selecting or applying a DESIGN.md visual direction for web UI work, generating page-specific UI prompts, creating a Vibe Gate execution contract, or checking generated frontend code for design consistency.
license: Complete terms in LICENSE.txt
---

# Vibe UI

Vibe UI is a local-first DESIGN.md workflow for web UI generation. It helps Claude choose an inspired visual direction, apply the selected `DESIGN.md`, generate page prompts, and run a lightweight consistency pass after implementation.

Included styles are inspired by publicly visible UI patterns. They are not official brand systems. Do not copy logos, trademarks, screenshots, proprietary assets, or official brand claims.

## Commands

For project-changing commands such as `use`, `check`, and `report`, run from the target project root and call this skill's script by absolute path. For browsing styles only, running inside the skill directory is fine.

```bash
node scripts/design.mjs list [--source built-in|all]
node scripts/design.mjs search <keyword> [--source built-in|all]
node scripts/design.mjs recommend "<user goal>" [--source built-in|all]
node scripts/design.mjs use <design_id>
node scripts/design.mjs like <design_id> [page_type] [--strength light|medium|bold]
node scripts/design.mjs workflow <page_type> [--design design_id] [--template template_id] [--target file_or_directory]
node scripts/design.mjs invariants <design_id>
node scripts/design.mjs brief-check <page_type> [--design design_id] [--template template_id]
node scripts/design.mjs generate <page_type> [--template template_id]
node scripts/design.mjs check <file_or_directory>
node scripts/design.mjs report <file_or_directory> [--out DESIGN-REPORT.md]
node scripts/design.mjs browse [--source built-in|all] [--out directory]
node scripts/design.mjs preview [--source built-in|all] [--out directory]
```

Supported page types: `landing`, `dashboard`, `pricing`, `login`, `docs`, `settings`, `profile`, and `chrome-extension-landing`.

## Workflow

- If the user has not chosen a style, run `recommend "<goal>"`. Use `list` or `search` when the goal is unclear.
- If the user names a style, run `use <design_id>` from the project root with the skill script path. This writes `DESIGN.md`, `DESIGN.generated.md`, and `.vibe-ui/current-design.json`.
- If the user asks for a page that should feel "like" a known product, run `like <design_id> [page_type]` and keep the result brand-safe.
- Before editing or generating visible UI, run `workflow <page_type> --design <design_id>` and then `invariants` plus `brief-check`. `brief-check` writes `.vibe-ui/vibe-gate-contract.json`.
- Generate the implementation prompt with `generate <page_type>`.
- After implementation, run `check <file_or_directory>` or `report <file_or_directory>`.

## Bundled Resources

- `registry.json` contains 18 curated built-in style entries.
- `resource/awesome-design-md-main/design-md/*/DESIGN.md` contains the curated source DESIGN.md files required by the built-in registry.
- `resource/open-design-systems.json` is a stub catalog so source-filter commands remain compatible without bundling the full offline library.
- `resource/open-design-template-recipes.json` contains compact Vibe UI template recipes distilled from upstream source patterns.
- `resource/ui-anti-patterns.json` contains the Vibe Gate watchlist used by `brief-check`, `check`, and `report`.
- `NOTICE.md` records provenance and license notes for upstream resources.

The full standalone Vibe UI project also publishes a larger offline bundle. This skill contribution keeps only the compact curated set to reduce review and install size.

## Guardrails

- Treat `DESIGN.md` as the source of truth for colors, typography, spacing, radius, shadows, layout rhythm, density, and interaction style.
- Use brand names only as inspiration labels and source identifiers. Never claim the selected style is official.
- Do not use the workflow to produce pixel-perfect replicas of commercial websites.
- Avoid default LLM indigo, arbitrary gradients, emoji icons, invented metrics, filler copy, unsupported heavy shadows, and radius drift unless the selected `DESIGN.md` explicitly allows them.
- Use stable `data-od-id` values on top-level generated sections when reviewing source-backed page work.
- The checker is a first-pass static review. Still inspect the rendered UI and run the project's own tests before shipping.
