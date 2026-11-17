---
name: lica-brochure-design
description: Brochure-specific multi-panel layout, typography, fold reading order, and critique guidance from the LICA dataset’s folded-marketing category—not generic multi-page design. Use when the user asks to design or critique tri-fold, bi-fold, or informational brochures, panel roles, bleed/safe area, or print-ready spacing in design tools (e.g. Figma including via MCP). Prefer this when folds and panel flow matter.
license: Complete terms in LICENSE.txt
---

Brochure guidance is derived from the [LICA (Layout Intent and Composition Annotations) dataset](https://github.com/purvanshi/lica-dataset). Apply these principles when designing or critiquing brochures.

## Why LICA maps to **one skill per document type**

LICA encodes **per-category** structure: user intent, element placement, hierarchy, and composition differ systematically between document classes. Brochures introduce **fold logic, panel identity, and reading order** that single-page skills do not cover; merging everything into one “layout” skill dilutes those constraints. Category-specific skills let agents load **only** the rules that match the artifact—aligned with how LICA is organized by use case.

This skill is the **folded brochure** slice. Together with `lica-flyer-design`, it demonstrates a **repeatable pattern**: one focused skill per LICA-aligned category, with room to add resume, poster, logo, etc., as separate skills (see category list in [design-skills](https://github.com/purvanshi-lica/design-skills)).

## Sub-tasks: concrete outputs (execution discipline)

Unless the user restricts scope, run a full brochure pass through the sub-tasks **in order**. Each sub-task must emit a **concrete block** (table, numbered panel spec, wireframe in text, or checklist)—not a loose paragraph of advice.

### Sub-task A — Intake gaps (only what is missing)
Ask only for what is absent: fold type (tri / bi / gate / z), flat size (A4/Letter/custom), **panel count and fold direction**, print bleed/safe specs, audience, brand kit, must-win message, mandatory sections (pricing, map, team, legal), and imagery rules.

### Sub-task B — Fold + panel map
Generate:
1. **Diagram in text**: list panels as **P1, P2, …** in **reading order after folding** (unfolded flat map + folded user path).
2. A **table**:

| Panel ID | Role (cover / spread / back / flap) | WxH (flat) | Fold edges | Bleed | Safe inset |
|----------|--------------------------------------|------------|------------|-------|------------|
| | | | | | |

### Sub-task C — Narrative arc (content spine)
Generate **five bullets**: problem → promise → proof → details → CTA. Map each bullet to **one or more panel IDs** (where it will appear).

### Sub-task D — Per-panel content outline
For **each panel**, output:

```text
Panel Px — <role>
- Headline (if any): ...
- Subheads / bullets (max N lines): ...
- Body: ...
- Visual: (photo / icon row / diagram / none)
- CTA / contact: (yes/no + copy)
```

Keep body **scannable**; prefer bullets over long paragraphs on inside panels.

### Sub-task E — Per-panel wireframe (zones)
For **each panel**, give a **vertical or horizontal zone stack** with **approximate % heights or widths** (e.g. “top 40% hero image, middle 45% two-column bullets, bottom 15% CTA strip”). Note **what crosses a fold** (nothing critical in the gutter).

### Sub-task F — Shared typography system
One **master table** for the whole brochure:

| Role | Size (px or pt eq.) | Weight | Application (cover / inside / back) |
|------|---------------------|--------|----------------------------------------|
| Cover headline | | | |
| Section head | | | |
| Body | | | |
| Caption / legal | | | |

State **max font families** (typically ≤2) and rules for **consistent section heads** across panels.

### Sub-task G — Repeating components
List **reusable patterns** with rules: feature cards, icon+bullet rows, pull quotes, stat callouts, footer strip. For each: **structure** (e.g. “icon 24px, title, 2-line max”) and **which panels** reuse it.

### Sub-task H — Color + imagery consistency
Generate **brand application rules**: primary/secondary/neutral usage per panel type; **image crop alignment** to folds; **callout/card** fill vs stroke. Flag panels that should stay **mostly white** for readability.

### Sub-task I — Build plan (execution order)
Numbered checklist tailored to fold type, e.g.:

1. Flat master frame + margins guides  
2. Panel grid + fold guides  
3. Cover (P…) hero + headline  
4. Inside spread modules in reading order  
5. Back panel contact + legal  
6. Cross-panel **style sync** (type + color + cards)  
7. Fold simulation: **re-check trim and gutter**  
8. Final critique pass  

Use 10–18 steps as needed; reference **panel IDs** from sub-task B.

### Sub-task J — Critique pass
Apply the **Critique Checklist** in this skill: each item **Pass / Fail**; every Fail gets **one specific fix** (panel ID + change).

**Partial runs:** Match the user’s ask to sub-tasks only (e.g. “rewrite inside copy” → D for those panels only; “print setup” → B table + I steps 1–2 and 7).

## Canvas & Format
- Common print formats: tri-fold A4/Letter, bi-fold A4/Letter
- Set panel widths accurately for fold behavior
- Include bleed and safe area in every panel

## Layout Principles
### Tri-fold Brochure
- Front cover: brand + headline + hero image
- Inside spread: value proposition, features, visuals
- Back panel: contact details, social, legal/footer

### Bi-fold Brochure
- Cover with strong story hook
- Inside spread for narrative + feature blocks
- Back for company/about + CTA/contact

### Information Brochure
- Sectioned modules with clear dividers
- Consistent iconography for categories
- Scannable bullets over long paragraphs

## Typography
- Cover headline: 32–56px equivalent
- Section heads: 18–28px
- Body: 10–12pt print equivalent
- Keep line length comfortable and consistent

## Visual & Brand
- Keep brand colors consistent across all panels
- Use image crops aligned with fold boundaries
- Maintain consistent card/callout styles
- Avoid overcrowding any single panel

## Content Architecture
- Start with audience problem
- Present solution and differentiators
- Add trust proof (stats/testimonials/certifications)
- End with direct CTA and contact path

## Critique Checklist
- [ ] Does each panel have a clear role?
- [ ] Is reading flow intuitive after folding?
- [ ] Are headings and body text consistently styled?
- [ ] Is spacing sufficient around folds and edges?
- [ ] Are CTA and contact details easy to find?

## Usage
When designing or reviewing brochures, default to the **Sub-tasks** section so every response includes **specific generations** (panel map table, per-panel outlines, wireframes, type system, build plan, critique). Use **Sub-task A** only for missing facts; do not repeat questions the user already answered.
