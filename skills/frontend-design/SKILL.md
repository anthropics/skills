---
name: frontend-design
description: Establish domain-specific visual identity, typographic hierarchy, spatial layout, and interface copy when building a new user interface or refactoring an existing interface.
license: Complete terms in LICENSE.txt
---

# Frontend Design

## Domain Grounding

- Derive color palette, typographic hierarchy, spatial layout, and interface copy directly from the industry, physical materials, domain vernacular, target audience, and functional objective specified in the input brief.
- Extract existing user preferences and project context from provided session parameters to anchor visual direction prior to layout generation.
- Formulate a concrete proposal defining a single product subject, target audience, and primary functional objective for user confirmation prior to code generation when the input brief omits subject specifications.
- Populate interface components with domain-authentic content and terminology derived from the target subject matter across each view.

## Execution Workflow

- Execute design and implementation in two sequential phases: Phase 1 (Design Specification Plan) followed by Phase 2 (Source Code Implementation).
- Construct a structured design token specification in Phase 1 prior to generating source code:
  + Color Tokens: Define 4 to 6 named hexadecimal color values representing the core palette.
  + Typography Tokens: Specify 1 or 2 typeface families and assign each family to a distinct structural role.
  + Layout Specification: Formulate single-sentence spatial descriptions paired with comparative ASCII wireframes and explicit text alignment rules (left-aligned, center-aligned, or justified).
  + Visual Differentiation Rules: Define the domain-specific structural and aesthetic mechanisms that distinguish the interface.
- Prioritize explicit visual directions stated in the input brief over general design rules.
- Audit each unspecified visual axis in the Phase 1 design plan against recurring cross-domain default patterns, replacing generic defaults with domain-grounded alternatives and documenting each revision rationale prior to Phase 2 code generation:
  + Warm cream background (`#F4F1EA`) paired with high-contrast serif display typography and terracotta accent (`#D97757`)
  + Near-black background (`#0B0B0B` or `#111111`) paired with a single acid-green or vermilion accent
  + Broadsheet grid with hairline rules, `0px` border-radius, and multi-column newspaper density
  + Uniform rounded SaaS card grids with identical border-radius across hierarchy levels, `rgba(0,0,0,0.1)` drop shadows, and decorative gradient washes
  + Recurring template chrome consisting of tracked uppercase eyebrow labels, middle-dot metadata strings (`A · B · C`), spaced em-dash labels (`WORD — fragment`), monospace micro-labels, and trailing arrow glyphs (`→`) on interactive triggers

## Visual and Structural Specifications

- Anchor the primary viewport (hero section) with the primary representative artifact of the subject domain—selected from a typographic statement, primary imagery, choreographed animation, live functional demo, or interactive component—separated from default metric-counter blocks and gradient accents unless specified by the input brief.
- Concentrate visual contrast on 1 primary focal element per view while maintaining neutral supporting surfaces, retaining exclusively structural elements that serve an informational role in the brief.
- Select 1 typeface family for the interface or 2 structurally contrasting typeface families mapped to display and body roles, calibrated to the domain vernacular of the brief.
- Configure a modular typographic scale governed by *The Elements of Typographic Style* using explicit font weights, character widths, and letter-spacing values so headline typography operates as an active structural element.
- Constrain body copy measure to a maximum of 80 characters per line for sans-serif typefaces, expanding line length and vertical line-height proportionally when rendering serif body text.
- Render headlines with uniform typographic weight, style, and color across the complete phrase, separated from single-word italic, bold, or color highlights.
- Format interface labels in sentence case or title case, and position structural headings directly above content blocks separated from intermediary uppercase eyebrow labels.
- Assign structural dividers, borders, outlines, and labels strictly to encode semantic hierarchy and content relationships.
- Apply sequential numeric markers (`01`, `02`, `03`) exclusively to ordered multi-step processes or chronological timelines.
- Restrict autonomous motion to at most 1 orchestrated page-load or reveal sequence per view, separated from repetitive section fade-up entrances and uniform card hover transitions.
- Bind interactive motion directly to user-triggered state changes (opening, expanding, or confirming actions) to indicate structural state transitions.

## Interface Copy Specifications

- Formulate interface copy in sentence case, active voice, and plain domain verbs where each text element executes 1 informational or navigational function.
- Label interface controls and views according to end-user mental models, separated from internal system architecture terminology:
  + `Webhook config` ➔ `Notifications`
- Specify the exact state mutation on each interactive trigger and maintain lexical equivalence between the trigger label and its resulting state confirmation:
  + `Submit` ➔ `Save changes`
  + `Publish` (action trigger) ➔ `Published` (confirmation toast)
- Construct empty states as actionable onboarding prompts and format error messages as direct diagnostic statements specifying the failure cause and remediation step, separated from apologetic phrasing.

## Technical Implementation and Verification

- Partition CSS selector specificity across layout containers (such as `.section`) and interactive components (such as `.cta`) to preserve orthogonal margin and padding declarations.
- Implement responsive viewport adaptation down to mobile breakpoints, visible `:focus-visible` keyboard indicators, `@media (prefers-reduced-motion: reduce)` compliance, and WCAG-compliant color contrast across each view.
- Capture and inspect rendered viewport screenshots when supported by the execution environment to identify and resolve spatial, typographic, or alignment defects prior to final output delivery.
- Record executed visual tokens and layout patterns into an explicit design log parameter when persistent workspace storage is available to maintain cross-session visual differentiation.
