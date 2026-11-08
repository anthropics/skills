---
name: lica-flyer-design
description: Flyer-specific layout, typography, color, and critique guidance distilled from the LICA dataset’s promotional-layout category—not generic design advice. Use when the user asks to design, critique, or improve flyers, event promos, sale announcements, or similar single-page marketing layouts in design tools (e.g. Figma including via MCP) or static mockups. Prefer this over broad “design” skills when the artifact is explicitly a flyer.
license: Complete terms in LICENSE.txt
---

Flyer guidance is derived from the [LICA (Layout Intent and Composition Annotations) dataset](https://github.com/purvanshi/lica-dataset). Apply these principles when designing or critiquing flyers.

## Why LICA maps to **one skill per document type**

LICA’s strength is **granularity**: annotations and patterns are tied to **real layouts in a specific category** (flyer vs brochure vs resume vs logo system, etc.). Rules that fit a tri-fold brochure misfire on a single-page promo; a logo skill should not own flyer hierarchy. That is why LICA-backed agent skills should be **small and category-specific**: each `SKILL.md` encodes one document class so the model loads **narrow, evidence-shaped** constraints at invocation time—similar to picking the right tool for the job.

This skill covers the **flyer / promotional single-page** slice of LICA. A full LICA-aligned library is a **family** of such skills (see [design-skills](https://github.com/purvanshi-lica/design-skills) for the category matrix). This PR intentionally ships **two** categories first to establish the pattern before expanding coverage.

## Sub-tasks: concrete outputs (execution discipline)

When running a full flyer pass, complete the sub-tasks below **in order** so the user gets inspectable artifacts (tables, trees, copy deck)—not only prose. Each sub-task must produce a **visible block** (table, list, tree, or short spec).

### Sub-task A — Intake gaps (only what is missing)
Ask only for inputs not already provided: purpose/event, audience, channel (print / digital / social + exact size if known), must-have copy (headline, date, venue, CTA), brand colors/fonts/logo, legal or fine print, and imagery constraints (stock ok or not).

### Sub-task B — Intent + pattern choice
Generate:
1. **Intent label** (one of: event promo, sale/discount, community/nonprofit, corporate announcement, party/nightlife, or hybrid) with one sentence why it fits.
2. **Layout pattern** (one sentence): e.g. “hero-top + overlay text stack + isolated CTA bar.”
3. **Anti-patterns to avoid** (2 bullets) for this intent.

### Sub-task C — Canvas spec (numbers)
Generate a markdown **table** with exact values:

| Field | Value |
|--------|--------|
| Final WxH (px) | … |
| Bleed (if print) | … |
| Safe margin inset | … |
| Baseline grid / spacing unit | e.g. 8px |
| Export / platform | … |

### Sub-task D — Zone map (percentages + anchors)
Generate:
1. A **3-zone breakdown** with **percentage bands** of canvas height (hero / middle / bottom) and what lives in each.
2. For each zone: **alignment** (left / center / full-bleed) and **max text lines** allowed.

### Sub-task E — Type scale (roles → numbers)
Generate a **table**:

| Role | Size (px eq.) | Weight | Line-height | Font slot (1 or 2) |
|------|----------------|--------|-------------|---------------------|
| Headline | | | | |
| Subhead | | | | |
| Body | | | | |
| CTA | | | | |
| Footer | | | | |

State **max distinct sizes** (must be ≤4) and headline **max line count** (≤2).

### Sub-task F — Color tokens
Generate a **token list** (name, hex, role: background / headline / body / CTA fill / CTA text / accent). Include one sentence on **contrast strategy** (e.g. dark field + light headline) and note **WCAG** target (AA body 4.5:1, large text 3:1).

### Sub-task G — Layer / component tree
Output the **tree** from “Component Placement” for *this* flyer (not generic): every node that will exist, top to bottom, including overlay GROUP and CTA GROUP. If using Figma/MCP vocabulary, label nodes as FRAME / TEXT / GROUP / IMAGE consistently.

### Sub-task H — Copy deck (final strings)
Generate the **exact strings** to place (use placeholders in square brackets only where still unknown after intake):

- Headline (≤2 lines)
- Subhead (optional, 1 line)
- Body (2–4 short lines max)
- CTA label
- Footer / legal (if any)

### Sub-task I — Hero image brief
Generate a **5-bullet art direction**: subject, crop/aspect, mood, **overlay need** (yes/no + opacity range), and **what must stay text-free** for legibility.

### Sub-task J — Build plan (execution order)
Generate a **numbered checklist** (8–14 steps) for building in the design tool: e.g. set frame → background → hero image → overlay → headline stack → body → CTA → logo → footer → contrast pass. Tailor steps to the user’s tool (Figma layers, slides, etc.).

### Sub-task K — Critique pass
Run the **Critique Checklist** in this skill: output each item as **Pass / Fail**; for every Fail, give **one specific fix** (metric or layer change).

**Partial runs:** If the user only asks for one thing, still use the matching sub-task format (e.g. “only K” → full checklist table with fixes; “only typography” → sub-task E + contrast notes).

## Canvas & Dimensions
- Portrait standard: 816×1056px (US Letter) or 794×1123px (A4)
- Landscape promo: 1200×628px (social/web flyer)
- Square: 1080×1080px (Instagram/social)
- Choose based on distribution channel: print → portrait letter/A4, digital social → square or landscape

## Layout Principles (from LICA annotations)
- **One dominant headline**: The largest text element must answer "what is this?" instantly
- **3-zone structure**: Hero image zone (top 50%) → Headline + body (middle 30%) → CTA + details (bottom 20%)
- **Visual entry point**: Image or large typographic element anchors the eye at top-center
- **CTA must be isolated**: Surround call-to-action text with a GROUP background shape (button)
- Never let text overlap image without a contrast-ensuring overlay (semi-transparent GROUP)

## Typography Rules
- Headline: max 2 lines, extremely large (48–96px equivalent), bold or black weight
- Subheadline: 50–60% of headline size, medium weight
- Body copy: 12–16px, regular weight, line-height 1.4–1.6
- CTA button text: all-caps or title-case, bold, contrasting color to button background
- Maximum 2 font families; display font for headline, readable sans for body

## Color & Visual
- Use a bold, energetic palette — flyers compete for attention
- Background: can be rich/dark; let headline color pop against it
- Images: use `opacity: 1.0` for hero images, overlay GROUP at `opacity: 0.4–0.6` for text legibility
- Accent shapes via `GROUP` with `clip_path: true` — diagonal cuts, circles, and ribbons signal promotions
- Consistent color theme: event flyers use analogous colors; sale flyers use high-contrast complementary

## Component Placement (JSON structure awareness)
```
Canvas (width × height)
├── Background IMAGE or GROUP (full bleed)
├── Overlay GROUP (semi-transparent, for text zones)
├── Hero IMAGE (top 40–55% of canvas)
├── Headline TEXT (largest, centered or left-aligned)
├── Subheadline TEXT
├── Body TEXT (event details, 2–4 lines max)
├── Divider GROUP (decorative line or shape)
├── CTA GROUP (button container)
│   └── CTA TEXT
├── Logo IMAGE (top-left corner, small)
└── Footer TEXT (fine print, address, date/time)
```

## Design Intents (LICA user_intent patterns)
- **Event promo**: Date/time/venue dominant; energetic palette; countdown urgency
- **Sale/discount**: % or $ figure as giant hero text; red/yellow; "LIMITED TIME" urgency cue
- **Community/nonprofit**: Warm imagery; approachable sans-serif; pastel or earth tones
- **Corporate announcement**: Clean grid; brand colors; minimal imagery; formal hierarchy
- **Party/nightlife**: Dark background; neon accents; textured or gradient overlays

## Aesthetics Guidelines (LICA aesthetics field patterns)
- Contrast ratio: text on backgrounds must meet WCAG AA (4.5:1 for body, 3:1 for large text)
- Focal density: top third should have the highest visual weight
- Breathing room: even busy flyers need one "quiet" zone to rest the eye
- Consistency: margins, padding within text blocks should be uniform multiples (8px grid)

## Critique Checklist
When reviewing a flyer design, evaluate:
- [ ] Can you read the headline in under 2 seconds from normal viewing distance?
- [ ] Is the CTA visually distinct and easy to find?
- [ ] Does text have sufficient contrast against its background?
- [ ] Is the hierarchy (headline > subheadline > body > CTA) unambiguous?
- [ ] Are there fewer than 4 distinct font sizes?
- [ ] Is there a clear visual entry point at the top of the design?
- [ ] Does the overall color palette match the emotional tone of the message?

## Usage
When a user asks to design, critique, or improve a flyer, apply all principles above. Default to the **Sub-tasks** section: produce the concrete generations (tables, trees, copy deck, build plan, critique). Use **Sub-task A** first only for missing inputs; do not re-ask for information the user already gave.
