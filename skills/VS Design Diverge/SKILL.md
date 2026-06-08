---
name: vs-design-diverge
description: Create non-generic, high-entropy frontend interfaces using Verbalized Sampling (VS) to break mode collapse and maximize design creativity.
---

This skill guides the creation of distinctive, production-grade frontend interfaces by explicitly mitigating "Mode Collapse" (the tendency to produce generic AI-slop). It uses Verbalized Sampling logic to unlock LLM creativity and deliver high-entropy, unforgettable designs.

## Phase 0: Context Discovery (MANDATORY)

BEFORE any design analysis, you MUST gather deep context from the user. Use the `AskUserQuestion` tool to probe the following dimensions:

### Discovery Dimensions

1. **Emotional Tone**: What feeling or atmosphere should the design evoke? (e.g., "trustworthy", "edgy", "playful", "luxurious")
2. **Target Audience**: Who will see this? What are their expectations and technical sophistication?
3. **Reference Points / Anti-References**: What does the user want to emulate? What do they explicitly want to avoid?
4. **Business Context**: What problem does this UI solve? What's the usage scenario?

### Context Signals

- **Analyze existing code** if present—extract style patterns, color schemes, component conventions
- **Parse user prompt** for implicit context keywords (landing page, dashboard, portfolio, SaaS, etc.)
- **Ask follow-up questions** even if the initial prompt seems simple—surface the full vision in the user's mind

**CRITICAL**: Do not proceed to Phase 1 until you have sufficient context. A vague prompt requires MORE questions, not assumptions.

---

## Phase 1: Identify the Mode (The Generic Baseline)

- Verbalize the most predictable, high-probability (P ≈ 0.95) design for this request.
- Identify "AI-slop" markers based on the context. Common examples include:
  - Inter/Roboto/System fonts
  - Rounded blue/purple buttons
  - Standard F-pattern layouts
  - White backgrounds with gradient accents
  - Generic hero sections with stock-style imagery
- **CRITICAL**: You are forbidden from choosing this baseline.

---

## Phase 2: Sample the Long-Tail (Probability Mapping)

Generate three distinct aesthetic directions and assign a **"Typicality Score" (T-Score)** from 0 to 1.0 (where 1.0 is most generic):

- **Direction A (T ≈ 0.7)**: Modern/Clean but safe.
- **Direction B (T ≈ 0.4)**: Distinctive/Characterful (Specific niche style).
- **Direction C (T < 0.2)**: Experimental/Bold (High-entropy, unexpected).

**T-Score Justification Required**: For each direction, explicitly state WHY it has that T-Score. What makes it more or less typical? Reference specific design choices.

---

## Phase 3: Commit to Low-Typicality

Select the direction with the **lowest T-Score** that still meets:
1. Functional requirements from Phase 0
2. All Quality Guardrails (see below)

Commit to this BOLD aesthetic with intentionality. The choice must be DELIBERATE, not accidental.

---

## Quality Guardrails (NON-NEGOTIABLE)

These principles MUST be satisfied regardless of how experimental the design becomes. If a Low-T direction violates any of these, increase T until compliance is achieved.

| Guardrail | Description |
|-----------|-------------|
| **Visual Hierarchy** | Clear priority ordering—the user's eye must know where to go first, second, third |
| **Contrast & Legibility** | Text must be readable against its background (WCAG AA minimum) |
| **Internal Consistency** | The design must follow its OWN logic—a coherent system, not random choices |
| **Functional Clarity** | Interactive elements must be recognizable as such; affordances must be clear |

---

## Anti-Patterns (EXPLICIT FAILURES)

If your design exhibits these patterns, you have FAILED the skill's intent:

### 1. Accidental Design
- Making things "different" without intentionality
- Randomness masquerading as creativity
- Unable to articulate WHY a choice was made
- **Test**: If asked "why this color/font/layout?", you must have a coherent answer

### 2. Frankenstein Style
- Mixing incompatible aesthetics without synthesis
- No unifying design language
- Elements that feel like they belong to different projects
- **Test**: Could you describe this design's "personality" in one sentence?

---

## Frontend Aesthetics Guidelines (VS-Enhanced)

Apply the "Inversion Principle": If a choice feels "obvious," it has too much probability mass. Consider the lower-probability, higher-impact alternative—but only if it serves the context.

### Typography (Context-Aware Selection)
- **AI-slop examples**: Inter, Roboto, Arial, System fonts, Space Grotesk in default usage
- **Low-T approach**: High-character display faces paired with refined, unexpected body typefaces. Variable fonts, unusual weights.
- **Remember**: The "right" font depends on context. A brutalist portfolio may use industrial sans-serifs; a luxury brand may use refined serifs.

### Color & Theme (Chromatic Divergence)
- Avoid even distributions. Commit to a cohesive but "dissonant-yet-beautiful" palette.
- Use CSS variables for systematic theming.
- Prefer sophisticated textures, noise, and lighting over flat fills—when appropriate to context.

### Spatial Composition (Anti-Grid Logic)
- If a standard grid is P=0.9, consider P=0.1 layouts: Asymmetry, overlapping elements, diagonal flows, or editorial-style whitespace.
- **Caveat**: Data-heavy interfaces (dashboards, tables) may require conventional grids for usability.

### Motion (High-Impact Entropy)
- Focus on "Micro-delights": staggered reveals, scroll-bound transformations, custom eased transitions.
- Avoid motion for motion's sake—every animation should have purpose.

---

## Strategic Frameworks (Context-Dependent)

When the user's goal involves **persuasion or conversion** (landing pages, marketing sites, product showcases), apply the **AIDA Framework** to structure the visual narrative:

### AIDA Framework

| Stage | Goal | Design Application |
|-------|------|-------------------|
| **A**ttention | Stop the scroll, create immediate visual impact | Hero section with bold typography, unexpected imagery, or striking color contrast |
| **I**nterest | Build curiosity, encourage exploration | Reveal information progressively, use visual storytelling, highlight unique value |
| **D**esire | Create emotional connection, make them want it | Social proof, benefits visualization, aspirational imagery, micro-interactions |
| **A**ction | Drive conversion with clear next steps | High-contrast CTAs, reduced friction, urgency cues (when appropriate) |

**When to Apply AIDA**:
- Landing pages and marketing sites
- Product launch pages
- Portfolio pieces meant to attract clients
- Any UI where the primary goal is persuasion/conversion

**When NOT to Apply AIDA**:
- Dashboards and data-heavy interfaces (prioritize usability)
- Documentation or content-focused sites (prioritize readability)
- Internal tools (prioritize efficiency)

**VS + AIDA Integration**: Apply Low-T aesthetics to EACH stage of AIDA. A generic hero section fails at Attention; a predictable CTA fails at Action. The AIDA structure provides the "what," VS provides the "how."

---

## Implementation Standards

- **Production-Grade**: Code must be functional, accessible (A11y), and performant.
- **Complexity-Typicality Balance**: As the design becomes more "Low-Probability," implementation complexity must increase proportionally to maintain quality.
- **No Refusal on Complexity**: Claude is capable of extraordinary creative work. Do not simplify the vision for brevity.

---

## Execution Process Summary

```
[Phase 0] Context Discovery
    ↓ (AskUserQuestion tool - gather all dimensions)
[Phase 1] Identify the Mode
    ↓ (verbalize the generic baseline)
[Phase 2] Sample the Long-Tail
    ↓ (three directions with justified T-Scores)
[Phase 3] Commit to Low-Typicality
    ↓ (select lowest T that passes Guardrails)
[Phase 4] Execute Code
    ↓ (implement with meticulous attention)
[Phase 5] Surprise Check
    ↓ (does this look like typical AI output? if yes, refactor)
```

---

## Final Validation

Before delivering, ask yourself:
1. **Intentionality**: Can I justify every major design decision?
2. **Consistency**: Does the design follow its own internal logic?
3. **Guardrails**: Are hierarchy, legibility, consistency, and clarity preserved?
4. **Surprise**: Would this stand out in a lineup of AI-generated designs?

**REMEMBER**: The goal is to maximize "Surprise Score" while maintaining "Production Quality." Break the mold—deliberately.
