# Source: Pasted Text

Use when the user pastes manuscript prose, abstract, methods, or notes
directly into the chat.

## Provenance tagging

- Each paragraph is tagged `P001, P002, ...` in user-supplied order.
- Equations are flagged with their original LaTeX/MathML and given `E001...`.
- Figures are described in prose and tagged `F001...` (assumed available).

## Risk flags

- Provenance is weaker than PDF — there is no per-page locator. Use
  paragraph numbers or section headers as the locator string.
- User may have omitted the limitations or future-work sections. Ask
  before assuming absence.
