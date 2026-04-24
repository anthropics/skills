---
name: dita-xml

description: Generate structured DITA XML documentation from source inputs — codebase, existing end-user documentation, and audience context. Produces concept, task, and reference topic types. TRIGGER when: user wants to generate DITA-structured documentation from product source files; user needs topic-typed XML output (concept/task/reference); user is documenting software procedures or UI workflows in DITA format. SKIP: user wants plain prose or Markdown output; user is not working with DITA or XML-based documentation systems.

license: MIT
---

# DITA XML Documentation Generator

Generate structured DITA XML documentation grounded in actual product behavior.

## Inputs Required

Before generating content, confirm these inputs are available in the session:

1. **Application source** — codebase, UI specifications, or API definitions
2. **Existing end-user documentation** — validated documentation for this product if available
3. **Topic type** — concept, task, or reference
4. **Audience** — who this documentation is for and their operational context

## Topic Type Selection

| Topic Type | Use When |
|---|---|
| `<concept>` | Explaining what something is or how it works |
| `<task>` | Documenting a procedure the user performs |
| `<reference>` | Documenting UI elements, fields, options, or parameters |

## Generation Rules

- Ground all content in the provided source inputs — do not generate from general knowledge
- For task topics: each step must correspond to a verifiable action in the application
- For concept topics: descriptions must reflect actual system behavior, not general software patterns
- For reference topics: field names, values, and defaults must match the source exactly
- Apply short-form steps sized for users working under operational pressure
- Do not include prerequisites, warnings, or conditions that are not verifiable from the source inputs — flag gaps for the domain expert to resolve

## Output Format

Produce valid DITA 1.3 XML topics. Use standard DITA 1.3 element structure. Do not invent custom elements or attributes.

## Reference

This skill applies the DITA 1.3 standard as defined by OASIS:
- [DITA 1.3 Specification](https://docs.oasis-open.org/dita/dita/v1.3/dita-v1.3-part0-overview.html)
- [DITA 1.3 Element Reference](https://docs.oasis-open.org/dita/dita/v1.3/errata02/os/complete/part3-all-inclusive/langRef/containers/concept-elements.html)

## Validation Reminder

Output from this skill requires Stage 3 behavioral validation by the domain-expert technical communicator before publication. Generated content is a starting point, not a finished deliverable.
