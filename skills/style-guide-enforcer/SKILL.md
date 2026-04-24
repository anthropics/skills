---
name: style-guide-enforcer

description: Apply documentation style standards to AI-generated content at creation time — not as a post-creation checklist. TRIGGER when: user wants to enforce style guide rules during content generation; user has a style guide or documentation standards document to apply; user wants consistent terminology, voice, and formatting across generated content. SKIP: user has no style guide or standards to apply; user wants freeform prose without style constraints.

license: MIT
---

# Style Guide Enforcer

Apply documentation style standards during content creation — before validation, not after.

## Inputs Required

1. **Style guide or standards reference** — provide the document, rules, or key standards to apply. Examples: Microsoft Writing Style Guide (software/UI documentation); Google Developer Documentation Style Guide (developer and API documentation); ASD-STE100 Simplified Technical English (aerospace and defense technical documentation); Plain Language Guidelines — plainlanguage.gov (U.S. federal and regulated-industry content)
2. **Content to generate or review** — the documentation content in scope
3. **Product terminology** — confirmed terms for UI elements, features, and workflows

## Application Rules

Apply style standards at the point of generation. Do not produce content first and apply style second — this produces inconsistency.

### Terminology
- Use only confirmed product terminology from the provided source
- Flag any term not found in the source inputs — do not invent synonyms
- Apply terminology consistently across all topics in scope

### Voice and Tone
- Apply the voice specified in the style guide
- Default to active voice and direct address ("Select X" not "X can be selected")
- Size sentences for users working under time pressure — short, unambiguous

### Formatting
- Apply heading hierarchy as specified
- Apply list formatting rules as specified
- Apply note, warning, and caution conventions as specified

### Consistency
- Maintain consistent structure across parallel topics
- Apply the same pattern for equivalent UI interactions throughout

## Reference

Authoritative style guides supported by this skill:
- [Microsoft Writing Style Guide](https://learn.microsoft.com/en-us/style-guide/welcome/)
- [Google Developer Documentation Style Guide](https://developers.google.com/style)
- [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/)
- [Plain Language Guidelines — plainlanguage.gov](https://www.plainlanguage.gov/guidelines/)

## What This Skill Does Not Do

Style compliance does not substitute for behavioral validation. Stylistically correct content can still be operationally insufficient. Stage 3 validation is required regardless of style compliance.
