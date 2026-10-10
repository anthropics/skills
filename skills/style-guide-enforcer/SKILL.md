---
name: style-guide-enforcer

description: Apply documentation style standards to AI-generated content at creation time — not as a post-creation checklist. Use this skill when the user wants to enforce style guide rules during content generation, has a style guide or documentation standards document to apply, or wants consistent terminology, voice, and formatting across generated content.

license: Complete terms in LICENSE.txt
---

# Style Guide Enforcer

Apply documentation style standards during content creation — not after.

## When to Use This Skill

Use this skill when the user has a style guide or documentation standards to apply during content generation, wants consistent terminology and formatting across generated content, or needs AI output to comply with a specific style standard.

Do not use this skill when the user has no style guide or standards to apply, or wants freeform prose without style constraints.

## Inputs Required

1. **Style guide or standards reference** — the specific document, rules, or key standards to apply
2. **Content to generate or review** — the documentation content in scope
3. **Product terminology** — confirmed terms for UI elements, features, and workflows

## Step-by-Step Workflow

1. **Identify the style guide** — Confirm which single style guide the user is applying. Do not apply multiple guides simultaneously — they produce conflicting rules. See the Reference table below for domain-matched options.
2. **Load terminology** — Confirm the product terminology source. If none is provided, ask the user before proceeding.
3. **Apply standards during generation** — Apply style rules at the point of content creation. Do not produce content first and apply style second — this produces inconsistency.
4. **Flag unknown terms** — If any term appears in the content that is not in the confirmed terminology source, flag it explicitly. Do not invent synonyms.
5. **Verify consistency** — After generation, confirm that parallel topics use the same structure, equivalent UI interactions follow the same pattern, and terminology is applied consistently across all content in scope.

## Application Rules

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

## Examples

### Before and After — Active Voice

**Before (passive):**
"The Export button can be selected to generate the report."

**After (active):**
"Select **Export** to generate the report."

### Before and After — Terminology Enforcement

**Before (inconsistent):**
"To delete the route, click Remove. If you want to erase the flight plan, press Delete."

**After (consistent terminology):**
"To remove the route, select **Remove**. To remove the flight plan, select **Delete**."

### Before and After — Heading Hierarchy

**Before (inconsistent levels):**
```
# Configuration
## Settings
### Display Options
## Configuring the Map
```

**After (correct hierarchy):**
```
# Configuration
## Display Options
## Map Configuration
```

## Common Edge Cases

- **User provides multiple style guides** — Select one based on the user's domain. Ask which to apply if domain is ambiguous.
- **Style guide conflicts with product terminology** — Product terminology takes precedence. Flag the conflict for the user.
- **No product terminology source provided** — Do not proceed without one. Ask the user to supply confirmed terminology before generating content.

## Reference

Select one style guide based on your industry and domain. Applying multiple guides simultaneously will produce conflicting rules.

| Style Guide | Domain |
|---|---|
| [Microsoft Writing Style Guide](https://learn.microsoft.com/en-us/style-guide/welcome/) | Software and UI documentation |
| [Google Developer Documentation Style Guide](https://developers.google.com/style) | Developer and API documentation |
| [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/) | Aerospace, defense, and safety-critical systems |
| [Plain Language Guidelines — GSA](https://github.com/gsa/plainlanguage.gov) | U.S. federal and regulated-industry content |
| [Apple Style Guide](https://developer.apple.com/documentation/styleguide) | iOS, macOS, and Apple platform documentation |

## Validation Requirement

Style-compliant content must still be tested against actual application behavior before publication. Style compliance does not detect operationally insufficient content — procedures that use correct terminology and formatting but omit prerequisite conditions, misrepresent sequence dependencies, or fail to convey what the user needs to know. The person performing this validation must have direct knowledge of the end user's operational context.
