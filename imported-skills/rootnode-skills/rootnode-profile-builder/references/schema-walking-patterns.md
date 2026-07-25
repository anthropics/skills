# Schema-Walking Patterns

The full reference for translating JSON Schema constructs into conversational interview questions. The Profile Builder is schema-agnostic — it generates the interview from the target schema's structure. This file documents how each common schema shape maps to interview behavior, including conditional dependencies, nested objects, polymorphic types (oneOf/anyOf), and arrays.

**When to consult this file:** When implementing or extending the Profile Builder's schema parsing logic, when debugging an interview that doesn't ask the right questions for a given schema shape, when authoring a schema that the builder will consume (and wanting to know how the schema's structure will translate to questions), or when a user asks why the interview asked or didn't ask a specific question.

---

## Table of Contents

1. [Required Fields vs Optional Fields](#required-fields-vs-optional-fields)
2. [Object Properties](#object-properties)
3. [Enum Fields](#enum-fields)
4. [Polymorphic Types — oneOf / anyOf / allOf](#polymorphic-types--oneof--anyof--allof)
5. [Arrays](#arrays)
6. [Conditional Dependencies — if / then / else](#conditional-dependencies--if--then--else)
7. [Nested Objects](#nested-objects)
8. [Worked Walkthrough Examples](#worked-walkthrough-examples)

---

## Required Fields vs Optional Fields

The schema's `required` array drives mandatory questions. The interview must produce a value for every required field; optional fields may be skipped.

**For required fields:** ask. Validate. Re-ask if invalid. If the user refuses to provide a value, halt and explain — the schema requires it, the builder cannot fabricate it.

**For optional fields:** offer in Tier 4 ("Optional details") or skip entirely. Provide defaults from `default` in the schema if present; otherwise leave the field absent from output.

**Edge case — required at conditional depth:** A field may be required only when a sibling field has a specific value (`if X = "weighted" then condition_weights required`). The required-status is dynamic. Track the conditional state during the interview and only ask for the conditionally-required field when its trigger condition is met.

---

## Object Properties

The schema's `properties` object enumerates the fields. For each property, the schema specifies:
- `type`: drives input parsing (string / integer / boolean / array / object)
- `description`: used as the question prompt when no plain-language override exists
- `default`: drives default offering
- `enum`: drives multiple-choice
- Constraints (`minimum`, `maximum`, `pattern`, `minLength`, `maxLength`): drive per-question validation

### Walking properties

Walk properties in this order:
1. Identity properties (typically `name`, `description`) — Tier 1
2. Required substantive properties (the fields that determine the profile's shape) — Tier 2
3. Numeric properties with sensible defaults — Tier 3
4. Optional properties — Tier 4

The order isn't always declared in the schema; use field-name heuristics + required status + presence of `default` to bucket them.

### When `description` is missing

The schema's `description` is the primary source for question prompts. When absent:
- Use the field name converted to plain English (`min_pass_count` → "Minimum number that must pass")
- Append a constraint summary if helpful ("must be between 1 and 7")
- Ask the user to provide a value matching the type
- Flag in the output notes that the field had no schema description (the schema author should add one)

---

## Enum Fields

Enums drive multiple-choice questions. The Profile Builder's most important translation: **never expose machine names**. Always describe what each enum value means operationally.

### Enum walking pattern

For an enum `["all_must_pass", "min_count", "weighted"]`:

```
How strict should this be?
  (a) Every condition must pass — strictest, for unattended runs.
  (b) Most conditions must pass — balanced.
  (c) Weight conditions by importance — advanced.
```

Map (a) to `all_must_pass`, (b) to `min_count`, (c) to `weighted`. The user picks a letter; the builder writes the machine name.

### When the schema has enum descriptions

Some schemas attach `description` to each enum value (in `oneOf` form with `const` + `description`). When present, use those descriptions verbatim in the question — the schema author has done the translation work.

### When the enum is large (>5 options)

Group into categories. Don't present 12 options in a flat list. Group by purpose ("Strict options:" / "Balanced options:" / "Lenient options:") and offer the categories first, then the within-category options.

### When the enum has hidden semantic ordering

If the enum represents a spectrum (`strict` → `balanced` → `lenient`), order the options along the spectrum in the prompt. Don't surface them in alphabetical or schema-declaration order if a meaningful semantic order exists. The semantic order helps users locate themselves on the spectrum.

---

## Polymorphic Types — oneOf / anyOf / allOf

Polymorphic types are the most complex schema construct the builder handles. The interview must determine which variant applies, then ask the variant-specific questions.

### oneOf — exactly one variant

`oneOf` means the value must match exactly one of the listed schemas. The interview should:
1. Determine the discriminator (a property whose value selects the variant). Most well-designed `oneOf` schemas have an explicit discriminator field.
2. Ask the discriminator question first.
3. Branch into the variant-specific schema and walk it as a sub-interview.

**Example:** A `trigger` field with `oneOf` for time_window, geofence, calendar, custom_signal:

```
What kind of trigger fires this rule?
  (a) Time of day / day of week
  (b) Location (geofence label)
  (c) Calendar event
  (d) Custom signal
```

After the user picks (a), walk the time_window variant's schema to ask `start_time`, `end_time`, `days_of_week`. The other variants' fields are not asked.

### anyOf — at least one variant

`anyOf` is rarer but means the value must match at least one variant. The interview should:
1. Ask which variants apply (multiple-select).
2. Walk each selected variant's required fields.
3. Merge the answers into a single object satisfying all selected variants.

In practice, `anyOf` often indicates a schema that should be `oneOf` with a clearer discriminator. If the user is confused by the multi-select, that's a schema design issue worth raising back to the schema author.

### allOf — all variants required

`allOf` means the value must match all listed sub-schemas. Treat as a single combined schema: walk all required fields from all sub-schemas. Conflicts (same field with different constraints) are a schema bug; surface to the user and halt.

---

## Arrays

The schema's `items` defines the array element shape. The interview should:
1. Ask how many items the user wants to add.
2. For each item, walk the item shape (which is itself a schema, possibly nested).
3. Validate the array's `minItems` / `maxItems` / `uniqueItems` constraints.

### Array walking patterns

**Fixed-size arrays (e.g., `minItems: 7, maxItems: 7`):** Don't ask "how many" — walk all 7 items in sequence with descriptive labels ("First condition: ...", "Second condition: ...").

**Open-ended arrays:** Ask "how many [items] do you want to add?" Default to 0 unless `minItems > 0`. Each added item walks the item schema as a sub-interview.

**Arrays of strings with `enum` constraint:** Multiple-select question. Show all enum options; user picks zero or more. Validate `minItems` after selection.

**Arrays of objects:** Walk each item as a nested sub-interview. Number them in the output ("Item 1 of 3:") so the user knows where they are.

### Empty arrays

When the schema allows empty arrays (`minItems: 0` or absent), offer the user a "skip — leave empty" option in addition to "add an item." Don't force an item just because the field exists.

---

## Conditional Dependencies — if / then / else

JSON Schema draft-07 supports `if/then/else` for conditional shape. The pattern: when a property has a specific value, additional properties become required (or different constraints apply).

### Conditional walking

When the interview reaches a property that's an `if` trigger (e.g., `threshold_rule`), the answer to that property determines downstream questions:

```
"How strict should this be?"
  → user picks "weighted"
"You picked weighted thresholds. I need to know the weight per condition.
 Walking conditions one at a time..."
  → walks the conditional `then` block's required fields
```

If the user picks an option that has no `then` block (e.g., `all_must_pass` requires no further info), skip the dependent block entirely.

### Schema dependencies (`dependencies` keyword)

Older draft-07 syntax uses `dependencies` for the same pattern. Treat it equivalently — when the named property is set, the dependent fields become required.

### Conditional anti-pattern in schemas

If the schema has many nested if/then/else structures, the interview becomes hard to navigate. Surface this back to the schema author — usually the right answer is to break the schema into multiple `oneOf` variants instead of one schema with deep conditionals.

---

## Nested Objects

When a property's type is `object`, walk its sub-schema as a nested interview. Use indentation in the question prompts to signal the nesting:

```
Building budget data source for this profile...
  > Where does budget data come from?
    (a) Manual input each time
    (b) Live telemetry feed
    (c) Config file
  > [if (b)] What's the telemetry feed URL?
  > [if (b)] How often should the value be refreshed?
```

Limit nesting depth to 2-3 levels for readability. If the schema requires deeper nesting, the questions should still flow naturally; if they don't, that's a schema-design issue.

---

## Worked Walkthrough Examples

### Example walkthrough — handoff-trigger-check profile from scratch

The handoff-trigger-check schema has these top-level properties: `name`, `description`, `threshold_rule` (enum), `min_pass_count` (conditional on threshold_rule), `required_conditions` (array of enums), `budget_safety_margin` (number), `budget_data_source` (oneOf with discriminator).

Walking it produces this interview:

1. **Tier 1 — Identity:** "What should this profile be called?" (suggested: based on user's stated context)
2. **Tier 1 — Purpose:** "When does this profile apply? One sentence."
3. **Tier 2 — Strictness (enum):** "How strict should the gate be? (a) Every condition must pass — strictest. (b) Most conditions must pass — balanced. (c) Weight conditions by importance — advanced."
4. **Tier 2 — Conditional follow-up:** If user picked (b), ask "How many conditions must pass at minimum?" (suggested 5 of 7)
5. **Tier 2 — Required conditions (array enum, multi-select):** "Are any conditions required regardless of count? Pick zero or more." Show all 7 conditions with plain-language descriptions; user multi-selects.
6. **Tier 3 — Budget margin (number):** "How much budget headroom do you want? Suggested: 1.1x (because [rationale])."
7. **Tier 2 — Budget data source (oneOf discriminator):** "Where does budget data come from? (a) Manual input. (b) Live telemetry. (c) Config file. (d) No check."
8. **Tier 2 — Conditional follow-up:** If (b), ask "What's the telemetry feed URL?"
9. **Tier 4 — Optional notes:** "Want to add notes or advanced settings? (y/n)"
10. **Summary + confirm + write.**

The interview is 7-9 substantive questions, each one driven by the schema's structure. No machine names appear in any prompt.

### Example walkthrough — cloning an existing profile

Starting with an existing `desk` profile, building `overnight`:

1. Load `desk.json` as the starter object.
2. **Show:** "Cloning from `desk` profile. Most settings will copy; I'll ask only about what should change for overnight use."
3. **Ask name:** "Name for the new profile?" (suggest `overnight`)
4. **Walk delta — only the substantive Tier 2 questions get re-asked, with the existing values shown and the recommendation framed as a delta:**
   - "Strictness: change from min_count(5) to all_must_pass? (Recommended for unattended runs.)"
   - "Budget margin: change from 1.1x to 1.3x? (Recommended because you can't correct mid-run.)"
   - "Anything else to change?"
5. **Summary highlighting deltas + confirm + write.**

The clone walk is faster than fresh because most fields copy; only the user-flagged changes get re-asked.

### Example walkthrough — user uncertain on a question

When the user says "I don't know" to any question:

1. Provide rationale: "[Field] controls [behavior]. The trade-off: [outcome of low values] vs [outcome of high values]."
2. Recommend a value based on the user's stated profile purpose.
3. Ask: "Accept the recommendation, or enter your own value?"

This pattern is the same regardless of schema shape — the recommendation is grounded in the field's semantic meaning, drawn from the schema's `description` field plus the profile's stated purpose. If the user remains uncertain after the recommendation, accept the recommended value and proceed.
