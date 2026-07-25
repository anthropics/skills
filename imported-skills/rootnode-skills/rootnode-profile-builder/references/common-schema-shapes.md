# Common JSON Schema Shapes — Quick Reference

A targeted reference for the JSON Schema draft-07 constructs the Profile Builder encounters most often. Each entry names the construct, what it does in the schema, and how the builder should translate it into interview behavior.

**When to consult this file:** When a schema uses a construct the builder isn't handling well, when authoring a schema and wanting to know how a construct will be interpreted, when extending the builder to handle a new construct, or when debugging an interview that's misinterpreting a schema feature.

---

## Table of Contents

1. [Type Constructs](#type-constructs)
2. [Validation Constraints](#validation-constraints)
3. [Composition Constructs](#composition-constructs)
4. [Reference and Reuse](#reference-and-reuse)
5. [Annotation Constructs](#annotation-constructs)
6. [Constructs the Builder Cannot Handle](#constructs-the-builder-cannot-handle)

---

## Type Constructs

### `type: string`

The most common type. Builder asks for free-text input. Validates against any string-specific constraints (`minLength`, `maxLength`, `pattern`, `format`).

**Builder behavior:** "What should [field] be?" — single-line input, validated.

### `type: integer` / `type: number`

Numeric input. Distinguishes between integer (no fractional part) and number (any numeric).

**Builder behavior:** "What should [field] be? (must be [constraint summary])" — parsed and validated. Reject non-numeric input with a re-ask.

### `type: boolean`

Yes/no input.

**Builder behavior:** "[Field]? (y/n)" — accept y/yes/true → true; n/no/false → false. Reject anything else with a re-ask.

### `type: array`

Multiple values. See `arrays` section in `schema-walking-patterns.md` for full walking semantics.

### `type: object`

Nested object. Walk as a sub-interview. See `nested objects` section in `schema-walking-patterns.md`.

### `type: null`

Rare. The field's value must be null. Builder doesn't ask — it just sets the value to null. Surface in summary as "Will be set to null per schema."

### `type: [array of types]`

The field can be one of several types. Most common: `["string", "null"]` for nullable fields. Builder asks first whether to set a value at all; if yes, asks for the value.

---

## Validation Constraints

### `minimum` / `maximum` / `exclusiveMinimum` / `exclusiveMaximum`

Numeric bounds. Builder shows them in the prompt: "Must be between X and Y" or "Must be at least X."

### `minLength` / `maxLength`

String length bounds. Builder shows in prompt: "Length between X and Y characters."

### `minItems` / `maxItems`

Array size bounds. Builder enforces by either asking the user how many to add (open-ended arrays) or walking a fixed count (bounded arrays). See `schema-walking-patterns.md`.

### `uniqueItems`

Array elements must be unique. Builder validates after each addition; if duplicate, re-ask with explanation.

### `pattern`

Regex pattern for strings. Builder validates input against the pattern. On failure, show the pattern in plain language if possible ("Must contain only letters, numbers, and dashes") or surface the regex if no plain-language description fits.

### `format`

Hint for the string's intended format. Common values:
- `date-time` → ISO-8601 timestamp
- `email` → email address
- `uri` / `url` → URL
- `uuid` → UUID

Builder validates the format and offers an example in the prompt ("Format: ISO-8601 timestamp, e.g., 2026-05-01T14:30:00-07:00").

### `multipleOf`

Numeric value must be a multiple of N. Builder shows in prompt and validates.

### `enum`

Restricted to a list of values. Builder converts to multiple-choice. See `Enum Fields` in `schema-walking-patterns.md`.

### `const`

Field must be a single specific value. Builder doesn't ask — it sets the value automatically and notes it in the summary.

---

## Composition Constructs

### `oneOf`

Value must match exactly one of the listed sub-schemas. The interview must determine which variant applies via a discriminator field. See `Polymorphic Types` in `schema-walking-patterns.md`.

### `anyOf`

Value must match at least one sub-schema. Multi-select question. Less common than `oneOf` and often a sign of schema design issues. See `Polymorphic Types`.

### `allOf`

Value must match all sub-schemas combined. Builder walks the union of required fields from all sub-schemas. Conflicts between sub-schemas are schema bugs.

### `not`

Value must NOT match the listed sub-schema. Rare in profile schemas. Builder validates after collecting the value but cannot directly drive question phrasing — it's a post-validation construct.

### `if / then / else`

Conditional dependency. When `if` matches, `then` applies; otherwise `else`. See `Conditional Dependencies` in `schema-walking-patterns.md`.

### `dependencies` (or `dependentRequired` / `dependentSchemas`)

Older syntax for conditional dependencies. Treat equivalently to `if/then/else`.

---

## Reference and Reuse

### `$ref`

Reference to another schema location. Builder resolves the reference and walks the referenced schema as if it were inline.

**Internal references** (`#/definitions/foo`): resolve within the current schema document.

**External references** (`https://example.com/schema.json`): the builder typically operates on schemas from local files (the consuming Skill's `schema/` directory). External `$ref` references are rare for profile schemas; if encountered, the builder should fetch and resolve, but most deployment scenarios use local-only schemas.

**Circular references:** Detect and halt with a clear error. The interview cannot walk a cycle. Schema author needs to break the cycle.

### `definitions` (or `$defs` in draft-2019)

Reusable sub-schemas referenced via `$ref`. Builder treats them as the target of `$ref` resolution; doesn't ask about them directly.

---

## Annotation Constructs

### `description`

Plain-language description of the field. Builder uses it as the question prompt. **Always prefer the schema's description over auto-generated prompts** — the schema author has done the translation work.

### `title`

Short label for the field. Builder uses it as a section header when the field is part of a nested object or polymorphic variant.

### `default`

The field's default value. Builder offers it as the suggested answer with rationale: "Suggested: [default]. Accept, or enter your own value?"

If `default` and the user's answer differ, note the override in the summary.

### `examples`

Sample valid values. Builder shows one example in the prompt to clarify the expected shape: "e.g., 'desk', 'overnight'."

### `readOnly`

Field is informational; not user-set. Builder doesn't ask — it sets the value if a default is present, or skips if no default.

### `deprecated`

Field is being phased out. Builder skips it during interview unless the user is editing an existing profile that has the field set. Surface deprecation in the summary if the field is present.

---

## Constructs the Builder Cannot Handle

Some JSON Schema constructs are out of scope for the Profile Builder. When encountered:

### Schemas requiring runtime context the builder doesn't have

If a field's validity depends on data only available at execution time (e.g., "must be the ID of an existing record in the database"), the builder cannot validate. Accept the user's input as-is and document the validation gap in the output notes.

### `propertyNames` constraint

Constrains the names of object properties. Rare in profile schemas. If encountered, the builder doesn't ask about it directly; it validates property names as the user adds them to objects with `additionalProperties`.

### `patternProperties`

Object properties matching a pattern. The builder offers "add a property" with a name pattern hint, then walks the property's value schema.

### Custom keywords / vocabularies

JSON Schema allows custom keywords beyond the core spec. The builder should preserve them in the output but ignore them for question generation. Surface in output notes that the schema includes custom keywords the builder didn't process.

### Schema versions other than draft-07

The builder is designed for draft-07. Other versions (draft-04, draft-06, draft-2019, draft-2020) have similar but not identical syntax. If the schema declares a different `$schema`, halt with an explanation: "This builder supports draft-07 only. Convert the schema or use a different builder."
