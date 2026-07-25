# Troubleshooting

Common failure modes and resolution guidance for the Profile Builder, organized by symptom. Use this when the interview is producing wrong questions, when validation is rejecting valid-seeming inputs, or when the resulting profile JSON doesn't match what the user intended.

**When to consult this file:** When the interview asks unclear or wrong questions for a given schema, when validation rejects an input the user believes is valid, when the output file doesn't write to the expected location, or when the user expresses confusion at any point in the interview.

---

## Table of Contents

1. [Schema and Input Issues](#schema-and-input-issues)
2. [Interview Behavior Issues](#interview-behavior-issues)
3. [Validation Issues](#validation-issues)
4. [Output Issues](#output-issues)
5. [User Experience Issues](#user-experience-issues)

---

## Schema and Input Issues

### Schema not found

**Symptom:** The Skill cannot proceed because no target schema was provided or located.

**Resolution:** Ask the user where the schema is located, or which Skill they're building a profile for so the schema can be located in that Skill's installation directory. Don't attempt to write a profile against an unknown schema — the result would be unvalidated and unsafe to use. If the user names a Skill but the schema isn't in the expected directory, surface that the Skill may not be installed correctly, or that the schema lives at a non-standard path.

### Schema doesn't follow JSON Schema draft-07

**Symptom:** The Skill detects the schema declares a different `$schema` version (draft-04, draft-2019, OpenAPI, custom).

**Resolution:** This Skill requires draft-07 conformance for parsing. Other schema dialects are out of scope. Ask the user to provide a draft-07 schema or convert the existing one. If the schema declares no `$schema` at all, attempt to parse as draft-07 and surface any parse failures specifically.

### Schema includes fields the Skill doesn't recognize

**Symptom:** The schema has properties the Skill encounters but doesn't have explicit handling for.

**Resolution:** The Skill is schema-agnostic; treat unknown fields as standard fields and use the schema's `description` text as the question prompt. If `description` is missing, ask the user to provide a value matching the field's type/constraints with a generic prompt. Flag in the output notes that the field had no plain-language description — the schema author should add one.

### Schema includes custom keywords beyond JSON Schema spec

**Symptom:** The schema uses keywords like `x-custom-validator` or domain-specific extensions.

**Resolution:** Preserve them in the output but ignore them for question generation. Surface in output notes that the schema includes custom keywords the builder didn't process. The custom keywords may still be honored by the consuming Skill at runtime; the builder just doesn't know how to drive an interview from them.

---

## Interview Behavior Issues

### User wants to skip questions

**Symptom:** User responds to a required question with "skip" or refuses to answer.

**Resolution:** Allow it for non-required fields. For required fields, explain why the answer is needed (which schema constraint requires it) and offer the recommended default. If the user still refuses, halt — cannot produce a valid profile without required fields. Don't fabricate values to "make it work."

### User wants advanced control over every field

**Symptom:** Power user wants to set every field explicitly rather than accept defaults.

**Resolution:** Offer the "advanced: review all defaults" mode at the end of the standard interview. Walk through each defaulted field, show value and rationale, accept overrides. This satisfies power users without burdening the standard flow. The advanced mode preserves the same validation logic — overrides still validate against schema constraints.

### Interview asks confusing or redundant questions

**Symptom:** User says the interview is asking strange questions, or asking the same thing twice.

**Diagnosis:** Most often the schema has redundant constraints or unclear `description` fields. The builder is faithfully translating the schema; the schema is the source of confusion.

**Resolution:** Document the friction in the output notes. The right long-term fix is on the schema side — the schema author should consolidate redundant constraints and improve descriptions. The builder can mitigate by deduplicating effectively-identical questions in the same interview, but this is a heuristic and not always reliable.

### Conditional follow-up didn't fire when expected

**Symptom:** User picked an option that should have triggered a follow-up question, but no follow-up appeared.

**Diagnosis:** The conditional dependency in the schema may not be expressed correctly. JSON Schema supports `if/then/else`, `dependencies`, and `oneOf` discriminators — each has different syntax. The builder needs the schema to use one of these constructs explicitly.

**Resolution:** Inspect the schema for the conditional structure. If the dependency is implicit (in the schema author's head but not encoded), add explicit `if/then/else` or `dependencies` blocks. The builder cannot infer dependencies that aren't declared.

---

## Validation Issues

### Validation fails after final answer

**Symptom:** Per-question validation passed for each input, but the final pass over the assembled profile fails.

**Diagnosis:** Should be rare given per-question validation. When it happens, usually the cause is a constraint that depends on multiple fields' values jointly (e.g., `min_pass_count` must be ≤ the length of `required_conditions`).

**Resolution:** Surface the specific JSON Schema validation error in plain language ("The combination of X and Y isn't valid because Z") and re-ask the relevant questions. Don't silently retry or fudge values. If the constraint cannot be satisfied by any combination of valid answers, the schema is over-constrained — surface to the user.

### Validation rejects an input the user believes is valid

**Symptom:** User provides an answer they believe matches the schema, but validation rejects it.

**Diagnosis:** Most common: the user's mental model of the constraint differs from the schema's actual constraint (e.g., user thinks `name` accepts spaces, schema's `pattern` requires kebab-case).

**Resolution:** Surface the specific constraint in plain language ("Name must contain only letters, numbers, and dashes — no spaces or other characters"). If the user disagrees with the constraint itself, that's a schema-design issue, not a builder issue. Suggest they raise it with the schema author.

### Validation passes but consuming Skill rejects the profile

**Symptom:** Builder writes a validated profile, but when the consuming Skill loads it, the Skill rejects it.

**Diagnosis:** The consuming Skill may have additional validation beyond the schema (e.g., severity coverage requirement in critic-gate). The builder's schema-level validation is necessary but not always sufficient.

**Resolution:** Update the consuming Skill's schema to encode the additional constraint (preferred) so the builder can enforce it. As a workaround, the builder can call the consuming Skill's validation method as a final pass — but this requires the consuming Skill to expose a validation API.

---

## Output Issues

### Output path not writable

**Symptom:** Schema validation passes, but the OS prevents writing to the destination path.

**Resolution:** Surface the OS-level error to the user. Offer to write to an alternative path (e.g., the user's home directory) or to display the JSON for manual save. Never silently fail. Common causes: directory doesn't exist (offer to create), permission denied (suggest sudo or alternative path), disk full (surface the error).

### User completes interview but cancels at summary

**Symptom:** User goes through the whole interview, then chooses "no" at the final confirmation.

**Resolution:** Save as a `.draft.json` file in the destination directory if the user wants to resume later. Don't lose the answers. Offer: "Save your answers as a draft to resume later?" If yes, write to `[name].draft.json`. If no, discard cleanly. Mention that drafts can be loaded as starter profiles in a future session.

### Companion notes file fails to write

**Symptom:** The `.notes.md` companion file fails to write even though the JSON file succeeded.

**Resolution:** Surface the error but don't roll back the JSON write. The notes file is for audit trail; the JSON file is the load-bearing artifact. Offer to retry the notes write or skip it.

### User wants to overwrite an existing profile

**Symptom:** Destination path already has a file. Builder needs to decide: overwrite, error, or rename.

**Resolution:** Don't overwrite silently. Show the user the existing file's modification date and ask: "A profile already exists at [path] (last modified [date]). Overwrite, save as a new name, or cancel?" If overwrite, preserve the old file as `.bak` before writing.

---

## User Experience Issues

### User is uncertain on a question

**Symptom:** User responds with "I don't know" or similar uncertainty.

**Resolution:** Provide rationale and a recommendation, then ask for confirmation. Pattern:
1. "[Field] controls [behavior]. The trade-off: [low values produce X] vs [high values produce Y]."
2. "Based on your stated profile purpose ('[user's purpose]'), I recommend [value] because [rationale grounded in the schema's `description` and the profile's purpose]."
3. "Accept the recommendation, or enter your own value?"

If the user remains uncertain after the recommendation, accept the recommended value and proceed.

### User gives an informal answer to a structured question

**Symptom:** User responds "yeah" to a numeric prompt or "sure thing" to a multiple-choice question.

**Resolution:** Interpret charitably and confirm. "I'll take that as accepting the default of X — confirm?" If the user clarifies, walk back and process the actual answer. Don't reject informal phrasing; users shouldn't have to re-type when the intent is clear.

### Interview drags

**Symptom:** User is showing fatigue partway through the interview ("how many more questions?").

**Resolution:** Surface progress: "We're at question 4 of 7 substantive questions. Three more, then summary." If the schema is genuinely too long for one sitting, offer to save as draft and resume later. Long interviews are a sign of either an over-detailed schema or the user not being ready to make all the decisions yet — both warrant pause-and-resume.

### User wants to hand-edit the JSON anyway

**Symptom:** User says "actually, just give me the JSON; I'll edit it myself."

**Resolution:** Respect that. Provide the schema reference, an example template, and exit. The Skill exists for users who don't want to hand-edit; users who do want to should not be forced through the interview. Document that they can still validate hand-edited JSON via the consuming Skill's profile-loading validation.
