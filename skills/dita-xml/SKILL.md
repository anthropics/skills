---
name: dita-xml

description: Generate structured DITA 1.3 XML documentation from source inputs — codebase, existing end-user documentation, and audience context. Produces concept, task, and reference topic types. Use this skill when the user wants to generate DITA-structured documentation from product source files, needs topic-typed XML output, or is documenting software procedures or UI workflows in DITA format.

license: Complete terms in LICENSE.txt
---

# DITA XML Documentation Generator

Generate structured DITA XML documentation grounded in actual product behavior.

## When to Use This Skill

Use this skill when the user wants to generate DITA-structured documentation from product source files, needs topic-typed XML output (concept/task/reference), or is documenting software procedures or UI workflows in DITA format.

Do not use this skill for plain prose or Markdown output, or when the user is not working with DITA or XML-based documentation systems.

## Inputs Required

Before generating content, confirm these inputs are available in the session:

1. **Application source** — codebase, UI specifications, or API definitions
2. **Existing end-user documentation** — validated documentation for this product if available
3. **Topic type** — concept, task, or reference
4. **Audience** — who this documentation is for and their operational context

## Step-by-Step Workflow

1. **Confirm inputs** — Verify all required inputs are available. If any are missing, ask the user before proceeding.
2. **Select topic type** — Choose the appropriate DITA topic type based on the content purpose:
   - `<concept>` — explaining what something is or how it works
   - `<task>` — documenting a procedure the user performs
   - `<reference>` — documenting UI elements, fields, options, or parameters
3. **Extract from source** — Ground all content in the provided source inputs. Do not generate from general knowledge.
4. **Generate XML** — Produce valid DITA 1.3 XML using standard element structure. Do not invent custom elements or attributes.
5. **Verify against source** — For task topics, confirm each step corresponds to a verifiable action. For concept topics, confirm descriptions reflect actual system behavior. For reference topics, confirm field names, values, and defaults match the source exactly.
6. **Behavioral validation required** — The user must test generated procedures against actual application behavior before publication. This step is not optional. AI-generated content can be technically accurate against source inputs but operationally insufficient — correct descriptions that fail to convey what users need to know, omit prerequisite conditions, or misrepresent sequence dependencies. These errors are invisible without hands-on testing by someone with direct knowledge of the user's operational context.

## Generation Rules

- For task topics: each step must correspond to a verifiable action in the application
- For concept topics: descriptions must reflect actual system behavior, not general software patterns
- For reference topics: field names, values, and defaults must match the source exactly
- Apply short-form steps sized for users working under operational pressure
- Do not include prerequisites, warnings, or conditions not verifiable from source inputs — flag gaps for the domain expert to resolve

## Examples

### Task Topic

**Input:** User provides API endpoint documentation and asks for a task topic on authenticating API requests.

**Output:**

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE task PUBLIC "-//OASIS//DTD DITA 1.3 Task//EN" "task.dtd">
<task id="api-authentication">
  <title>Authenticate API Requests</title>
  <taskbody>
    <context>Before calling any API endpoint, you must authenticate your request with a valid API key.</context>
    <steps>
      <step>
        <cmd>Open your API dashboard and copy your API key.</cmd>
      </step>
      <step>
        <cmd>Add an <codeph>Authorization</codeph> header to your request with the value <codeph>Bearer {your-api-key}</codeph>.</cmd>
      </step>
      <step>
        <cmd>Send the request to the API endpoint.</cmd>
      </step>
    </steps>
    <result>The API validates your key and processes the request.</result>
  </taskbody>
</task>
```

### Concept Topic

**Input:** User provides system architecture docs and asks for a concept topic on multi-tenant data isolation.

**Output:**

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE concept PUBLIC "-//OASIS//DTD DITA 1.3 Concept//EN" "concept.dtd">
<concept id="multi-tenant-isolation">
  <title>Multi-Tenant Data Isolation</title>
  <conbody>
    <p>Each tenant's data is stored in a logically separated database schema. Queries are scoped to the authenticated tenant, preventing cross-tenant data access.</p>
  </conbody>
</concept>
```

## Common Edge Cases

- **Source inputs are incomplete** — Generate what is verifiable and flag gaps explicitly with comments in the XML.
- **Multiple topic types could apply** — When content could be a concept or a task, prefer task if the user needs to perform an action, concept if they need to understand the system.
- **Source contradicts existing documentation** — Trust the source (code/spec) over existing docs. Flag the contradiction for the domain expert.

## Reference

- [DITA 1.3 Specification](https://docs.oasis-open.org/dita/dita/v1.3/dita-v1.3-part0-overview.html)
- [DITA 1.3 Element Reference](https://docs.oasis-open.org/dita/dita/v1.3/errata02/os/complete/part3-all-inclusive/langRef/containers/concept-elements.html)

## Validation Requirement

Generated content must be tested against actual application behavior before publication. This is not editorial review — it is behavioral validation:

- For task topics: perform each documented step in the live application and confirm the documented sequence matches actual behavior
- For concept topics: verify descriptions against the running system, not just the source code
- For reference topics: confirm every field name, value, default, and option against the live UI

The person performing this validation must have direct knowledge of the end user's operational context — what the user is doing, under what conditions, and with what consequences for error.
