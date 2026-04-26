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

**Input:** User provides airline operations platform UI specs and asks for a task topic on submitting a delay report.

**Output:**

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE task PUBLIC "-//OASIS//DTD DITA 1.3 Task//EN" "task.dtd">
<task id="submit-delay-report">
  <title>Submit a Delay Report</title>
  <taskbody>
    <context>When a flight departs late, submit a delay report to record the cause and duration for compliance tracking.</context>
    <steps>
      <step>
        <cmd>From the flight list, select the delayed flight.</cmd>
      </step>
      <step>
        <cmd>Select <cmdname>Report Delay</cmdname>.</cmd>
      </step>
      <step>
        <cmd>Select the primary delay cause from the drop-down list.</cmd>
      </step>
      <step>
        <cmd>Enter the delay duration in minutes.</cmd>
      </step>
      <step>
        <cmd>Select <cmdname>Submit</cmdname>.</cmd>
      </step>
    </steps>
    <result>The delay is recorded against the flight and reflected in the daily compliance summary.</result>
  </taskbody>
</task>
```

### Concept Topic

**Input:** User provides crew management documentation and asks for a concept topic on flight duty period.

**Output:**

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE concept PUBLIC "-//OASIS//DTD DITA 1.3 Concept//EN" "concept.dtd">
<concept id="flight-duty-period">
  <title>Flight Duty Period</title>
  <conbody>
    <p>A flight duty period (FDP) is the time from when a crew member reports for duty until the last flight lands and the aircraft is parked. FDP limits vary by regulatory authority and depend on the number of flight segments, departure time, and crew complement.</p>
    <p>The platform calculates FDP automatically based on the assigned schedule and flags any segment that would exceed the applicable limit.</p>
  </conbody>
</concept>
```

### Reference Topic

**Input:** User provides alert configuration specs and asks for a reference topic on alert settings.

**Output:**

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE reference PUBLIC "-//OASIS//DTD DITA 1.3 Reference//EN" "reference.dtd">
<reference id="alert-settings">
  <title>Alert Configuration Settings</title>
  <refbody>
    <table>
      <tgroup cols="3">
        <thead>
          <row>
            <entry>Field</entry>
            <entry>Type</entry>
            <entry>Default</entry>
          </row>
        </thead>
        <tbody>
          <row>
            <entry>Alert Name</entry>
            <entry>Text (required)</entry>
            <entry>—</entry>
          </row>
          <row>
            <entry>Severity</entry>
            <entry>Drop-down: Low, Medium, High, Critical</entry>
            <entry>Medium</entry>
          </row>
          <row>
            <entry>Threshold (minutes)</entry>
            <entry>Integer</entry>
            <entry>15</entry>
          </row>
          <row>
            <entry>Notification Channel</entry>
            <entry>Drop-down: Email, SMS, Dashboard</entry>
            <entry>Dashboard</entry>
          </row>
        </tbody>
      </tgroup>
    </table>
  </refbody>
</reference>
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
