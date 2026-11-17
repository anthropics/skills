---
name: audience-adapter

description: Reframe the same system behavior for distinct user groups with different operational contexts, knowledge bases, and task requirements. Use this skill when the user needs to produce documentation for multiple distinct audiences from the same source, needs audience-specific framing for a procedure or concept, or when AI output has collapsed audience distinctions into generic content.

license: Complete terms in LICENSE.txt
---

# Audience Adapter

Reframe system behavior documentation for specific user groups — AI collapses audience distinctions without explicit direction.

## When to Use This Skill

Use this skill when the user needs to produce documentation for multiple distinct audiences from the same source, needs audience-specific framing for a procedure or concept, or when AI output has collapsed audience distinctions into generic content.

Do not use this skill when documentation has a single audience, or when content differences between audiences are minimal.

## Inputs Required

1. **Source content** — the base documentation or system description to adapt
2. **Target audience** — who this version is for
3. **Audience context** — their role, operational environment, knowledge base, and task goals
4. **Regulatory or compliance context** — any standards or requirements specific to this audience

## Step-by-Step Workflow

1. **Identify audiences** — List each distinct user group. Confirm their roles, operational environments, and what they are trying to accomplish. If the user cannot identify distinct audiences, this skill is not needed.
2. **Analyze source content per audience** — For each audience, determine what the source content means to them. The same system function has different operational significance for different user groups.
3. **Calibrate knowledge assumptions** — For each audience, determine what they already know and what they do not. Do not explain concepts the audience already knows. Do not assume knowledge the audience does not have.
4. **Adapt framing and depth** — Rewrite the content for each audience:
   - Frame procedures around what that audience is trying to accomplish — not what the system does
   - Match procedural depth to workload context — shorter steps for time-pressured users, more context for infrequent complex tasks
   - Apply terminology appropriate for that audience's operational environment
5. **Apply regulatory context** — Where an audience operates under specific regulatory requirements, reference those requirements explicitly where relevant to the procedure.
6. **Verify audience distinction** — After adaptation, confirm that each version is framed for its specific audience and that audience-specific operational context is preserved.

## Adaptation Rules

### Knowledge Base
Calibrate assumed knowledge to the audience. Do not explain concepts the audience already knows. Do not assume knowledge the audience does not have.

### Task Framing
Frame procedures around what this audience is trying to accomplish — not what the system does. The same system function has different meanings for different users.

### Operational Context
Apply terminology and framing appropriate for this audience's operational environment. What is standard language for one user group may be unfamiliar to another.

### Regulatory Context
Where the audience operates under specific regulatory requirements, reference those requirements explicitly where relevant to the procedure.

### Depth and Detail
Match procedural depth to the audience's workload context. Users operating under time pressure need shorter steps and less background. Users performing infrequent complex tasks need more context.

## Examples

### Same Feature, Two Audiences

**Source:** Flight disruption alert — the platform detects a schedule conflict and generates an alert with cause, affected flights, and proposed recovery options.

**Adapted for Operations Controller:**

> ## Respond to a Schedule Disruption Alert
>
> When a disruption alert appears in your queue, evaluate the proposed recovery options and apply the best one.
>
> 1. Select the alert to view affected flights and proposed recovery options.
> 2. Compare aircraft swap and re-routing options by delay impact and downstream effect.
> 3. Select the recovery option and select **Apply**.
> 4. Verify that downstream flights are updated and no new conflicts are introduced.
>
> If no proposed option is viable, escalate to the operations manager and document the reason.

**Adapted for Crew Scheduler:**

> ## Review Crew Impact from a Disruption
>
> When a disruption alert affects crewed flights, check whether existing assignments are still legal under duty time limits.
>
> The alert lists all crew members affected by the schedule change. For each crew member, the platform flags whether their revised flight sequence exceeds flight duty period limits or violates rest requirements.
>
> If a crew member is flagged: reassign them before the schedule is published. See Modify a Crew Assignment for steps.

### Audience Collapse (What to Avoid)

**Collapsed output (generic):**
"When a disruption occurs, the system generates an alert. Users should review the alert and take appropriate action."

This serves neither audience. The controller needs to evaluate and apply recovery options. The scheduler needs to verify crew legality and reassign if necessary.

## Common Edge Cases

- **User provides one prompt for multiple audiences** — Do not produce a single combined version. Produce separate versions for each audience and label them clearly.
- **Audiences share some context** — Use shared framing for overlap, audience-specific framing for divergence. Do not merge distinct operational contexts into one section.
- **Regulatory context is unclear** — Ask the user which regulations apply to each audience before generating. Do not assume regulatory requirements.

## Output Format

Produce adapted content in the same format as the source — topic type and structure unchanged, framing and depth adjusted for the target audience.

## Validation Requirement

Adapted content must be reviewed by someone with direct knowledge of each audience's operational context. Audience-appropriate framing cannot be verified by style review alone — the validator must be able to answer: would this audience understand what to do, under the conditions they actually face, with the consequences that apply to them? If the validator cannot answer this for a specific audience, that audience's adapted content has not been validated.

## Reference

- [Plain Language Guidelines — GSA](https://github.com/gsa/plainlanguage.gov)
- [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/) — audience-calibrated writing for technical and regulated industries
