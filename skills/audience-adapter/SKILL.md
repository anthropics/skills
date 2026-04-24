---
name: audience-adapter

description: Reframe the same system behavior for distinct user groups with different operational contexts, knowledge bases, and task requirements. TRIGGER when: user needs to produce documentation for multiple distinct audiences from the same source; user needs audience-specific framing for a procedure or concept; AI has collapsed audience distinctions in generated content. SKIP: documentation has a single audience; content differences between audiences are minimal.

license: MIT
---

# Audience Adapter

Reframe system behavior documentation for specific user groups — AI collapses audience distinctions without explicit direction.

## Inputs Required

1. **Source content** — the base documentation or system description to adapt
2. **Target audience** — who this version is for
3. **Audience context** — their role, operational environment, knowledge base, and task goals
4. **Regulatory or compliance context** — any standards or requirements specific to this audience

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

## Output Format

Produce adapted content in the same format as the source — topic type and structure unchanged, framing and depth adjusted for the target audience.

## Reference

- [Microsoft Writing Style Guide — Audience](https://learn.microsoft.com/en-us/style-guide/audiences)
- [Plain Language Guidelines — Know Your Audience](https://www.plainlanguage.gov/guidelines/audience/)
- [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/) — audience-calibrated writing for technical and regulated industries

## What This Skill Does Not Do

Audience adaptation does not substitute for domain-expert review. Whether adapted content is operationally sufficient for a specific audience requires validation by someone with direct knowledge of that audience's operational context.
