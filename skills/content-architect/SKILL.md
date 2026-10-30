---
name: content-architect

description: Design topic hierarchy, content relationships, and information architecture for product documentation. Use this skill when the user needs to structure documentation for a new product or feature, needs a topic map or content plan before writing begins, or needs to organize existing content into a coherent structure.

license: Complete terms in LICENSE.txt
---

# Content Architect

Design documentation structure before content generation begins.

## When to Use This Skill

Use this skill when the user needs to structure documentation for a new product or feature, needs a topic map or content plan before writing begins, or needs to organize existing content into a coherent structure.

Do not use this skill when the user already has a content structure and needs content generation, or when the user needs editorial review of an existing structure.

## Inputs Required

1. **Product scope** — what the product does and who uses it
2. **User goals** — what tasks users need to accomplish
3. **Audience** — user groups and their operational contexts
4. **Existing documentation** — current structure if reorganizing

## Step-by-Step Workflow

1. **Gather inputs** — Confirm product scope, user goals, audience groups, and existing documentation. If any are missing, ask the user before proceeding.
2. **Identify user goals** — List every distinct task users need to accomplish with the product. Group by audience if multiple user groups exist.
3. **Assign topic types** — For each user goal, assign a content type:
   - **Concept** — explaining what something is or how it works
   - **Task** — documenting a procedure the user performs
   - **Reference** — documenting UI elements, fields, options, or parameters
4. **Build the topic map** — Organize topics hierarchically by user goal, not by system architecture. Apply parallel structure for equivalent topics across user groups.
5. **Identify relationships** — Map parent-child relationships, cross-references, and reuse opportunities across user groups.
6. **Flag coverage gaps** — Identify topics required that do not yet exist in current documentation.

## Architecture Principles

- Organize by what the user is doing — not how the system is built
- One topic per user goal or concept — avoid combining unrelated information
- Parallel structure for equivalent topics across user groups
- Minimize prerequisite chains — users should reach any topic with minimal navigation

## Examples

### Topic Map Output

**Input:** User provides scope for an airline operations control platform serving operations controllers and crew schedulers.

**Output:**

```
Airline Operations Platform — Help Documentation Map

Operations Controller Topics
├── CONCEPT: Disruption Management Overview
│   └── How the platform detects schedule conflicts and proposes recovery options
│   └── PREREQUISITE: Flight Status Workflow (cross-audience)
├── TASK: Recover a Disrupted Schedule
│   └── Review alerts, evaluate re-routing and aircraft swap options, apply recovery
│   └── RELATED: Modify a Crew Assignment (scheduler) — disruption recovery may require crew changes
├── TASK: Monitor Operational Compliance
│   └── Track delay codes, crew duty limits, and maintenance windows across the fleet
│   └── SEE ALSO: Duty Time Fields (scheduler reference) — crew duty limits are defined there
└── REFERENCE: Alert Types and Severity
    └── Delay threshold alerts, crew timeout warnings, maintenance due flags — definitions and required actions

Crew Scheduler Topics
├── CONCEPT: Crew Assignment Logic
│   └── How the platform matches crew to flights based on qualifications, duty time, and rest requirements
│   └── PREREQUISITE: Flight Status Workflow (cross-audience)
├── TASK: Modify a Crew Assignment
│   └── Replace a crew member, verify qualification and legality, publish the update
│   └── RELATED: Recover a Disrupted Schedule (controller) — crew changes may trigger schedule alerts
├── TASK: Build a Monthly Crew Plan
│   └── Generate assignments from the schedule, resolve conflicts, and submit for approval
│   └── PREREQUISITE: Crew Assignment Logic
└── REFERENCE: Duty Time Fields
    └── Flight duty period, rest period, cumulative hours — definitions and regulatory limits
    └── REUSED BY: Monitor Operational Compliance (controller) — same field definitions

Cross-Audience
├── CONCEPT: Flight Status Workflow
│   └── Shared topic — covers how a flight moves from scheduled to dispatched
│   └── GAP: controllers need guidance on crew-impact assessment during disruption — scheduler version does not cover this
```

### Coverage Gap Identification

**Input:** User provides existing documentation that covers only installation and system configuration.

**Output:**

```
Coverage gaps identified:
- No task topics: existing docs cover setup but not daily user procedures
- No audience separation: single topic set for both controllers and schedulers
- Missing: schedule recovery and compliance monitoring procedures for operations controllers
- Missing: crew assignment modification and monthly planning procedures for crew schedulers
```

## Common Edge Cases

- **User provides system architecture instead of user goals** — Restructure around what users do, not how the system is built. Ask the user to confirm the restructured goals.
- **Multiple audiences with overlapping tasks** — Create shared topics for overlap, audience-specific topics for divergence. Flag where operational context requires separate framing despite shared content.
- **Existing documentation is unstructured** — Map existing content to the new topic types before identifying gaps. Do not discard existing content.

## Output Format

Produce a structured topic map as a hierarchical list with topic titles, types, and brief descriptions. Flag any gaps where source inputs are insufficient to define scope.

## Validation Requirement

The topic map must be reviewed by someone with direct knowledge of the end users' operational contexts before content generation begins. A structurally correct topic map can still miss critical user goals, conflate distinct operator workflows, or organize content around system architecture rather than user tasks. The person performing this review must be able to answer: does each topic map to something a user actually needs to do, under conditions they actually face?

## Reference

- [DITA 1.3 Topic Types — OASIS](https://docs.oasis-open.org/dita/dita/v1.3/dita-v1.3-part0-overview.html)
- [Every Page is Page One — Mark Baker](https://everypageispageone.com/) — topic-based authoring principles
- [Diátaxis Framework](https://diataxis.fr/) — systematic approach to technical documentation structure
