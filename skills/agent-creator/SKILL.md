---
name: agent-creator
description: Compose focused, task-specific agents with curated skill sets. Use when you need to define specialized agent roles (e.g., "Deep Research Agent", "Frontend Specialist", "Data Analyst") and equip them with a whitelisted subset of available skills. Helps in creating modular, auditable, and efficient agent manifestations.
---

# Agent Creator

A skill for composing specialized agents by combining a specific role identity with a curated set of skills.

## Overview

The `agent-creator` skill follows a **whitelist approach** to agent design. Instead of a single generalist agent with access to all capabilities, you use this skill to create agents that are "fit for purpose." This improves safety, reduces context noise, and increases the reliability of the resulting agent.

### Key Concepts

- **Role Definition**: The persona, identity, and specific purpose of the agent.
- **Skill Selection**: A whitelist of existing skills that this specialized agent is authorized to use.
- **Agent Manifest**: A structured definition (often a `.md` file) that combines the role and skills into a deployable agent configuration.

---

## Workflow

### 1. Define the Agent's Role

Start by interviewing the user to understand the specialized task the agent needs to perform.
- What is the agent's primary goal?
- What are the success criteria for its tasks?
- What is the "voice" or "persona" of the agent?
- What are the boundaries? (What should it NOT do?)

### 2. Select Skills (Whitelist)

Browse the available skill library and select only the skills necessary for the defined role.
- **Avoid Over-provisioning**: Only include skills that are directly relevant to the agent's tasks.
- **Check Dependencies**: Ensure any scripts or resources required by the selected skills are available.

### 3. Draft the Agent Manifest

Create a new manifest file (e.g., `agents/my-specialized-agent.md`). The manifest should follow this structure:

```markdown
# [Agent Name]

## Identity & Purpose
[A clear description of the agent's role and goal]

## Authorized Skills
This agent is equipped with the following skills:
- **[Skill Name 1]**: [Brief description of when/why the agent uses this skill]
- **[Skill Name 2]**: [Brief description of when/why the agent uses this skill]

## Operating Guidelines
- [Specific instruction 1]
- [Specific instruction 2]
```

### 4. Verification

Validate the specialized agent by running a few test prompts that are typical for its role. Ensure it stays within its defined boundaries and uses the authorized skills effectively.

---

## Guidelines

- **Prefer Composition**: When a task becomes too complex for one specialized agent, consider creating a "Coordinator Agent" that orchestrates multiple specialized agents rather than adding more skills to a single agent.
- **Auditability**: The whitelist should be explicit. It must be clear at a glance what an agent can and cannot do.
- **Efficiency**: Specialized agents are more efficient because they operate with less "distraction" from irrelevant tools and instructions.

## Examples

### Example 1: Creating a "Deep Research Agent"
**Input**: "I need an agent that can do deep research on technical topics and produce structured reports."
**Skills selected**: `claude-api`, `web-artifacts-builder`, `pdf`
**Manifest Draft**:
```markdown
# Deep Research Agent
## Identity & Purpose
Expert technical researcher focused on synthesizing information from web sources and APIs into comprehensive reports.
## Authorized Skills
- **claude-api**: For advanced reasoning and data synthesis.
- **web-artifacts-builder**: To create interactive visualizations of research findings.
- **pdf**: To extract data from research papers and whitepapers.
```

### Example 2: Creating a "Frontend Specialist"
**Input**: "Build a frontend expert that knows our brand guidelines."
**Skills selected**: `frontend-design`, `brand-guidelines`, `web-artifacts-builder`
**Manifest Draft**:
```markdown
# Frontend Specialist
## Identity & Purpose
Specialized UI/UX engineer that builds modern web interfaces strictly adhering to corporate brand guidelines.
## Authorized Skills
- **frontend-design**: For core UI implementation.
- **brand-guidelines**: To ensure visual consistency.
- **web-artifacts-builder**: To prototype components.
```
