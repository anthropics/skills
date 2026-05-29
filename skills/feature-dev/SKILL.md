---
name: feature-dev
description: Guided feature development with codebase understanding and architecture focus. Use when a user wants to implement a new feature, build functionality, or develop a capability in their codebase. Triggers on requests like "build a feature", "implement X", "add functionality for Y", or when the user invokes /feature-dev. This workflow helps developers understand the codebase deeply, ask clarifying questions, design architecture, implement with quality review, and document results.
---

# Feature Development

This skill provides a structured workflow for implementing features. It uses sub-agents for codebase exploration, architecture design, and code review.

## Agents

This skill includes three specialized agents in the `agents/` directory:

- **code-explorer**: Traces execution paths, maps architecture, and identifies key files
- **code-architect**: Designs feature architectures with implementation blueprints
- **code-reviewer**: Reviews code for bugs, quality issues, and convention adherence

## Workflow Command

The main workflow is defined in `commands/feature-dev.md`. It guides the user through 7 phases:

1. Discovery
2. Codebase Exploration
3. Clarifying Questions
4. Architecture Design
5. Implementation
6. Quality Review
7. Summary
