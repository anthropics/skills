---
name: agentic-shift
description: Interactive onboarding for AI-assisted development. Use when users want to set up a project for AI-assisted coding, create CLAUDE.md files, or learn the spec-driven workflow. Adapts to user context including regulated industries (HIPAA, PCI-DSS, SOX, GDPR), security requirements, and tech stack. Guides users through their first AI-generated feature in about 5 minutes.
---

# The Agentic Shift

Interactive setup assistant for AI-assisted development. Adapts to user context through questions.

## Core Workflow

```
User writes spec → Claude asks questions → Claude generates code → User approves
```

## When Invoked

Start with:

> Let's set up AI-assisted development for your project.
>
> First, are you in a project directory with code you want to work on?

## Phase 1: Context Gathering

Ask these questions to adapt the setup:

**1. Compliance** (if yes, add code classification to CLAUDE.md):
> Does your work involve healthcare data (HIPAA), financial data (PCI-DSS), government contracts (FedRAMP), or EU personal data (GDPR)?

**2. Security** (if yes, recommend human-written for critical paths):
> Does this project contain security-critical code like authentication, payments, or encryption?

**3. Tech Stack** (store for CLAUDE.md):
> What's your tech stack? (e.g., 'Node.js, Express, PostgreSQL, Jest')

**4. Commands** (store for CLAUDE.md):
> What command runs your tests? What starts your dev server?

## Phase 2: Create CLAUDE.md

Create minimal CLAUDE.md in project root:

```markdown
# Project Context

Tech stack: [from Q3]

## Commands
Test: [from Q4]
Dev: [from Q4]
```

If compliance YES, add:

```markdown
## Code Classification

DO NOT use AI for code in:
- [ask user for security-critical directories]

These require human implementation.
```

## Phase 3: First Feature

1. Ask: "What's a small feature you need? Describe it in 2-3 sentences."

2. If stuck, offer stack-appropriate examples:
   - Node/Express: "Health check endpoint returning { status: 'ok' }"
   - Python/Flask: "/ping route returning 'pong'"
   - React: "Loading spinner component"

3. Demonstrate the workflow:
   - Ask 2-3 clarifying questions about their codebase
   - Generate implementation
   - Run tests if available
   - Present diff for approval

4. Confirm: "That's the workflow. Describe what you want, I generate, you approve."

## Phase 4: Offer Add-ons (Contextual)

Only offer relevant add-ons:

- **GitHub** (if mentioned): "Want GitHub integration for issues and PRs?"
- **Figma** (if frontend): "Want Figma connection for design references?"
- **Database** (if mentioned SQL): "Want database connection for schema context?"
- **Security hooks** (if compliance): "Want pre-commit hooks for secrets detection?"

## Contextual Warnings

Surface only when relevant:

- **Security code**: "Auth/encryption/payments are better human-written. Proceed anyway?"
- **Iterations**: "Each iteration costs tokens. Be specific to reduce iterations."
- **Test failures**: "After 3 failures on same issue, manual debugging is faster."
- **No tests**: "Without tests, changes can't be verified. Add tests first or verify manually."

## Style

- **Fast**: Minimize time to first feature
- **Adaptive**: Ask, don't assume
- **Minimal**: Only offer what's contextually relevant
- **Practical**: Use their real project
