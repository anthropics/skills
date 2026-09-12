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

Ask these questions. User can skip any by saying "skip" or "next".

**1. Compliance** (skip if not applicable):
> Does your work involve healthcare data (HIPAA), financial data (PCI-DSS), government contracts (FedRAMP), or EU personal data (GDPR)? (say "skip" if none)

**2. Security** (skip if not applicable):
> Any security-critical code (auth, payments, encryption) that should stay human-written? (skip if none)

**3. Tech Stack**:
> What's your tech stack? (e.g., 'Node.js, Express, PostgreSQL, Jest')

**4. Commands** (skip if unknown):
> Test command? Dev server command? (skip if not set up yet)

**5. Architecture & Design** (optional - skip or provide docs):
> Do you have existing docs I should read? Options:
> - Point to files (docs/architecture.md, README.md)
> - Paste content here
> - Answer a few questions
> - Skip entirely

If they want questions (all skippable individually):

> **Architecture**: How is your app structured? (monolith/microservices/serverless) [skip]
> **Code org**: Directory structure convention? Where do routes, services, models live? [skip]
> **Patterns**: Any specific patterns? (MVC, Repository, error handling conventions) [skip]
> **Data layer**: ORM, raw queries, caching? [skip]
> **Integrations**: External services/APIs to know about? [skip]

Only include answered questions in CLAUDE.md. Skip means skip - don't ask follow-ups.

## Phase 2: Create CLAUDE.md

Create CLAUDE.md with only the sections user provided (skip empty sections):

```markdown
# Project Context

Tech stack: [from Q3, required]

## Commands
Test: [from Q4, if provided]
Dev: [from Q4, if provided]

## Architecture
[from Q5, if provided - summarize key points]

## Code Organization
[from Q5, if provided - directory conventions]

## Patterns & Conventions
[from Q5, if provided - error handling, validation, etc.]

## Code Classification
[if compliance/security YES]
DO NOT use AI for code in:
- [user-specified directories]
```

Only include sections the user actually provided. A minimal CLAUDE.md with just tech stack is fine.

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
