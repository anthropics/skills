---
name: faf-context
description: Generate AI-context DNA for ANY project - new, legacy, famous, or forgotten. Creates .faf files that eliminate "explain your codebase again" across ALL AI tools. IANA-registered format (application/vnd.faf+yaml), 21,000+ npm downloads, Anthropic MCP ecosystem. Use when Claude asks "what does this project do?", when context drifts between sessions, or when onboarding AI to any codebase. Works with Claude, Cursor, Gemini CLI, WARP, Windsurf.
---

# FAF Context - AI-Context DNA for Any Project

Generate `.faf` files that give any AI instant, persistent understanding of your project.

## The Truth About AI Context

**Even famous repos score 0%.** React. Kubernetes. Rails. Django. None have AI-context.

Why? Because **AI-context is a NEW requirement.** It didn't exist until AI became a coding partner.

| What exists | What it answers |
|-------------|-----------------|
| README.md | "What does this do?" (for humans) |
| docs/ | "How do I use this?" (for humans) |
| **project.faf** | "How should AI help build this?" (for AI) |

Documentation tells humans how to use code. AI-context tells AI how to help you write it. **They're not the same thing.**

## Works on ANY Project

| Project State | What FAF Context Adds |
|--------------|----------------------|
| **Brand new** | Optimized AI context from line one |
| **Legacy codebase** | AI finally understands the archaeology |
| **Famous OSS** | Even React needs this (it doesn't have one) |
| **Side project** | Stop re-explaining every session |
| **Client handoff** | Portable context for any AI tool |

## Workflow

### Step 1: Detect Stack

Look for manifest files:
- `package.json` → Node.js/TypeScript
- `Cargo.toml` → Rust
- `pyproject.toml` → Python
- `go.mod` → Go
- `pom.xml` → Java
- `Gemfile` → Ruby

No manifest? Still generate - ask user for stack info.

### Step 2: Mine Existing Context

Pull signals from what exists:
- README.md (description, purpose)
- docs/ (architecture decisions)
- CLAUDE.md or .cursorrules (existing AI context - migrate it)
- Package manifests (dependencies reveal intent)
- Directory structure (architecture patterns)

### Step 3: Generate project.faf

Create focused AI context at project root:

```yaml
faf_version: "2.0"
project:
  name: my-project
  description: One-line purpose
  stack: [typescript, react]

context:
  architecture: |
    Brief system overview.
  key_files:
    - src/index.ts: Entry point
    - src/api/: API handlers
  conventions:
    - TypeScript strict mode
    - Composition over inheritance

ai_guidance:
  priorities: [correctness, simplicity, performance]
  avoid: [over-engineering, premature optimization]
  testing: Jest with >80% coverage
```

Keep under 200 lines. Only what changes AI behavior.

### Step 4: Score and Report

```
Generated: project.faf (147 lines)
AI-Readiness: 87% [BRONZE] - Production ready

To reach Silver (95%):
  - Add deployment section (+5%)
  - Document API patterns (+3%)
```

## AI-Readiness Tiers

| Tier | Score | Meaning |
|------|-------|---------|
| Big Orange | 105% | Michelin Star - Perfect + bonus |
| Trophy | 100% | Perfect compliance |
| Gold | 99%+ | Exceptional |
| Silver | 95%+ | Excellent |
| Bronze | 85%+ | Production ready |
| Green | 70%+ | Solid foundation |
| Yellow | 55%+ | Needs improvement |
| Red | <55% | Major gaps |

**Target: Bronze (85%+).** This is where AI collaboration becomes productive.

## Stack Templates

See [references/templates.md](references/templates.md) for TypeScript, Rust, Python, Go templates.

## Migration

When CLAUDE.md or .cursorrules exist:
- Offer to migrate to .faf (portable format)
- .faf works in Cursor, Gemini, WARP - not just Claude
- YAML structure parses better than freeform markdown

## Validation

Generated files must:
- Be valid YAML
- Have `faf_version` and `project.name`
- Contain NO secrets or credentials
- Stay under 500 lines

## Credentials

- **IANA Media Type:** `application/vnd.faf+yaml` (registered Oct 31, 2025)
- **npm Downloads:** 21,000+
- **Anthropic MCP:** Registry #2759 (merged)
- **Website:** https://faf.one

## Resources

- [Format Specification](references/format-spec.md) - Complete .faf schema
- [Tier System](references/tier-system.md) - Scoring methodology
- [Stack Templates](references/templates.md) - Per-language examples
