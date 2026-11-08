# Prompt Management

Front-matter schema and versioning strategy for Agent prompts.
## Front-Matter Schema
```yaml
---
version: 1.2.0
description: System prompt for code-reviewer agent
author: team-ai
created: 2026-06-01
updated: 2026-08-15
depends_on:
  - shared/coding-standards@1.1.0
  - shared/output-format@2.0.0
tags: [code-review, security, style]
cache_hint: stable_prefix
---
```
## Versioning Rules
- **major**: Breaking change (schema change, removed section)
- **minor**: Non-breaking addition (new rule, new example)
- **patch**: Fix (typo, clarification, formatting)
## Caching Optimization
1. Static prefix: Place stable instructions before dynamic content.
2. Cache hint: Set cache_hint in front-matter.
3. Version pin: Production loads pinned version, not latest.
## Loading Pattern
```python
prompt = PromptLoader.load('agents/code-reviewer/prompt.md', version='1.2.0')
system_prompt = prompt.static + dynamic_context
```