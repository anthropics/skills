# 0-editor

A robust, native file editing skill for agents that uses fuzzy AST/line matching instead of exact string replacement. Use this skill whenever you need to edit source code files to avoid whitespace and indentation matching errors.

## Why 0-editor?

Standard agentic `edit` tools often rely on exact string matching. This means any hallucinated space, tab, or newline by the LLM will cause the edit to fail. 
`0-editor` aligns edits semantically by allowing agents to pass chunks of code, intelligently ignoring indentation and whitespace drifts.

## Included files

- `SKILL.md`: The system prompt to attach to your agent or load into your context window when working with code bases.
