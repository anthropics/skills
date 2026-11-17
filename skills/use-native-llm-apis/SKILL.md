---
name: use-native-llm-apis
description: Use when implementing, integrating, migrating, or debugging provider-native LLM APIs in code, especially auth, request shapes, streaming, tool calling, structured output, or provider switching.
---

# Use Native LLM APIs

Use this skill for provider-native API implementation work, not pricing research, prompt writing, or generic AI product planning.

This skill covers a broad provider registry, but the provider files are not all equally deep. Some are gold references, some are usable notes, and some are partial. Historical or reserved depth labels such as `skeleton` may still appear in maintenance docs, but the live snapshot in [references/research/coverage-status.md](references/research/coverage-status.md) is the source of truth.

## Trigger Boundary

Trigger when both are true:

1. the request names a provider or clearly implies a provider-native API
2. the request asks for implementation work in code

Typical implementation work:

- integrate / connect / call
- migrate / switch
- debug 400 / 401 / 422
- add streaming
- add tool calling
- add structured JSON output
- 接入 / 对接 / 调用 / 迁移 / 切换 / 排查

Do not trigger for:

- pricing or model comparison
- prompt engineering
- chatbot or RAG planning without concrete provider API work

## Start Protocol

Always use this order:

1. open [references/start-here.md](references/start-here.md)
2. choose exactly one task recipe
3. resolve the provider path through [references/providers/index.md](references/providers/index.md)
4. open the exact provider file
5. open one comparison file only if the task requires it
6. check [references/routing-checklist.md](references/routing-checklist.md)
7. then write or patch code

Do not jump directly from `SKILL.md` to a guessed provider file.

## Missing-Info Rule

Ask at most one clarification question before routing:

- provider missing -> ask which provider API they want
- provider present but task ambiguous -> ask one task question
- provider and task both missing -> do not trigger yet

Examples:

- "给项目加 AI 对话" -> do not trigger yet
- "Hook up Claude" -> ask what task they need
- "Convert OpenAI to Gemini" -> route immediately as migration

## Guardrails

- Keep the work provider-native unless the user explicitly wants an abstraction layer.
- Resolve provider paths through `references/providers/index.md`, not from memory.
- Treat partial provider files as starting notes, not authoritative end-to-end references.
- Treat `skeleton` as a reserved or historical depth label unless the live coverage snapshot says otherwise.
- Prefer raw HTTP examples over abstraction-heavy wrappers.
- Prefer official docs over memory when bundled references are insufficient.
- Do not assume OpenAI-compatible means fully behavior-compatible.

For trigger examples and few-shot routing, see [references/recipes/prompt-patterns.md](references/recipes/prompt-patterns.md).
