# Publishing extensions

You've built a tool that calls your company's internal API. Or a model provider for a regional LLM service. Or a session manager that persists to Redis. It works great for your project—now you want to share it with others.

This guide walks you through packaging and publishing your Strands components so other developers can install them with `pip install`.

## Why publish

When you build a useful component, you have two choices: keep it in your project, or publish it as a package.

Publishing makes sense when your component solves a problem others face too. A Slack integration, a database session manager, a provider for a popular LLM service—these help the broader community. Publishing also means you own the package. You control when to release updates, what features to add, and how to prioritize bugs.

Your package can get listed in our [community catalog](../../community/community-packages.md), making it discoverable to developers looking for exactly what you built.

## What you can publish

Strands has several extension points. Each serves a different purpose in the agent lifecycle.

| Component | Purpose | Learn more |
|-----------|---------|------------|
| **Tools** | Add capabilities to agents—call APIs, access databases, interact with services | [Custom tools](../../user-guide/concepts/tools/custom-tools.md) |
| **Model providers** | Integrate LLM APIs beyond the built-in providers | [Custom model providers](../../user-guide/concepts/model-providers/custom_model_provider.md) |
| **Hook providers** | Extend or modify agent behavior during lifecycle events such as invocations, tool calls, and model calls | [Hooks](../../user-guide/concepts/agents/hooks.md) |
| **Session managers** | Persist conversations to external storage for resumption or sharing | [Session management](../../user-guide/concepts/agents/session-management.md) |
| **Conversation managers** | Control how message history grows—trim old messages or summarize context | [Conversation management](../../user-guide/concepts/agents/conversation-management.md) |

Tools are the most common extension type. They let agents interact with specific services like Slack, databases, or internal APIs.


## Get discovered

Once you publish, the next step is getting other developers to discover and use your package. See the [Get Featured guide](../../community/get-featured.md) for how to add GitHub topics and get listed in our community catalog.
