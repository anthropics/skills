# Claude API Skill - Navigation Guide

The Claude API skill is comprehensive (546 lines) and covers many topics. This guide helps you find what you need quickly.

## Quick Find by Task

### "I'm just starting to build with Claude"
→ Read: **SKILL.md § Before You Start** (sets up SDK usage fundamentals)
→ Then: **SKILL.md § Which Surface Should I Use?** (pick building approach)
→ Then: Language-specific docs in `{lang}/` subdirectories

### "I want to switch models or migrate code"
→ Read: **SKILL.md § Subcommands → `migrate`** section
→ Use: Run `/claude-api migrate` for guided workflow
→ Reference: `shared/model-migration.md` for breaking changes by model

### "I need to choose a Claude model"
→ Read: **SKILL.md § Current Models (cached: 2026-06-24)**
→ Reference: Model comparison table with capabilities, pricing, context windows
→ For latest: `shared/model-current.md` (may be more up-to-date than cached table)

### "How do I authenticate with Claude?"
→ Read: **SKILL.md § Authentication (Quick Reference)**
→ Then: Language-specific examples in `{lang}/authentication.md`
→ For advanced: `shared/auth-patterns.md` for API keys, OAuth, managed auth

### "I need to understand pricing"
→ Read: **SKILL.md § Current Models** (input/output pricing per model)
→ Reference: `shared/pricing.md` for detailed breakdown by feature (caching, tools, thinking, etc.)

### "How do I use tool calling (function calling)?"
→ Read: **SKILL.md § Tool Use Patterns (Quick Reference)**
→ Then: `{lang}/tools.md` for language-specific examples
→ For advanced patterns: `shared/tool-use-patterns.md`

### "I want to use extended thinking or reasoning"
→ Read: **SKILL.md § Thinking & Effort (Quick Reference)**
→ Reference: Check **⚠️ API Drift** table (thinking syntax changed in 2025-2026)
→ Deep dive: `shared/thinking-budget.md` for budget optimization

### "How do I improve response quality with caching?"
→ Read: **SKILL.md § Prompt Caching (Quick Reference)**
→ Then: `{lang}/caching.md` for language-specific examples
→ Advanced: `shared/caching-strategy.md` for cache optimization

### "I need to understand streaming responses"
→ Read: **SKILL.md § Which Surface Should I Use? → Streaming APIs**
→ Then: `{lang}/streaming.md` for language-specific patterns
→ Reference: `shared/streaming-patterns.md` for handling different event types

### "I want to build an agent"
→ Read: **SKILL.md § Which Surface Should I Use? → Building an Agent: Four Approaches**
→ Choose your approach (Tool Runner, Managed Agents, custom loop, single-turn)
→ Then: Read the corresponding section in `shared/agents.md`
→ Implementation: Language-specific examples in `{lang}/agents.md`

### "How do I use Managed Agents (beta)?"
→ Read: **SKILL.md § Managed Agents (Beta)** (overview and when to use)
→ Then: `shared/managed-agents-tools.md` for credentials and tool setup
→ Reference: `{lang}/managed-agents.md` for language-specific code

### "I need file/document handling"
→ Read: **SKILL.md § Document & File Input (Quick Reference)**
→ Then: Language-specific examples in `{lang}/files.md`
→ Deep dive: `shared/file-handling.md` for supported formats, size limits, costs

### "I need to set up vision (image understanding)"
→ Read: **SKILL.md § Document & File Input → Images & Vision**
→ Then: `{lang}/vision.md` for language-specific examples
→ Reference: `shared/vision-capabilities.md` for supported formats and quality tips

### "I'm getting errors or unexpected behavior"
→ Read: **SKILL.md § ⚠️ API Drift** (common breaking changes)
→ Check: `shared/common-errors.md` (error codes and how to fix them)
→ Reference: `{lang}/errors.md` for language-specific debugging

### "I want to use fast mode"
→ Read: **SKILL.md § Fast Mode (Quick Reference)**
→ Reference: `shared/fast-mode.md` for when it's available and any limitations

### "I need to use server tools (web search, web fetch, etc.)"
→ Read: **SKILL.md § Server Tools (Quick Reference)**
→ Reference: `shared/server-tools.md` for full tool reference and capabilities
→ Check: Which platform supports which tools (Bedrock, Vertex, etc.)

### "I want to use MCP (Model Context Protocol)"
→ Read: **SKILL.md § Which Surface Should I Use? → MCP**
→ Then: Repository has a dedicated `mcp-builder/` skill for deep guidance
→ Reference: `shared/mcp-integration.md` for server setup and best practices

### "I need to reduce latency or token usage"
→ Read: **SKILL.md § Compaction (Quick Reference)**
→ Then: `shared/optimization.md` for various optimization strategies
→ Consider: caching (large repeated context), compression (token reduction), batching

### "How do I handle mid-conversation system messages?"
→ Read: **SKILL.md § Mid-Conversation System Messages (Quick Reference)**
→ Reference: `shared/system-messages.md` for use cases and examples

### "I'm using a provider platform (Bedrock, Vertex AI, etc.)"
→ Read: **SKILL.md § Provider Clients (Quick Reference)**
→ Then: Platform-specific section (Amazon Bedrock, Microsoft Foundry, Google Cloud Vertex AI)
→ Reference: `shared/provider-platforms.md` for detailed setup and differences

### "I need context editing or token counting"
→ Read: **SKILL.md § Context Editing (Quick Reference)** or § Task Budgets (Quick Reference)**
→ Then: `{lang}/context-editing.md` or `{lang}/token-counting.md`
→ Advanced: `shared/context-editing-patterns.md` for complex workflows

---

## Structure of This Skill

```
SKILL.md (546 lines)
├── Before You Start
│   ├── Provider detection (OpenAI vs Claude)
│   ├── SDK vs. raw HTTP choice
│   └── Never-guess-SDK policy
├── Output Requirement (required SDKs and patterns)
├── Defaults (Claude Opus 5, adaptive thinking, streaming)
├── ⚠️ API Drift (important breaking changes 2025-2026)
├── Subcommands (`/claude-api migrate`)
├── Language Detection (which SDK to use)
├── Which Surface Should I Use? (choosing approach)
├── Architecture (models, pricing, features)
├── Current Models (Fable, Opus, Sonnet, Haiku with pricing)
├── Authentication (quick reference)
├── Thinking & Effort (quick reference)
├── Compaction (quick reference)
├── Prompt Caching (quick reference)
├── Fast Mode (quick reference)
├── Task Budgets (quick reference)
├── Provider Clients (Bedrock, Foundry, Vertex)
├── Context Editing (quick reference)
├── Mid-Conversation System Messages (quick reference)
├── Managed Agents (beta overview)
├── Server Tools (quick reference)
├── Document & File Input (quick reference)
├── Tool Use Patterns (quick reference)
└── Other API Surfaces (REST/cURL, web APIs)

references/
├── navigation-guide.md (this file)
├── model-migration.md (step-by-step migration workflow)
├── model-current.md (latest model info, updated more frequently)
├── pricing.md (detailed pricing by feature)
├── auth-patterns.md (authentication patterns across providers)
├── thinking-budget.md (optimizing thinking/reasoning)
├── caching-strategy.md (cache efficiency patterns)
├── streaming-patterns.md (streaming event handling)
├── agents.md (agent patterns and architectures)
├── managed-agents-tools.md (Managed Agents setup and credentials)
├── file-handling.md (documents, images, formats)
├── vision-capabilities.md (image understanding in detail)
├── common-errors.md (error codes and solutions)
├── fast-mode.md (fast mode details)
├── server-tools.md (web search, web fetch, etc.)
├── mcp-integration.md (MCP setup and best practices)
├── optimization.md (latency and token optimization)
├── system-messages.md (mid-conversation context)
├── provider-platforms.md (Bedrock/Foundry/Vertex differences)
├── context-editing-patterns.md (advanced context editing)
└── token-counting.md (token counting patterns)

{lang}/ (one directory per supported language: python, typescript, java, go, ruby, csharp, php)
├── authentication.md (SDK auth setup)
├── basic-message.md (first API call)
├── tools.md (tool use / function calling)
├── streaming.md (streaming patterns)
├── caching.md (implementing caching)
├── files.md (file/image input)
├── vision.md (image understanding)
├── agents.md (building agents)
├── managed-agents.md (Managed Agents setup)
├── token-counting.md (token counting)
├── context-editing.md (context editing)
├── errors.md (debugging in this language)
└── api-reference.md (quick syntax reference)

curl/ (raw HTTP examples)
├── basic-message.md (first request)
├── streaming.md (SSE streaming)
├── tools.md (tool calling)
├── files.md (multipart file upload)
└── errors.md (HTTP status codes)

shared/
├── live-sources.md (links to official docs and repos)
├── model-migration.md (breaking changes by target model)
└── ... (other shared references)
```

---

## How to Use Each Reference Section

### Quick Reference Sections (in SKILL.md)
**Format:** Concise table or bullet list  
**Use:** Get the essentials quickly (5-10 minutes)  
**Limitation:** May not cover all edge cases

### Language-Specific Docs (`{lang}/`)
**Format:** Code examples in a specific language  
**Use:** Implement features in your project's language  
**Scope:** Covers basic usage and common patterns

### Shared References (`shared/`)
**Format:** Detailed guides and patterns  
**Use:** Deep dives into specific topics  
**Scope:** Advanced patterns, trade-offs, optimization

### Navigation Guide (this file)
**Format:** Task-based finder  
**Use:** Find the right section for your specific need

---

## Most-Used Topics (by frequency)

Based on common usage patterns, these are the most-accessed sections:

1. **Model selection** — SKILL.md § Current Models
2. **Authentication** — SKILL.md § Authentication + `{lang}/authentication.md`
3. **Tool use / function calling** — SKILL.md § Tool Use Patterns + `{lang}/tools.md`
4. **Building an agent** — SKILL.md § Which Surface Should I Use → Building an Agent
5. **Streaming** — SKILL.md § Which Surface Should I Use → Streaming APIs + `{lang}/streaming.md`
6. **Error troubleshooting** — `shared/common-errors.md` + `{lang}/errors.md`
7. **Caching for cost reduction** — SKILL.md § Prompt Caching + `shared/caching-strategy.md`
8. **API drift / breaking changes** — SKILL.md § ⚠️ API Drift
9. **File/image input** — SKILL.md § Document & File Input + `{lang}/files.md`
10. **Model migration** — Use `/claude-api migrate` subcommand

---

## Common Starting Points by Skill Level

### Beginner: "I've never used the Claude API"
1. Read: **SKILL.md § Before You Start** (orientation)
2. Detect: Your project language
3. Read: `{lang}/authentication.md` (getting API key)
4. Read: `{lang}/basic-message.md` (first call)
5. Run: Copy example and test locally
6. Next: Expand to specific features (tools, files, caching)

### Intermediate: "I've used Claude before, adding a new feature"
1. Find: Your task in **Navigation Guide** (this document)
2. Read: The recommended section for that task
3. Check: **⚠️ API Drift** if it might have changed
4. Implement: Using language-specific examples
5. Debug: Using `{lang}/errors.md` if issues arise

### Advanced: "I need to optimize or use advanced features"
1. Read: **SKILL.md** for overview of all features
2. Deep-dive: Relevant `shared/` reference
3. Implement: Language-specific code
4. Benchmark: Using optimization patterns
5. Iterate: Based on performance metrics

---

## FAQ

**Q: The SKILL.md is long. Do I need to read all of it?**  
A: No. Use this navigation guide to find your specific task. Skim the relevant section; skip the rest.

**Q: I found conflicting info in two places. Which do I trust?**  
A: Priority: `{lang}/ specific files > shared/ detailed guides > SKILL.md quick references`.  
The more specific the section, the more up-to-date it usually is.

**Q: Can I use OpenAI/Gemini examples with Claude API?**  
A: Not directly. The APIs differ. If you need non-Claude providers, Claude API skill will tell you to stop—it only produces Claude/Anthropic SDK code.

**Q: How often is this skill updated?**  
A: SKILL.md is the source of truth; it's updated as APIs change.  
Individual reference files may be updated more frequently.  
Check `shared/live-sources.md` for links to official documentation (always authoritative).

**Q: I'm getting an error not covered here.**  
A: Check `shared/common-errors.md` first.  
Then check `{lang}/errors.md` for language-specific interpretation.  
Last resort: Check the official SDK repository (link in `shared/live-sources.md`).

**Q: How do I choose between different approaches?**  
A: Read **SKILL.md § Which Surface Should I Use?**.  
Each approach has trade-offs; the section explains when to pick each.

---

## Getting Help

1. **Stuck?** Use this navigation guide to find the most relevant section.
2. **Didn't find it?** Check `shared/live-sources.md` for links to official Anthropic documentation.
3. **Found an error?** Report it to Anthropic support.
4. **Want clarification on a specific pattern?** Ask Claude directly—it has access to this entire skill.
