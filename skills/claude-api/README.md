# Claude API

Comprehensive reference for building LLM-powered applications with Claude — covers model IDs, pricing, streaming, tool use, agents, caching, authentication, and API drift.

## Quick Start

**Use this skill when:**
- You're building an application with Claude
- You need to choose a Claude model
- You want to implement a specific feature (caching, tools, streaming, etc.)
- You're troubleshooting API errors
- You need to migrate code to a newer model

## What's In This Skill

This is a **reference skill**, not a tutorial. It provides:

- **SDK reference**: Official usage patterns for Python, TypeScript, Java, Go, Ruby, C#, PHP
- **Feature guides**: Caching, tool use, streaming, agents, file handling, vision
- **Model information**: Current models, pricing, context windows, capabilities
- **Migration help**: Step-by-step guides for upgrading to new models
- **Provider platforms**: Bedrock, Azure, Google Cloud Vertex AI setup
- **Troubleshooting**: Common errors and solutions

## Finding What You Need

**The SKILL.md file is 546 lines**—don't read it all at once. Instead:

1. **Use the navigation guide**: `references/navigation-guide.md` has a task-based finder
2. **Skim section headings** in SKILL.md to find your topic
3. **Read language-specific docs** in `{lang}/` subdirectories for code examples
4. **Dive into shared references** for deep dives on specific topics

**Example: "I need to use tool calling"**
→ Navigation guide suggests: SKILL.md § Tool Use Patterns + `{lang}/tools.md`
→ Read those two sections; skip the rest

## Key Topics

### Getting Started
- **Before You Start** (SKILL.md): Check for non-Anthropic providers
- **Language Detection** (SKILL.md): Identify your project language
- **Authentication**: `{lang}/authentication.md` for your language
- **First API Call**: `{lang}/basic-message.md` for your language

### Building Features
- **Tool Use / Function Calling**: SKILL.md § Tool Use Patterns + `{lang}/tools.md`
- **Streaming**: SKILL.md § Streaming APIs + `{lang}/streaming.md`
- **File/Image Input**: SKILL.md § Document & File Input + `{lang}/files.md`
- **Vision (Images)**: SKILL.md + `{lang}/vision.md`
- **Caching**: SKILL.md § Prompt Caching + `{lang}/caching.md`
- **Extended Thinking**: SKILL.md § Thinking & Effort + `shared/thinking-budget.md`

### Building Agents
- **Agent Approaches**: SKILL.md § Which Surface Should I Use? → Building an Agent
- **Tool Runner**: `{lang}/agents.md` for code examples
- **Managed Agents** (beta): SKILL.md § Managed Agents + `shared/managed-agents-tools.md`

### Advanced Topics
- **Context Editing**: SKILL.md § Context Editing (Quick Reference)
- **Token Counting**: `{lang}/token-counting.md`
- **Mid-Conversation System Messages**: SKILL.md § Mid-Conversation System Messages
- **Server Tools** (web search, etc.): SKILL.md § Server Tools (Quick Reference)
- **Provider Platforms**: SKILL.md § Provider Clients

### Troubleshooting
- **API Drift** (breaking changes): SKILL.md § ⚠️ API Drift
- **Common Errors**: `shared/common-errors.md` + `{lang}/errors.md`
- **Model Migration**: Use `/claude-api migrate` subcommand

## Critical Information

### ⚠️ Important: API Drift (2025-2026)

Several common patterns changed recently. Check **SKILL.md § ⚠️ API Drift** immediately:

| What changed | Old way | New way |
|---|---|---|
| Extended thinking | `budget_tokens: N` | `type: "adaptive"` (newer models) |
| Web search tool | `web_search_20250305` | `web_search_20260209` |
| PHP parameters | snake_case | Mostly camelCase in recent versions |
| Managed Agents auth | Host-side credentials | Vault-based environment variables |

**The `{lang}/` files are authoritative**. If you recall a pattern from training, verify it there before using.

### Defaults (When Not Specified)

Unless the user requests otherwise:
- **Model**: Claude Opus 5 (`claude-opus-5`)
- **Thinking**: Adaptive thinking (`thinking: {type: "adaptive"}`)
- **Streaming**: Enabled for long contexts or high `max_tokens`

## Supported Languages

- **Python** (official `anthropic` SDK)
- **TypeScript/JavaScript** (official `@anthropic-ai/sdk`)
- **Java** (official `com.anthropic.*` SDK)
- **Go** (official `github.com/anthropics/anthropic-sdk-go`)
- **Ruby** (official `anthropic` gem)
- **C#** (official `Anthropic` NuGet package)
- **PHP** (official `anthropic-sdk-php`)
- **cURL / Raw HTTP** (no SDK required)

## Current Models (as of Aug 2026)

See **SKILL.md § Current Models** for authoritative specs. Quick reference:

| Model | Best For | Context | Capability Tier |
|---|---|---|---|
| Claude Opus 5 | Most complex reasoning, long tasks | 1M tokens | Highest capability |
| Claude Sonnet 5 | Balanced (speed/quality) | 1M tokens | High capability |
| Claude Fable 5 | Agentic, complex workflows | 1M tokens | High capability |
| Claude Haiku 4.5 | Speed, lightweight tasks | 200K tokens | Efficient |

**Pricing and details**: Check SKILL.md § Current Models or `shared/pricing.md` for up-to-date rates and feature costs.

## Output Requirement

When building with Claude, you **must** use:

1. **Official Anthropic SDK** for your language (default)
2. **Raw HTTP** only if you explicitly request it or have no SDK

Never mix (e.g., don't use `requests` in Python just to feel lighter).

Never fall back to OpenAI-compatible shims.

**Exception**: If the project already uses a non-Anthropic provider (OpenAI, Gemini, etc.), this skill will tell you to stop—it only produces Claude/Anthropic code. Ask if you want to switch.

## Common Tasks

### Task: Choose a Model
1. Read: SKILL.md § Current Models
2. Check: Input/output pricing and context window
3. Consider: Speed vs. quality trade-off
4. See: `shared/model-current.md` for latest info

### Task: Implement Tool Calling
1. Read: SKILL.md § Tool Use Patterns (Quick Reference)
2. Read: `{lang}/tools.md` for your language
3. See: `shared/tool-use-patterns.md` for advanced patterns

### Task: Reduce Costs
1. Read: `shared/pricing.md` to understand cost drivers
2. Consider: Caching (repeated context), compression, batching
3. See: `shared/optimization.md` for concrete strategies

### Task: Migrate Code to New Model
1. Run: `/claude-api migrate` subcommand (guided workflow)
2. Read: `shared/model-migration.md` for breaking changes
3. Check: Model-specific sections for deprecations

### Task: Build an Agent
1. Read: SKILL.md § Building an Agent: Four Approaches
2. Choose: Your approach (Tool Runner, Managed Agents, custom loop, single-turn)
3. Read: Corresponding section in `shared/agents.md` or `{lang}/agents.md`

### Task: Add File/Image Support
1. Read: SKILL.md § Document & File Input
2. Read: `{lang}/files.md` for language-specific examples
3. Check: `shared/file-handling.md` for size limits and costs

## Structure of This Skill

```
SKILL.md (546 lines)
├── Orientation & SDK selection
├── Language detection
├── Model & pricing information
├── Authentication
├── Feature quick references
│   ├── Thinking/Effort
│   ├── Caching
│   ├── Streaming
│   ├── Context Editing
│   └── ... (10+ more)
├── Tool Use Patterns
├── Agent approaches
├── Provider platforms
├── API Drift warnings
└── Links to references/

references/
├── navigation-guide.md (task-based finder)
├── model-migration.md (step-by-step migration)
├── model-current.md (latest model info)
├── pricing.md (detailed cost breakdown)
├── common-errors.md (troubleshooting)
├── thinking-budget.md (optimization)
├── caching-strategy.md (efficiency patterns)
└── ... (10+ more)

{lang}/ (one per supported language)
├── authentication.md (API key setup)
├── basic-message.md (first call)
├── tools.md (tool use / function calling)
├── streaming.md (streaming patterns)
├── caching.md (caching implementation)
├── files.md (file/image input)
├── agents.md (agent patterns)
├── errors.md (debugging)
└── api-reference.md (quick syntax)

curl/
├── basic-message.md (first request)
├── streaming.md (SSE streaming)
├── tools.md (tool calling)
└── errors.md (HTTP status codes)
```

## Reading Paths by Use Case

### "I've never used Claude API"
1. SKILL.md § Before You Start
2. SKILL.md § Language Detection
3. `{lang}/authentication.md`
4. `{lang}/basic-message.md`
5. Run example and iterate

### "I'm familiar with Claude, adding a feature"
1. Navigation guide (this file) → find your task
2. Read suggested section(s)
3. Check ⚠️ API Drift if relevant
4. Implement using language-specific code
5. Troubleshoot with `{lang}/errors.md`

### "I need to optimize performance/cost"
1. `shared/optimization.md`
2. `shared/pricing.md` (understand cost drivers)
3. Choose strategy (caching, compression, batching)
4. Implement using `{lang}/` examples
5. Benchmark and iterate

### "I'm migrating code to a new model"
1. Use `/claude-api migrate` subcommand
2. Read `shared/model-migration.md` for breaking changes
3. Check model-specific sections
4. Test thoroughly before deploying

## Subcommands

This skill supports specific subcommands for common tasks:

```
/claude-api migrate        → Guided model migration workflow
```

Running `/claude-api migrate` will:
1. Ask which files/directories to migrate
2. Classify each file by complexity
3. Show breaking changes for your target model
4. Guide you through necessary changes

## Tips

**Do:**
- ✅ Use official SDKs (always better than raw HTTP)
- ✅ Verify patterns in `{lang}/` files before using
- ✅ Check API Drift before writing code
- ✅ Test streaming for long contexts
- ✅ Use caching for repeated prompts
- ✅ Validate with language-specific error guides

**Don't:**
- ❌ Guess SDK APIs from training data
- ❌ Mix SDKs in the same project
- ❌ Assume your recalled pattern still works
- ❌ Skip authentication/setup steps
- ❌ Deploy without testing on target model

## Quick Links

- **Navigation Guide**: `references/navigation-guide.md` (find your topic)
- **Model Migration**: Use `/claude-api migrate` or `shared/model-migration.md`
- **Common Errors**: `shared/common-errors.md`
- **Pricing**: `shared/pricing.md`
- **Official Docs**: See `shared/live-sources.md` for Anthropic documentation links

## For Contributors & Developers

This skill is reference material for building production applications. Contributions should:

- Include updated examples for the latest models
- Test code examples (don't guess syntax)
- Include both happy path and error cases
- Clearly mark what's deprecated or changed
- Link to official Anthropic documentation

## Resources

- **Official API Docs**: https://docs.anthropic.com/
- **SDK Repositories**: See `shared/live-sources.md`
- **Anthropic Support**: https://support.anthropic.com/
- **Model Information**: https://www.anthropic.com/products

---

**Last Updated**: August 2026
**License**: Complete terms in LICENSE.txt
**Repository**: anthropics/skills

**Ready to build?** Start with the navigation guide or jump straight to SKILL.md § Language Detection.
