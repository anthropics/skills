# refactor-code

[![Validate](https://github.com/Herdly-AI/refactor-code-skill/actions/workflows/validate.yml/badge.svg)](https://github.com/Herdly-AI/refactor-code-skill/actions/workflows/validate.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](./LICENSE)
[![Agent Skills](https://img.shields.io/badge/Agent_Skills-compatible-blueviolet)](https://agentskills.io/)
[![Claude Code](https://img.shields.io/badge/Claude_Code-plugin-orange)](https://code.claude.com/docs/en/plugin-marketplaces)
[![Version](https://img.shields.io/badge/version-1.0.0-blue)](./CHANGELOG.md)

A portable [Agent Skill](https://agentskills.io/) for principled, pattern-driven code refactoring based on Martin Fowler's catalog and the Gang of Four design patterns, cross-referenced at [refactoring.guru](https://refactoring.guru/).

Refactors code across TypeScript, JavaScript, Python, React/JSX, Go, C, C++, Java, C#, Ruby, PHP, Rust, and other languages, applying code smells → refactoring techniques → design patterns in that order, then cross-checking against language-specific linter rules (ESLint, ruff, clang-tidy, golangci-lint, etc.).

The Agent Skills format became an open standard in December 2025 and has been adopted by every major agentic coding platform. This skill is **not locked to Claude** — it runs unchanged on ChatGPT, Codex CLI, Gemini CLI, Cursor, and a dozen other agents. See the [compatibility matrix](#compatibility) below.

This repo is also a valid [Claude Code plugin marketplace](https://code.claude.com/docs/en/plugin-marketplaces), which means Claude Code users can install it with a single command.

## What it does

- **Diagnoses** the 22 Fowler code smells (Long Method, Primitive Obsession, Switch Statements, Feature Envy, Data Clumps, etc.)
- **Applies** Fowler refactoring techniques (Extract Method, Replace Conditional with Polymorphism, Introduce Parameter Object, Guard Clauses, etc.)
- **Reaches for design patterns** (Strategy, Factory, Builder, Observer, Decorator, etc.) when the code shape genuinely calls for them — never "pattern happy"
- **Cross-checks** against language-specific linter rules without running the linters
- **Outputs code, not lectures** — single-line header comment naming the refactorings applied, then clean code

Supports `.py`, `.js`, `.ts`, `.jsx`, `.tsx`, `.cpp`, `.c`, `.go`, `.java`, `.cs`, `.rb`, `.php`, `.rs`, and other programming language files. Activates when you ask to refactor, clean up, restructure, modernize, or improve code — or mention code smells, SOLID principles, design patterns, legacy code, or tech debt.

## Compatibility

| Platform | Supported? | Install method |
|---|---|---|
| Claude Code | ✅ | `/plugin install` from this repo's marketplace |
| Claude.ai (web / desktop) | ✅ | Upload `.skill` zip via Settings → Capabilities → Skills |
| ChatGPT | ✅ | Skills menu under your profile |
| Codex CLI | ✅ | Drop folder into `~/.codex/skills/`, run with `--enable skills` |
| Gemini CLI | ✅ | `gemini skills install` from this repo |
| Cursor | ✅ | Drop folder into `.cursor/skills/` (project) or `~/.cursor/skills/` (global) |
| GitHub Copilot (VS Code) | ✅ | Skills integration in recent VS Code releases |
| Goose, Windsurf, Amp, Roo, Trae, Factory, OpenCode | ✅ | Each follows the Agent Skills standard — consult its docs for the skills directory |
| Ollama (direct) | ❌ | Ollama serves raw models; it has no skills runtime |
| Ollama via OpenClaw / Goose / Continue | ✅ | The framework loads the skill; Ollama serves the model underneath |
| Gemini consumer web app | ❌ | Google's consumer Gemini has no skills system (Gems are a different mechanism) |

The skill itself is one `SKILL.md` plus a `references/` folder. Every platform above reads the same file — what changes is only where the file lives on disk, and that's documented per-platform below.

## Install

### Claude Code (recommended for this repo's primary install path)

```
/plugin marketplace add YOUR_GITHUB_USERNAME/refactor-code-skill
/plugin install refactor-code@refactor-code
```

### Claude.ai (web and desktop)

Build a `.skill` file from this repo, then upload via Settings → Capabilities → Skills:

```bash
git clone https://github.com/YOUR_GITHUB_USERNAME/refactor-code-skill
cd refactor-code-skill/plugins/refactor-code/skills
zip -r ../../../refactor-code.skill refactor-code/
```

Upload the resulting `refactor-code.skill` file in the Claude.ai skills UI.

### ChatGPT

ChatGPT accepts skills that follow the Agent Skills open standard. Clone this repo, then upload the `plugins/refactor-code/skills/refactor-code/` folder (or the `.skill` file built above) via your profile → Skills → Install.

### Codex CLI

Clone the skill into your Codex skills directory, then run Codex with the skills flag:

```bash
# Clone just the skill folder (not the whole marketplace wrapper)
git clone --depth 1 --filter=blob:none --sparse \
  https://github.com/YOUR_GITHUB_USERNAME/refactor-code-skill /tmp/refactor-code-skill
cd /tmp/refactor-code-skill
git sparse-checkout set plugins/refactor-code/skills/refactor-code
cp -r plugins/refactor-code/skills/refactor-code ~/.codex/skills/

# Run Codex with skills enabled
codex --enable skills
```

For project-scoped installation, put the skill in `.agents/skills/` inside your project root instead. Restart Codex after install so it rescans.

### Gemini CLI

Gemini CLI has first-class skill install commands:

```bash
# User scope (available across all workspaces)
gemini skills install https://github.com/YOUR_GITHUB_USERNAME/refactor-code-skill.git \
  --path plugins/refactor-code/skills/refactor-code

# Or workspace scope (committed to the current repo's .gemini/skills/)
gemini skills install https://github.com/YOUR_GITHUB_USERNAME/refactor-code-skill.git \
  --path plugins/refactor-code/skills/refactor-code \
  --scope workspace
```

Verify with `gemini skills list`. Manage from inside an interactive session with `/skills`.

### Cursor

Copy into the Cursor skills directory — project-scoped (committed to the repo) or user-scoped:

```bash
# Clone the repo first
git clone https://github.com/YOUR_GITHUB_USERNAME/refactor-code-skill /tmp/refactor-code-skill

# Project scope (recommended for team-shared skills)
mkdir -p .cursor/skills
cp -r /tmp/refactor-code-skill/plugins/refactor-code/skills/refactor-code .cursor/skills/

# Or user scope
mkdir -p ~/.cursor/skills
cp -r /tmp/refactor-code-skill/plugins/refactor-code/skills/refactor-code ~/.cursor/skills/
```

Restart Cursor to discover the skill. Invoke with `/refactor-code` or let the agent pick it up from your natural-language request.

### Vercel `skills` CLI (one command, 20+ agents)

The `skills` CLI by Vercel Labs installs into every agent it detects on your machine:

```bash
# See which agents the CLI can target
npx skills list

# Install this skill into all detected agents
npx skills add YOUR_GITHUB_USERNAME/refactor-code-skill --skill refactor-code

# Or target specific agents only
npx skills add YOUR_GITHUB_USERNAME/refactor-code-skill \
  --skill refactor-code -a claude-code -a cursor -a codex
```

This is the easiest path if you use more than one agent and want the skill synced across all of them.

### Ollama (via an agent framework)

Ollama itself serves models — it doesn't have a skills runtime. To use this skill with an Ollama-served model, run it through an agent framework that speaks the Agent Skills standard. Options include:

- **[Goose](https://block.github.io/goose/)** (Block) — install the skill into Goose's skills directory, point Goose at your Ollama endpoint
- **OpenClaw** — same pattern; installs skills from GitHub, talks to Ollama for model inference
- **[Continue](https://continue.dev)** — supports skills in recent versions

The skill folder contents are identical across all of them; only the install path changes.

## Using the skill

Once installed on any platform, invoke naturally:

> refactor this function, it's a mess

> can you clean up this class? it's got that primitive obsession problem

> apply strategy pattern to this dispatch logic

> this file has too many responsibilities, split it up

The skill diagnoses smells first, picks refactorings by name, and emits code with a single-line header comment listing what was applied. No essays.

## Repo layout

```
refactor-code-skill/
├── .claude-plugin/
│   └── marketplace.json              ← Claude Code marketplace catalog
├── plugins/refactor-code/
│   ├── .claude-plugin/
│   │   └── plugin.json               ← Claude Code plugin manifest
│   ├── skills/refactor-code/         ← the portable skill itself
│   │   ├── SKILL.md                  (this is what every platform loads)
│   │   └── references/
│   │       ├── code-smells.md
│   │       ├── refactoring-techniques.md
│   │       ├── design-patterns.md
│   │       └── linting-by-language.md
│   └── evals/
│       ├── evals.json                # 3 realistic test prompts
│       └── inputs/                   # input code samples
├── README.md
└── LICENSE
```

The `plugins/refactor-code/skills/refactor-code/` directory is the **portable unit** — that's what you copy into any other agent's skills directory. The wrapping `plugins/` and `.claude-plugin/` layers exist only to make this repo double as a Claude Code marketplace.

## Updating

For Claude Code:

```
/plugin marketplace update refactor-code
```

For Gemini CLI: re-run `gemini skills install` with the same arguments. For the Vercel CLI: `npx skills update`. For everything else, re-copy the skill folder from a fresh clone.

## License

MIT — see [LICENSE](./LICENSE). Attribution-friendly; use, modify, and redistribute freely.

## Contributing

Issues and PRs welcome. The skill was built using the [skill-creator](https://github.com/anthropics/skills) workflow. Evals live in `plugins/refactor-code/evals/` — add a new test case there if you find a refactoring scenario the skill handles poorly, and open a PR with the fix.

## Further reading

- [Agent Skills specification](https://agentskills.io/specification) — the open standard this skill conforms to
- [refactoring.guru](https://refactoring.guru/) — the catalog of smells, refactorings, and patterns referenced throughout
- [Claude Code plugin marketplaces](https://code.claude.com/docs/en/plugin-marketplaces)
- [Codex CLI skills docs](https://developers.openai.com/codex/skills)
- [Gemini CLI skills docs](https://geminicli.com/docs/cli/skills/)
- [Vercel `skills` CLI](https://github.com/vercel-labs/skills)
