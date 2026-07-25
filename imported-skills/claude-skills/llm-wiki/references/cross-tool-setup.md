# Cross-Tool Setup

The LLM Wiki plugin is tool-agnostic. The **scripts** are pure Python stdlib and run anywhere. Only the **schema loader file** (the file the tool reads to understand conventions) differs per tool.

## How different CLIs discover project-level instructions

| Tool | Loader file | Notes |
|---|---|---|
| Claude Code | `CLAUDE.md` | Loaded automatically when CC starts in the vault dir |
| Codex CLI (OpenAI) | `AGENTS.md` | Loaded at session start |
| Cursor (new) | `AGENTS.md` | Modern Cursor reads `AGENTS.md` |
| Cursor (legacy) | `.cursorrules` | Older Cursor versions |
| Google Antigravity | `AGENTS.md` | Uses the standard `AGENTS.md` convention |
| OpenCode / Pi | `AGENTS.md` | Same convention |
| Gemini CLI | `AGENTS.md` | Same convention |
| Aider | `CONVENTIONS.md` or `.aider.conf.yml` | Point Aider at `CLAUDE.md` with `--read CLAUDE.md` |

**Recommendation:** ship **both** `CLAUDE.md` and `AGENTS.md` in every vault. `init_vault.py --tool all` does this by default.

## Multi-tool vault

If you use multiple CLIs against the same vault:

```bash
python scripts/init_vault.py --path ~/vaults/research --topic "X" --tool all
```

This creates:
- `CLAUDE.md`
- `AGENTS.md`
- `.cursorrules`

All three are **the same content**, formatted appropriately. You can symlink to keep them in sync:

```bash
cd <vault>
ln -sf CLAUDE.md AGENTS.md
# or edit both manually when you tune the schema
```

## Per-tool quickstart

### Claude Code

```bash
cd <vault>
claude
> /wiki-init              # if vault isn't initialized
> /wiki-ingest raw/paper.pdf
> /wiki-query "what does the paper say about X?"
```

The slash commands ship with this plugin. To install the plugin itself, either:
- Clone claude-code-skills and copy `engineering/llm-wiki/` into `~/.claude/skills/`, or
- Install via the marketplace if published

### Codex CLI

Codex reads `AGENTS.md` automatically. Then:

```bash
cd <vault>
codex
> ingest raw/paper.pdf into the wiki
> query: what does the paper say about X?
```

Codex doesn't have slash commands, but the schema file teaches it the ingest/query/lint workflow, so natural-language triggers work.

### Cursor

```bash
cd <vault>
cursor .
```

Open the Cursor chat in the sidebar. Cursor auto-reads `AGENTS.md`. Ask the same questions.

### Antigravity / OpenCode / Pi

Same as Codex — drop `AGENTS.md` in the vault root and use natural language.

### Multi-tool same session

You can run Claude Code and Codex **simultaneously** against the same vault. They'll both see updates if one writes a page — filesystem is the source of truth. Just make sure each vault is committed to git so you can resolve conflicts.

## Running the scripts directly (any tool)

The scripts don't care which tool calls them. You can run them from the shell any time:

```bash
# from inside the vault
python ~/.claude/skills/llm-wiki/scripts/lint_wiki.py --vault .
python ~/.claude/skills/llm-wiki/scripts/update_index.py --vault .
python ~/.claude/skills/llm-wiki/scripts/wiki_search.py --vault . --query "superposition"
```

Aliases are handy. Add to your shell rc:

```bash
alias wiki-lint='python ~/.claude/skills/llm-wiki/scripts/lint_wiki.py --vault .'
alias wiki-index='python ~/.claude/skills/llm-wiki/scripts/update_index.py --vault .'
alias wiki-search='python ~/.claude/skills/llm-wiki/scripts/wiki_search.py --vault .'
```

## MCP exposure (future)

The wiki can be exposed as an MCP tool so any MCP-capable client (Claude Desktop, Claude Code, etc.) can query it. See `engineering/mcp-design` in this repo for the pattern. A future version of this plugin will ship an `mcp/` directory with a reference MCP server.
