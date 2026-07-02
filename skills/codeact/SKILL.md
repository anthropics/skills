---
name: codeact
description: |
  Collapse multi-step tool chains into a single sandboxed Python run.
  Use instead of chained tool calls when a task reads 8+ files,
  cross-references multiple file sets, or needs 5+ sequential tool calls.
  NOT beneficial for simple grep-then-view workflows (≤5 files).
  ESPECIALLY valuable when MCP servers are loaded — fewer turns means the
  MCP tool catalog context is replayed fewer times.
  Trigger on: "codeact", "sandbox execution", "batch file ops",
  "collapse tool calls", "for each file", "chain tools".
---

# CodeAct — Sandboxed Python Execution

Collapse multi-step tool chains into a single sandboxed Python run. Instead
of N sequential tool calls (model → tool → model → tool …), write one Python
program that chains all the work together and executes it in one turn.

## Why

Each tool call replays the full conversation context — system prompt, tool
definitions, prior messages. With MCP servers loaded, every server's tool
catalog adds to that overhead. Collapsing N calls into one program eliminates
the replay.

Measured savings on real tasks:

| Task | Turns | Input tokens | Savings |
|------|:-----:|:------------:|:-------:|
| Test coverage + 4 MCP servers | 6 → 2 | 335K → 103K | **69%** |
| Full project function index | 4 → 2 | 130K → 57K | **57%** |
| Docstring coverage | 3 → 2 | 86K → 56K | **49%** |

## Prerequisites

Install the plugin first. Add to `~/.claude/settings.json`:

```jsonc
{
  "extraKnownMarketplaces": {
    "codeact-rajatverma-p": {
      "source": {
        "source": "github",
        "repo": "RajatVerma-p/claude-codeact-plugin"
      }
    }
  },
  "enabledPlugins": {
    "codeact@codeact-rajatverma-p": true
  }
}
```

Then run `/codeact-install` in Claude Code. It auto-detects the best backend
for your machine and writes the instructions file. Restart the session to load.

## Backends

| Backend | Startup | Python | Requires |
|---------|:-------:|:------:|:---------|
| **monty** | ~1ms | Subset (no classes, no match/case) | Python 3.10+ |
| **hyperlight** | ~680ms | Full 3.10–3.13 | Python 3.10–3.13, `/dev/kvm` on Linux |

Auto-detection picks hyperlight on Linux with KVM, monty everywhere else.
Force a specific backend with `/codeact-install-monty` or
`/codeact-install-hyperlight`.

## Usage

Once installed, write a single Python program using sandbox functions instead
of individual tool calls.

### Monty backend — functions called directly

```python
for f in glob(pattern="**/*.py", paths="src"):
    try:
        content = view(path=f)
    except Exception:
        continue
    todos = [l for l in content.split("\n") if "TODO" in l]
    if todos:
        print(f + ": " + str(len(todos)) + " TODOs")
```

### Hyperlight backend — functions via `call_tool()`

```python
for f in call_tool('glob', pattern='**/*.py', paths='src'):
    try:
        content = call_tool('view', path=f)
    except Exception:
        continue
    todos = [l for l in content.splitlines() if 'TODO' in l]
    if todos:
        print(f"{f}: {len(todos)} TODOs")
```

## Sandbox tools

`view`, `create`, `edit`, `glob`, `bash`, `sql`, `web_fetch`, `github_api`,
`mcp_call` — auto-discovered at install time based on what's available on
the host.

## Rules

- **One bash call, one program.** Do not scout with separate tool calls first.
  Write one program that globs, reads, analyzes, and prints results.
- **Wrap file reads in try/except.** One bad file should not abort the run.
- **Keep output minimal.** Print summaries and key findings only — not raw
  file contents. Output must fit in a single tool response (~5 KB).
- **Skip for small tasks.** Direct tool calls have less overhead for ≤5 files
  or single grep → view → done workflows.

## Return types (critical — wrong assumptions cause retries)

- `glob` → **list of strings** like `["src/app.py", "src/utils.py"]`
- `view` → **string** (full file content)
- `bash` → **dict** with `stdout`, `stderr`, `returncode`
- `mcp_call` → **string**

## Source

Plugin repo: [RajatVerma-p/claude-codeact-plugin](https://github.com/RajatVerma-p/claude-codeact-plugin)  
Adapted from: [jsturtevant/copilot-codeact-plugin](https://github.com/jsturtevant/copilot-codeact-plugin)
