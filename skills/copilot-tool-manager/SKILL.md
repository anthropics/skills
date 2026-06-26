---
name: copilot-tool-manager
description: >
  Enable, disable, and manage VS Code Copilot agent tools by category.
  Optimize your context window by selectively disabling unused tools.
  Dynamically discovers tools from your VS Code database with pattern-based categorization.
---

# Copilot Tool Manager

Enable, disable, and manage VS Code Copilot agent tools by category. Optimize your context window by selectively disabling unused tools.

## Triggers
- "disable tools", "enable tools", "toggle tools"
- "show tool status", "list tools"
- "context window optimization", "reduce context usage"
- "disable browser tools", "enable terminal tools"
- "which tools are enabled", "what tools consume most context"

## Why This Matters

- Tool definitions consume **~22-25% of the context window**
- Disabling unused tools frees up context for your actual work
- Not linear: browser tools (10 tools) consume more tokens than memory tools (2 tools) combined

## Fastest Method: Helper Script

Use the `copilot-tools.py` script in this skill directory:

```bash
python3 copilot-tools.py status                    # Show current state
python3 copilot-tools.py disable browser           # Disable browser tools
python3 copilot-tools.py enable browser            # Enable browser tools
python3 copilot-tools.py disable terminal github   # Disable multiple categories
python3 copilot-tools.py list                      # List all tools with status
python3 copilot-tools.py disable_tool click_element  # Disable a single tool
python3 copilot-tools.py enable_tool click_element   # Enable a single tool
```

Categories: `browser`, `file_ops`, `terminal`, `vscode`, `chat`, `github`, `memory`, `other`

## Database Details

### Database Location

| OS | Path |
|----|------|
| macOS | `~/Library/Application Support/Code/User/globalStorage/state.vscdb` |
| Linux | `~/.config/Code/User/globalStorage/state.vscdb` |
| Windows | `%APPDATA%\Code\User\globalStorage\state.vscdb` |

### Database Schema

- **Table:** `ItemTable`
- **Key:** `chat/selectedTools`
- **Value:** JSON with `toolEntries` array of `[tool_name, boolean]` pairs

## Tool Categories (73 total tools)

| Category | Count | Token Cost | Safe to Disable? |
|----------|-------|------------|------------------|
| **Browser** (10) | click, drag, hover, navigate, screenshot, etc. | **High** | ✅ Yes (if no web dev) |
| **File Operations** (9) | read, write, search, create files | Medium | ❌ No (core functionality) |
| **VS Code** (8) | rename, find usages, extensions | Medium | ⚠️ Partial |
| **Terminal** (6) | run commands, get output | Medium | ⚠️ Partial |
| **Chat/Agents** (3) | subagent, todo list | Low | ❌ No |
| **GitHub/Web** (3) | fetch page, search repos | Low | ⚠️ Optional |
| **Memory** (2) | persistent notes | Low | ⚠️ Optional |
| **Other** (2) | notebook edit, get errors | Low | ✅ Yes |

## Tool Name Reference

### Browser tools (10)
`click_element`, `drag_element`, `handle_dialog`, `hover_element`, `navigate_page`, `open_browser_page`, `read_page`, `run_playwright_code`, `screenshot_page`, `type_in_page`

### File operations (9)
`copilot_createDirectory`, `copilot_createFile`, `copilot_editFiles`, `copilot_readFile`, `copilot_viewImage`, `copilot_searchCodebase`, `copilot_findFiles`, `copilot_listDirectory`, `copilot_findTextInFiles`

### VS Code tools (8)
`vscode_renameSymbol`, `vscode_listCodeUsages`, `vscode_askQuestions`, `vscode_searchExtensions_internal`, `copilot_installExtension`, `copilot_createNewWorkspace`, `copilot_runVscodeCommand`, `copilot_getVSCodeAPI`

### Terminal tools (6)
`get_terminal_output`, `kill_terminal`, `run_in_terminal`, `send_to_terminal`, `terminal_last_command`, `terminal_selection`

### Chat/Agent tools (3)
`runSubagent`, `execution_subagent`, `manage_todo_list`

### GitHub/Web tools (3)
`copilot_fetchWebPage`, `copilot_githubRepo`, `copilot_githubTextSearch`

### Memory tools (2)
`copilot_memory`, `copilot_resolveMemoryFileUri`

### Other tools (2)
`copilot_editNotebook`, `copilot_getErrors`

## Usage Patterns

### When user asks to disable/enable tools:
1. Run the helper script: `python3 copilot-tools.py disable <category>`
2. Tell user to start a new chat session for changes to take effect

### When user asks about context window optimization:
1. Check which categories are still enabled
2. Suggest disabling "heavy" categories first (browser → file ops → VS Code)
3. Show expected impact based on category token cost

### Common presets:
- **Thesis writing**: Disable browser, github, memory, other
- **Web development**: Keep browser, terminal, file_ops; disable memory, other
- **Minimal**: Only keep file_ops + terminal + chat (~20 tools)

## Safety Notes

- ⚠️ **Close VS Code** before running commands to avoid database conflicts
- 💡 Start by disabling just `browser` tools (safest, highest impact)
- 🔄 Changes take effect on next Copilot chat session
- 📋 Use `status` command to verify state before/after changes
