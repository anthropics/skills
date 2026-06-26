#!/usr/bin/env python3
"""
Copilot Tool Manager - Fast enable/disable of Copilot agent tools.

Dynamically discovers tools from your VS Code database (no hardcoded names).
Categories are inferred from tool name prefixes/patterns.

Usage:
  ./copilot-tools.py status                    # Show current state
  ./copilot-tools.py disable browser           # Disable browser tools
  ./copilot-tools.py enable browser            # Enable browser tools
  ./copilot-tools.py disable terminal github   # Disable multiple categories
  ./copilot-tools.py list                      # List all tools with status
  ./copilot-tools.py disable_tool click_element  # Disable a single tool
  ./copilot-tools.py enable_tool click_element   # Enable a single tool
  ./copilot-tools.py unknown                   # Show uncategorized tools

Categories: browser, file_ops, terminal, vscode, chat, github, memory, other
"""
import json, os, sys, sqlite3, platform, re

VERSION = "1.1.0"

# Cross-platform database path
system = platform.system()
if system == "Darwin":
    DB_PATH = os.path.expanduser("~/Library/Application Support/Code/User/globalStorage/state.vscdb")
elif system == "Linux":
    DB_PATH = os.path.expanduser("~/.config/Code/User/globalStorage/state.vscdb")
elif system == "Windows":
    DB_PATH = os.path.expanduser("~/AppData/Roaming/Code/User/globalStorage/state.vscdb")
else:
    print(f"Unsupported OS: {system}")
    sys.exit(1)

# Category patterns - matched against tool names (regex)
CATEGORY_PATTERNS = {
    'browser': [
        r'click_element', r'drag_element', r'handle_dialog', r'hover_element',
        r'navigate_page', r'open_browser', r'read_page', r'run_playwright',
        r'screenshot', r'type_in_page'
    ],
    'file_ops': [
        r'copilot_create', r'copilot_edit', r'copilot_read', r'copilot_view',
        r'copilot_search', r'copilot_find', r'copilot_list'
    ],
    'terminal': [
        r'run_in_terminal', r'get_terminal', r'kill_terminal', r'send_to_terminal',
        r'terminal_last', r'terminal_selection'
    ],
    'vscode': [
        r'vscode_', r'copilot_install', r'copilot_createNew', r'copilot_runVscode',
        r'copilot_getVSCode', r'copilot_getErrors', r'copilot_getNotebookSummary',
        r'copilot_runNotebookCell'
    ],
    'notebook': [
        r'configure_notebook', r'configure_python_environment', r'notebook_install',
        r'notebook_list', r'get_python_environment', r'get_python_executable',
        r'install_python_packages', r'copilot_runNotebookCell'
    ],
    'testing': [
        r'runTests', r'testFailure', r'run_task', r'get_task_output', r'create_and_run_task'
    ],
    'mcp': [
        r'mcp_provides_tool_'
    ],
    'chat': [
        r'runSubagent', r'execution_subagent', r'manage_todo'
    ],
    'github': [
        r'copilot_fetchWeb', r'copilot_github', r'copilot_githubText'
    ],
    'memory': [
        r'copilot_memory', r'copilot_resolveMemory'
    ],
}

def categorize_tool(name):
    """Dynamically categorize a tool name using pattern matching."""
    for category, patterns in CATEGORY_PATTERNS.items():
        for pattern in patterns:
            if re.search(pattern, name, re.IGNORECASE):
                return category
    return 'other'

def discover_categories(data):
    """Build categories dynamically from actual tools in database."""
    categories = {}
    for tool_name, enabled in data['toolEntries']:
        cat = categorize_tool(tool_name)
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(tool_name)
    return categories

def get_data():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT value FROM ItemTable WHERE key='chat/selectedTools'")
    row = cur.fetchone()
    if not row:
        print("Error: No tool config found. Have you used Configure Tools UI at least once?")
        sys.exit(1)
    data = json.loads(row[0])
    conn.close()
    return data

def save_data(data):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("UPDATE ItemTable SET value=? WHERE key='chat/selectedTools'", (json.dumps(data),))
    conn.commit()
    conn.close()

def status(data):
    categories = discover_categories(data)
    enabled = [k for k,v in data['toolEntries'] if v]
    disabled = [k for k,v in data['toolEntries'] if not v]
    print(f"Copilot Tool Manager v{VERSION}")
    print(f"Enabled: {len(enabled)}, Disabled: {len(disabled)}, Total: {len(data['toolEntries'])}")
    print()
    for cat in sorted(categories.keys()):
        tools = categories[cat]
        cat_enabled = sum(1 for t in tools if any(t == e[0] and e[1] for e in data['toolEntries']))
        cat_disabled = len(tools) - cat_enabled
        status_icon = "✓" if cat_disabled == 0 else ("✗" if cat_enabled == 0 else "◐")
        print(f"  {status_icon} {cat}: {cat_enabled}/{len(tools)} enabled")

def toggle(data, action, *args):
    categories = discover_categories(data)
    tools_to_toggle = []
    unknown = []
    for arg in args:
        if arg in categories:
            tools_to_toggle.extend(categories[arg])
        elif arg in CATEGORY_PATTERNS:
            tools_to_toggle.extend(categories.get(arg, []))
        else:
            # Try to match as individual tool name
            found = False
            for tool_name, _ in data['toolEntries']:
                if tool_name == arg or re.search(arg, tool_name, re.IGNORECASE):
                    tools_to_toggle.append(tool_name)
                    found = True
            if not found:
                unknown.append(arg)
    
    if unknown:
        print(f"Warning: Unknown category/tool: {', '.join(unknown)}")
        print(f"Available categories: {', '.join(sorted(categories.keys()))}")
    
    if not tools_to_toggle:
        return
    
    # Deduplicate
    tools_to_toggle = list(set(tools_to_toggle))
    
    for entry in data['toolEntries']:
        if entry[0] in tools_to_toggle:
            entry[1] = (action == 'enable')
    
    save_data(data)
    enabled = [k for k,v in data['toolEntries'] if v]
    disabled = [k for k,v in data['toolEntries'] if not v]
    action_verb = "Enabled" if action == 'enable' else "Disabled"
    print(f"Done. Enabled: {len(enabled)}, Disabled: {len(disabled)}")
    print(f"  {action_verb}: {len(tools_to_toggle)} tools")

def list_tools(data):
    categories = discover_categories(data)
    for cat in sorted(categories.keys()):
        tools = categories[cat]
        print(f"\n{cat.upper()}:")
        for t in sorted(tools):
            for entry in data['toolEntries']:
                if entry[0] == t:
                    status_str = "✓ enabled" if entry[1] else "✗ disabled"
                    print(f"  {t}: {status_str}")
                    break

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(0)
    
    data = get_data()
    cmd = sys.argv[1]
    
    if cmd == 'status':
        status(data)
    elif cmd == 'list':
        list_tools(data)
    elif cmd in ('disable', 'enable'):
        toggle(data, cmd, *sys.argv[2:])
    elif cmd == 'disable_tool':
        toggle(data, 'disable', sys.argv[2])
    elif cmd == 'enable_tool':
        toggle(data, 'enable', sys.argv[2])
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)
