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
import json, os, sys, sqlite3, platform, glob, subprocess

VERSION = "1.2.0"


def get_db_path():
    """Find VS Code's state.vscdb, handling multiple installs (Code, VSCodium, Cursor, etc.)."""
    system = platform.system()

    if system == "Darwin":
        base = os.path.expanduser("~/Library/Application Support")
    elif system == "Linux":
        base = os.environ.get("XDG_CONFIG_HOME", os.path.expanduser("~/.config"))
    elif system == "Windows":
        base = os.path.expanduser(os.environ.get("APPDATA", "~/AppData/Roaming"))
    else:
        print(f"Unsupported OS: {system}")
        sys.exit(1)

    # Try common VS Code app names in order of likelihood
    app_names = ["Code", "VSCodium", "Cursor", "GitHub Codespaces", "Code - OSS"]

    # First check if VSCODE_PID is set (we're running inside VS Code)
    vscode_pid = os.environ.get("VSCODE_PID")
    if vscode_pid:
        # Try to find the app name from the parent process
        try:
            if system == "Darwin":
                cmd = ["ps", "-o", "comm=", "-p", vscode_pid]
            else:
                cmd = ["ps", "-o", "comm=", "-p", vscode_pid]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=2)
            parent = result.stdout.strip().lower()
            if "codium" in parent:
                app_names = ["VSCodium"] + [a for a in app_names if a != "VSCodium"]
            elif "cursor" in parent:
                app_names = ["Cursor"] + [a for a in app_names if a != "Cursor"]
        except (subprocess.SubprocessError, OSError):
            pass

    # Search for the database file
    for app in app_names:
        db_path = os.path.join(base, app, "User/globalStorage/state.vscdb")
        if os.path.exists(db_path):
            return db_path

    # Fallback: search all subdirectories
    pattern = os.path.join(base, "*/User/globalStorage/state.vscdb")
    matches = glob.glob(pattern)
    if matches:
        return matches[0]

    print(f"Error: Could not find VS Code state.vscdb in {base}")
    print("Tried app names: {0}".format(", ".join(app_names)))
    sys.exit(1)


DB_PATH = get_db_path()

# Category keywords — matched against tool names (order matters, first match wins)
# Each entry is (category, [keywords]) — keywords are matched as substrings (case-insensitive)
CATEGORY_KEYWORDS = [
    ('browser',     ['click_element', 'drag_element', 'handle_dialog', 'hover_element',
                     'navigate_page', 'open_browser', 'read_page', 'run_playwright',
                     'screenshot_page', 'type_in_page']),
    ('terminal',    ['run_in_terminal', 'get_terminal', 'kill_terminal', 'send_to_terminal',
                     'terminal_last', 'terminal_selection']),
    ('notebook',    ['configure_notebook', 'configure_python_environment', 'notebook_install',
                     'notebook_list', 'python_environment', 'python_executable',
                     'install_python_packages', 'runNotebookCell', 'getNotebookSummary',
                     'readNotebookCellOutput']),
    ('testing',     ['runTests', 'testFailure', 'run_task', 'get_task_output',
                     'create_and_run_task']),
    ('mcp',         ['mcp_provides_tool_', 'container-tools_']),
    ('memory',      ['copilot_memory', 'resolveMemory']),
    ('github',      ['copilot_github', 'githubRepo', 'githubTextSearch']),
    ('web',         ['copilot_fetchWeb']),
    ('vscode',      ['vscode_', 'copilot_install', 'copilot_createNew', 'copilot_runVscode',
                     'copilot_getVSCode', 'copilot_getErrors']),
    ('chat',        ['runSubagent', 'execution_subagent', 'manage_todo']),
    ('file_ops',    ['copilot_create', 'copilot_edit', 'copilot_read', 'copilot_view',
                     'copilot_search', 'copilot_find', 'copilot_list']),
]

# Cache: built once per run from actual tools in the database
_CATEGORY_CACHE = {}

def build_category_map(data):
    """Build category->tools mapping dynamically from actual tools in database."""
    categories = {}
    for tool_name, enabled in data['toolEntries']:
        cat = categorize_tool(tool_name)
        categories.setdefault(cat, []).append(tool_name)
    return categories

def categorize_tool(name):
    """Categorize a tool by matching against keyword list (first match wins)."""
    # Check cache first
    if name in _CATEGORY_CACHE:
        return _CATEGORY_CACHE[name]
    
    for category, keywords in CATEGORY_KEYWORDS:
        for keyword in keywords:
            if keyword.lower() in name.lower():
                _CATEGORY_CACHE[name] = category
                return category
    _CATEGORY_CACHE[name] = 'other'
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
        else:
            # Try to match as individual tool name (substring or exact)
            found = False
            for tool_name, _ in data['toolEntries']:
                if tool_name == arg or arg.lower() in tool_name.lower():
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
