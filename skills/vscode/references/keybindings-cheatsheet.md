# Keyboard Shortcuts Cheat Sheet

A curated list of the **most remapped** VS Code shortcuts. Use this when a user asks "how do I rebind X?" or "what's the default for Y?". The full default list (~1000 entries) lives at <https://code.visualstudio.com/docs/getstarted/keybindings>.

For the live editor that lists every default, open **File → Preferences → Keyboard Shortcuts** (Ctrl+K Ctrl+S).

## Format

Each row lists the **default chord** (Windows / Linux; macOS differs — see live docs for macOS symbols) and a one-line description. Key notation:

* `Ctrl` — control on Windows / Linux, ⌘ on macOS
* `Shift` — shift on all platforms
* `Alt` — alt on Windows / Linux, ⌥ on macOS
* `Chord` — two keys in sequence (e.g., `Ctrl+K Ctrl+S` means press Ctrl+K, release, then Ctrl+S)

## File & Editor

| Chord | Command |
|---|---|
| `Ctrl+N` | New file |
| `Ctrl+O` | Open file |
| `Ctrl+S` | Save |
| `Ctrl+Shift+S` | Save As |
| `Ctrl+K Ctrl+S` | Open keyboard shortcuts (chord) |
| `Ctrl+W` | Close editor |
| `Ctrl+Shift+T` | Reopen closed editor |
| `Ctrl+P` | Quick open file |
| `Ctrl+Shift+P` | Show all commands (Command Palette) |
| `Ctrl+G` | Go to line |
| `Ctrl+T` | Show all symbols by name |
| `Ctrl+Shift+O` | Go to symbol in file |
| `F12` | Go to definition |
| `Alt+F12` | Peek definition |
| `F2` | Rename symbol |
| `Ctrl+F2` | Find all references |
| `Ctrl+.` | Quick fix (lightbulb) |
| `Ctrl+Shift+K` | Delete line |
| `Alt+↑ / Alt+↓` | Move line up / down |
| `Shift+Alt+↑ / Shift+Alt+↓` | Copy line up / down |
| `Ctrl+/` | Toggle line comment |
| `Ctrl+Shift+A` | Toggle block comment |
| `Ctrl+D` | Add selection to next find match |
| `Ctrl+Shift+L` | Select all occurrences |
| `Alt+Click` | Insert cursor |
| `Ctrl+Alt+↑ / Ctrl+Alt+↓` | Insert cursor above / below |

## Navigation

| Chord | Command |
|---|---|
| `Ctrl+Tab` | Cycle through editors |
| `Ctrl+Shift+Tab` | Cycle through editors (reverse) |
| `Ctrl+1 / Ctrl+2 / ...` | Focus editor group 1, 2, ... |
| `Ctrl+K Ctrl+←/→` | Move editor left / right |
| `Ctrl+Alt+←/→` | Navigate back / forward |
| `Ctrl+E` | Quick open file (alt) |
| `Ctrl+B` | Toggle sidebar |
| `Ctrl+J` | Toggle panel |
| `Ctrl+`` ` | Toggle terminal |
| `Ctrl+Shift+`` ` | Create new terminal |
| `Ctrl+Shift+E` | Focus Explorer |
| `Ctrl+Shift+F` | Focus Search |
| `Ctrl+Shift+G` | Focus Source Control |
| `Ctrl+Shift+D` | Focus Run and Debug |
| `Ctrl+Shift+X` | Focus Extensions |

## Search & Replace

| Chord | Command |
|---|---|
| `Ctrl+F` | Find |
| `Ctrl+H` | Replace |
| `Ctrl+Shift+F` | Find in files |
| `Ctrl+Shift+H` | Replace in files |
| `Alt+C` | Toggle case-sensitive |
| `Alt+W` | Toggle whole-word match |
| `Alt+R` | Toggle regex |

## Debug

| Chord | Command |
|---|---|
| `F5` | Start / continue debugging |
| `Shift+F5` | Stop debugging |
| `F9` | Toggle breakpoint |
| `F10` | Step over |
| `F11` | Step into |
| `Shift+F11` | Step out |
| `Ctrl+Shift+F5` | Restart debugging |

## Tasks & Refactor

| Chord | Command |
|---|---|
| `Ctrl+Shift+B` | Run build task |
| `Ctrl+Shift+P → "Tasks: Run Task"` | Pick a task |
| `Ctrl+Shift+P → "Format Document"` | Format whole document |
| `Ctrl+Shift+P → "Organize Imports"` | Organize imports |

## Common Customizations

These are the most-requested rebinds:

| From | To | Why |
|---|---|---|
| `Ctrl+P` | `Ctrl+P` (unchanged) | Keep as quick open — already great. |
| `Ctrl+Shift+P` | `F1` | Many users keep `F1` as the canonical "command palette". |
| `Ctrl+`` ` | `Ctrl+`` ` (unchanged) | Toggle terminal — convenient. |
| `Alt+Click` | `Ctrl+Alt+Click` | Avoid accidental multi-cursor when using Alt for menu navigation. |

To rebind a chord, edit `keybindings.json` (user-level) or `.vscode/keybindings.json` (workspace-level). Format:

```json
[
  {
    "key": "ctrl+shift+p",
    "command": "workbench.action.showCommands"
  }
]
```

The skill does not currently provide a `keybindings set` command; edit `keybindings.json` directly.

## See Also

* Live default list: <https://code.visualstudio.com/docs/getstarted/keybindings>
* Live editor: File → Preferences → Keyboard Shortcuts (Ctrl+K Ctrl+S)