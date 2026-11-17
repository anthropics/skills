---
name: obsidian-cli
description: >-
  Interact with Obsidian vaults via the built-in Obsidian CLI (v1.12+).
  Create, read, search, and manage notes, daily notes, tasks, tags, properties,
  templates, plugins, themes, and more. Activate when the user mentions Obsidian,
  their vault, notes, or asks to interact with their knowledge base using the CLI.
allowed-tools: Bash, Read, Write
user-invocable: true
shell: bash
---

# Obsidian CLI Skill

This skill enables Claude to use the **Obsidian CLI** — the command-line interface
built into Obsidian v1.12+ — to interact with your Obsidian vault(s).

## Prerequisites

- **Obsidian v1.12 or later** installed
- **Obsidian app must be running** (the CLI communicates via local IPC)
- **CLI enabled** in Obsidian: *Settings → General → Command line interface → Register CLI*
- **`obsidian` command available** in your shell PATH

To verify:
```bash
obsidian version
```

If not found, add the Obsidian binary to your PATH:
- **macOS**: `/Applications/Obsidian.app/Contents/MacOS/obsidian`
- **Windows**: Typically added automatically after registering in settings
- **Linux**: Depends on installation method (AppImage, Snap, etc.)

## Syntax

```
obsidian <command> [options]
```

### Global Options

| Option | Description |
|--------|-------------|
| `vault=<name>` | Target a specific vault by name (required if multiple vaults) |
| `file=<name>` | Refer to a file by its name (wikilink-style resolution) |
| `path=<path>` | Refer to a file by its exact path (`folder/note.md`) |

### Important Rules

1. **File resolution**: `file=` resolves like wikilinks (by note name, first match wins);
   `path=` uses exact file paths. Most commands default to the **active file** when omitted.
2. **Quoting**: Wrap values containing spaces in quotes: `name="My Note"`.
3. **Escape sequences**: Use `\n` for newlines, `\t` for tabs in content values.
4. **Vault targeting**: If you have only one vault, `vault=` is usually optional.

## Command Reference

See `references/commands.md` for the complete list of all commands with their options.

### Complete Command List by Category

#### File Operations
| Command | Description |
|---------|-------------|
| `create name=<name> [content=] [template=] [open] [newtab] [overwrite]` | Create a new note |
| `read [file=] [path=]` | Read a note's contents |
| `append [file=] [path=] content= [inline]` | Append content to a note |
| `prepend [file=] [path=] content= [inline]` | Prepend content (after frontmatter) |
| `delete [file=] [path=] [permanent]` | Delete a note |
| `move [file=] [path=] to=<path>` | Move a note to another folder |
| `rename [file=] [path=] name=<name>` | Rename a note |
| `file [file=] [path=]` | Show file info |

#### Search & Navigation
| Command | Description |
|---------|-------------|
| `search query=<text> [path=] [limit=] [total] [case] [format=]` | Search vault contents |
| `search:context query=<text> [path=] [limit=] [case] [format=]` | Search with surrounding context |
| `search:open [query=]` | Open search view in Obsidian |
| `open [file=] [path=] [newtab]` | Open a file in Obsidian |
| `random [folder=] [newtab]` | Open a random note |
| `random:read [folder=]` | Read a random note |
| `recents [total]` | List recently opened files |
| `tabs [ids]` | List open tabs |
| `tab:open [group=] [file=] [view=]` | Open a new tab |

#### Daily Notes
| Command | Description |
|---------|-------------|
| `daily [paneType=tab\|split\|window]` | Open today's daily note |
| `daily:read` | Read today's daily note |
| `daily:append content= [inline] [open] [paneType=]` | Append to daily note |
| `daily:prepend content= [inline] [open] [paneType=]` | Prepend to daily note |
| `daily:path` | Get path to daily note |

#### Properties & Tags
| Command | Description |
|---------|-------------|
| `property:set name= value= [type=] [file=] [path=]` | Set a property |
| `property:read name= [file=] [path=]` | Read a property value |
| `property:remove name= [file=] [path=]` | Remove a property |
| `properties [file=] [path=] [name=] [total] [counts] [sort=] [active] [format=]` | List properties in vault |
| `tags [file=] [path=] [total] [counts] [sort=] [active] [format=]` | List tags |
| `tag name=<tag> [total] [verbose]` | Get tag info |

#### Tasks
| Command | Description |
|---------|-------------|
| `tasks [file=] [path=] [total] [done] [todo] [status=] [verbose] [active] [daily] [format=]` | List tasks |
| `task [ref=] [file=] [path=] [line=] [toggle\|done\|todo] [daily] [status=]` | Show or update a task |

#### Templates
| Command | Description |
|---------|-------------|
| `templates [total]` | List available templates |
| `template:read name= [resolve] [title=]` | Read template content |
| `template:insert name=` | Insert template into active file |

#### Links
| Command | Description |
|---------|-------------|
| `backlinks [file=] [path=] [counts] [total] [format=]` | List backlinks to a file |
| `links [file=] [path=] [total]` | List outgoing links from a file |
| `unresolved [total] [counts] [verbose] [format=]` | List unresolved links |
| `deadends [total] [all]` | Files with no outgoing links |
| `orphans [total] [all]` | Files with no incoming links |

#### Vault Info
| Command | Description |
|---------|-------------|
| `files [folder=] [ext=] [total]` | List vault files |
| `folders [folder=] [total]` | List vault folders |
| `folder path= [info=files\|folders\|size]` | Show folder info |
| `vault [info=name\|path\|files\|folders\|size]` | Show vault info |
| `vaults [total] [verbose]` | List known vaults |
| `wordcount [file=] [path=] [words] [characters]` | Count words and characters |
| `outline [file=] [path=] [format=tree\|md\|json] [total]` | Show file headings |

#### Plugin & Theme Management
| Command | Description |
|---------|-------------|
| `plugins [filter=core\|community] [versions] [format=]` | List installed plugins |
| `plugins:enabled [filter=core\|community] [versions] [format=]` | List enabled plugins |
| `plugins:restrict [on\|off]` | Toggle or check restricted mode |
| `plugin id=<plugin-id>` | Get plugin info |
| `plugin:enable id= [filter=core\|community]` | Enable a plugin |
| `plugin:disable id= [filter=core\|community]` | Disable a plugin |
| `plugin:install id= [enable]` | Install a community plugin |
| `plugin:uninstall id=` | Uninstall a community plugin |
| `plugin:reload id=` | Reload a plugin (developer use) |
| `themes [versions]` | List installed themes |
| `theme [name=]` | Show active theme or get theme info |
| `theme:set name=` | Set active theme |
| `theme:install name= [enable]` | Install a community theme |
| `theme:uninstall name=` | Uninstall a theme |

#### History, Sync & Diff
| Command | Description |
|---------|-------------|
| `history [file=] [path=]` | List file history versions |
| `history:list` | List files with history |
| `history:open [file=] [path=]` | Open file recovery |
| `history:read [file=] [path=] [version=]` | Read a specific history version |
| `history:restore [file=] [path=] version=<n>` | Restore a specific version |
| `diff [file=] [path=] [from=] [to=] [filter=local\|sync]` | List or diff versions |
| `sync:status` | Show sync status |
| `sync [on\|off]` | Pause or resume sync |
| `sync:deleted [total]` | List deleted files in sync |
| `sync:history [file=] [path=] [total]` | List sync version history |
| `sync:open [file=] [path=]` | Open sync history |
| `sync:read [file=] [path=] version=<n>` | Read a sync version |
| `sync:restore [file=] [path=] version=<n>` | Restore a sync version |

#### Commands & Automation
| Command | Description |
|---------|-------------|
| `help [<command>]` | Show list of all commands or help for a specific one |
| `command id=<command-id>` | Execute any Obsidian command by ID |
| `commands [filter=]` | List all available commands |
| `workspace [ids]` | Show workspace tree |
| `reload` | Reload the vault |
| `restart` | Restart Obsidian |

#### Aliases
| Command | Description |
|---------|-------------|
| `aliases [file=] [path=] [total] [verbose] [active]` | List aliases in the vault |

#### Bases (Databases)
| Command | Description |
|---------|-------------|
| `bases` | List all base files in vault |
| `base:create [file=] [path=] [view=] [name=] [content=] [open] [newtab]` | Create a new item in a base |
| `base:query [file=] [path=] [view=] [format=]` | Query a base and return results |
| `base:views [file=] [path=]` | List views in a base file |

#### Bookmarks
| Command | Description |
|---------|-------------|
| `bookmarks [total] [verbose] [format=]` | List bookmarks |
| `bookmark [file=] [subpath=] [folder=] [search=] [url=] [title=]` | Add a bookmark |

#### CSS Snippets
| Command | Description |
|---------|-------------|
| `snippets` | List installed CSS snippets |
| `snippets:enabled` | List enabled CSS snippets |
| `snippet:enable name=` | Enable a CSS snippet |
| `snippet:disable name=` | Disable a CSS snippet |

#### Hotkeys
| Command | Description |
|---------|-------------|
| `hotkeys [total] [verbose] [all] [format=]` | List hotkeys |
| `hotkey id=<command-id> [verbose]` | Get hotkey for a command |

#### Other
| Command | Description |
|---------|-------------|
| `web url=<url> [newtab]` | Open URL in Obsidian web viewer |
| `version` | Show Obsidian version |

#### Developer Tools
| Command | Description |
|---------|-------------|
| `eval code=<javascript>` | Execute JavaScript and return result |
| `devtools` | Toggle Electron dev tools |
| `dev:cdp method=<CDP.method> [params=]` | Run Chrome DevTools Protocol command |
| `dev:console [clear] [limit=] [level=]` | Show captured console messages |
| `dev:css selector= [prop=]` | Inspect CSS with source locations |
| `dev:debug [on\|off]` | Attach/detach CDP debugger |
| `dev:dom selector= [total] [text] [inner] [all] [attr=] [css=]` | Query DOM elements |
| `dev:errors [clear]` | Show captured errors |
| `dev:mobile [on\|off]` | Toggle mobile emulation |
| `dev:screenshot [path=]` | Take a screenshot |

## Common Usage Patterns

### Creating notes
```bash
# Simple note
obsidian create name="Meeting Notes" content="Discussed Q4 roadmap"

# Note from a template
obsidian create name="Daily Journal" template="Journal Template" open

# Note in a specific vault
obsidian vault="Work" create name="Sprint Review" content="Sprint 42 completed"
```

### Reading and searching
```bash
# Read a specific file
obsidian read file="Meeting Notes"

# Search vault
obsidian search query="Q4 roadmap" limit=10

# Search with context
obsidian search:context query="action items" format=text
```

### Managing tasks
```bash
# List all incomplete tasks
obsidian tasks todo

# List tasks in a specific file
obsidian tasks file="Project Plan" done

# Toggle task status
obsidian task file="Project Plan" line=12 toggle
```

### Daily notes workflow
```bash
# Log to today's daily note
obsidian daily:append content="- Reviewed PR #42" inline

# Read yesterday's daily note
obsidian vault="Personal" daily:read
```

### Properties
```bash
# Add a property
obsidian property:set file="Meeting Notes" name="Status" value="Done" type=text

# Read a property
obsidian property:read file="Meeting Notes" name="Status"

# Remove a property
obsidian property:remove file="Meeting Notes" name="Old-Prop"
```

## Error Handling Tips

- **"Command not found"**: The Obsidian CLI is not in PATH or not enabled in Settings
- **"No vault specified"**: Use `vault=<name>` when multiple vaults exist or the active vault is unclear
- **"File not found"**: The file name/path doesn't exist. Try using `path=` with the full path if `file=` fails
- **"Obsidian is not running"**: The CLI requires the Obsidian desktop app to be open
- **"Cannot find file"**: Check spelling or use `files` to list available files first

## Slash Commands

When invoked via `/obsidian-cli`, the skill provides general guidance on using the
Obsidian CLI. For specific operations, just describe what you want to do in natural
language — the skill will determine the correct command automatically.
