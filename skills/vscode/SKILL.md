---
name: vscode
description: "Configure and operate VS Code-family IDEs (VS Code, VS Code Insiders, Cursor, VSCodium, Trae, Qoder, CodeBuddy) via CLI and structured JSON files. Handles settings.json (user and project scope), .vscode/{settings,tasks,launch,extensions}.json, keybindings.json, snippets, profiles, extensions, Python interpreter, SSH and WSL Remote. Qoder and CodeBuddy support is limited to their VS Code-compatible configuration surface, not proprietary AI chat, accounts, models, agents, marketplaces, or internal state. Uses environment variables and a config file for portable paths so the skill works on any machine. Trigger phrases: VS Code, VSCode, VS Code 配置, settings.json, .vscode, tasks.json, launch.json, keybindings.json, extensions.json, snippets, profiles, Cursor, VSCodium, Trae, Qoder, CodeBuddy, Remote SSH, WSL, Python interpreter, VSIX, MCP, theme, font."
---

# VS Code

A portable skill for configuring and operating VS Code-family IDEs (VS Code, VS Code Insiders, Cursor, VSCodium, Trae, Qoder, CodeBuddy) through the product CLI and structured JSON config files. Defaults use only standard locations; explicit paths are taken from environment variables and a config file so the skill can run on any machine without editing.

> Platform note: **Cross-platform** via the Python gateway `scripts/vscode_skill.py`. On Windows it forwards to the PowerShell driver `vscode-cli.ps1` (the original implementation, 11/11 tests pass). On macOS and Linux it implements `info`, `ext list`, `settings path/get/set/smoke`, and `python set-interpreter` natively in Python; everything else shells out to your local `code` binary.

## Quick Start

### Cross-platform (recommended)

```bash
# Show detected product, CLI path, and key locations
python scripts/vscode_skill.py info

# List installed extensions
python scripts/vscode_skill.py ext list

# Show user settings.json path and current core settings
python scripts/vscode_skill.py settings path
python scripts/vscode_skill.py settings get

# Change font size in user settings (writes only with --Apply)
python scripts/vscode_skill.py settings set \
    --FontSize 16 --FontFamily "JetBrains Mono, Consolas, monospace" --Apply

# Project-scope settings
python scripts/vscode_skill.py settings set \
    --Scope project --ProjectPath /path/to/project \
    --FormatOnSave true --Apply

# Python interpreter for a project
python scripts/vscode_skill.py python set-interpreter \
    --ProjectPath /path/to/project --VenvName .venv
```

### Windows-only (PowerShell)

The same commands work directly through `vscode-cli.ps1` if you prefer PowerShell:

```powershell
pwsh -File $PSScriptRoot\scripts\vscode-cli.ps1 info
pwsh -File $PSScriptRoot\scripts\vscode-cli.ps1 ssh open `
    --HostName devbox --LinuxPath /home/user/project
```

`--Product` values:

- `auto` (default): probe VS Code, then VS Code Insiders.
- `vscode`: use `code` / `code.cmd`.
- `vscode-insiders`: use `code-insiders` / `code-insiders.cmd`.
- Any configured product slug such as `cursor`, `vscodium`, `trae-cn`, `qoder`, or `codebuddy-cn`: use `products.<slug>.cliPath`, `userDataPath`, and `extensionsPath` from the config file.

Set the default product explicitly with `VSCODE_SKILL_PRODUCT` or via the config file (see [Configuration](#configuration)).

## VS Code-Compatible Products

Built-in auto-detection is strongest for VS Code and VS Code Insiders. Cursor, VSCodium, Trae, Qoder, and CodeBuddy are handled through the generic product configuration path unless their CLI is already discoverable through an environment-specific wrapper.

This skill only claims the VS Code-compatible configuration surface for derived products:

- User and project settings, including `.vscode/settings.json`.
- Project `.vscode/tasks.json`, `.vscode/launch.json`, and `.vscode/extensions.json`.
- Keybindings, snippets, profiles, extensions, templates, Python interpreter selection, and Remote-style open flows where the local product CLI supports them.

Do not use this skill as support for proprietary AI chat, accounts, model settings, agent stores, product-specific marketplaces, hidden SQLite state, tokens, or internal runtime files. For Qoder and CodeBuddy in particular, keep support to the VS Code-compatible editor/configuration layer unless the user provides official product-specific documentation and asks for a separate adapter.

## Configuration

Paths and per-machine preferences are resolved in this order:

1. **Environment variable** (highest priority).
2. **Config file** at `$VSCODE_SKILL_CONFIG` if set, otherwise the platform default:
   - Windows: `%APPDATA%\vscode-skill\config.json`
   - macOS / Linux: `$XDG_CONFIG_HOME/vscode-skill/config.json` or `~/.config/vscode-skill/config.json`
3. **Built-in defaults** (lowest priority).

### Environment Variables

| Variable | Purpose | Default |
|---|---|---|
| `VSCODE_SKILL_HOME` | Skill install location | parent of the running script |
| `VSCODE_SKILL_CONFIG` | Override config file path | platform default above |
| `VSCODE_SKILL_TEMP` | Override temp directory for tests | `$TEMP/vscode-skill` |
| `VSCODE_SKILL_PRODUCT` | Default `--Product` value | `auto` |
| `VSCODE_CODE_CLI` | Explicit path to VS Code CLI | auto-detected |
| `VSCODE_INSIDERS_CLI` | Explicit path to VS Code Insiders CLI | auto-detected |
| `VSCODE_EXTENSIONS_DIR` | Override extension install dir for any product | product default or config |
| `VSCODE_USER_DATA` | Override user data dir (rare) | platform default |

### Config File Schema

Copy `config.example.json` from the skill root to your config location and edit. All keys are optional.

```json
{
  "product": "auto",
  "tempDir": null,
  "products": {
    "vscode": {
      "cliPath": "C:\\Users\\you\\scoop\\apps\\vscode\\current\\bin\\code.cmd"
    },
    "vscode-insiders": {
      "cliPath": "C:\\Users\\you\\scoop\\apps\\vscode-insiders\\current\\bin\\code-insiders.cmd"
    },
    "cursor": {
      "cliPath": "C:\\Users\\you\\AppData\\Local\\Programs\\cursor\\resources\\app\\bin\\cursor.cmd",
      "userDataPath": "C:\\Users\\you\\AppData\\Roaming\\Cursor\\User",
      "extensionsPath": "C:\\Users\\you\\.cursor\\extensions"
    },
    "vscodium": {
      "cliPath": "C:\\Users\\you\\scoop\\apps\\vscodium\\current\\bin\\codium.cmd",
      "userDataPath": "C:\\Users\\you\\AppData\\Roaming\\VSCodium\\User",
      "extensionsPath": "C:\\Users\\you\\.vscode-oss\\extensions"
    },
    "trae-cn": {
      "cliPath": "C:\\Users\\you\\AppData\\Local\\Programs\\Trae CN\\bin\\trae-cn.cmd",
      "userDataPath": "C:\\Users\\you\\AppData\\Roaming\\Trae CN\\User",
      "extensionsPath": "C:\\Users\\you\\.trae-cn\\extensions"
    },
    "qoder": {
      "cliPath": "C:\\Users\\you\\AppData\\Local\\Programs\\Qoder\\bin\\qoder.cmd",
      "userDataPath": "C:\\Users\\you\\AppData\\Roaming\\Qoder\\User",
      "extensionsPath": "C:\\Users\\you\\.qoder\\extensions"
    },
    "codebuddy-cn": {
      "cliPath": "C:\\Users\\you\\AppData\\Local\\Programs\\CodeBuddy CN\\bin\\codebuddy.cmd",
      "userDataPath": "C:\\Users\\you\\AppData\\Roaming\\CodeBuddy CN\\User",
      "extensionsPath": "C:\\Users\\you\\.codebuddycn\\extensions"
    }
  },
  "ssh": {
    "defaultHost": "localhost",
    "defaultUser": "you"
  },
  "wsl": {
    "defaultDistro": "Ubuntu-24.04"
  }
}
```

Run `pwsh -File scripts/init-config.ps1` to write a starter config file in the default location.

## Scope Discipline

Before writing any IDE state, classify it into one of three scopes and confirm with the user when ambiguous:

- **Read-only inspection**: `info`, `ext list`/`locate`, `settings get`/`path`. Always safe.
- **Project configuration**: `.vscode\settings.json`, `tasks.json`, `launch.json`, `extensions.json`, project snippets. Commit-worthy; do not include personal themes, fonts, account info, or machine-local absolute paths.
- **User / global configuration**: user `settings.json`, `keybindings.json`, user snippets, profile settings, installed extensions. Always state target product, file, key, old value (when readable), new value, and rollback path before applying.

Rules:

- `settings set` requires explicit `--Apply`; without it, the command only validates inputs.
- `ext install` calls the product CLI's `--install-extension`. If the gallery fails, the script does **not** silently retry with Open VSX; a clear warning is printed and the caller decides.
- Project settings written via this skill should never include `python.defaultInterpreterPath` pointing at a machine-local venv unless the project is meant to be reproducible on that specific machine.

## Settings Reference

Common user-settings paths:

- VS Code: `%APPDATA%\Code\User\settings.json`
- VS Code Insiders: `%APPDATA%\Code - Insiders\User\settings.json`

Common keys (all settable through `settings set`):

| Key | Flag | Type |
|---|---|---|
| `editor.fontFamily` | `--FontFamily` | string |
| `editor.fontSize` | `--FontSize` | int |
| `editor.lineHeight` | `--LineHeight` | number |
| `workbench.colorTheme` | `--ColorTheme` | string |
| `workbench.iconTheme` | `--IconTheme` | string |
| `workbench.productIconTheme` | `--ProductIconTheme` | string |
| `editor.wordWrap` | `--WordWrap` | string |
| `editor.tabSize` | `--TabSize` | int |
| `editor.formatOnSave` | `--FormatOnSave` | bool |
| `files.autoSave` | `--AutoSave` | string |
| `editor.minimap.enabled` | `--Minimap` | bool |
| `python.defaultInterpreterPath` | (set via `python set-interpreter`) | string |

For arbitrary keys, pass `--SettingKey <key> --SettingValue <value>`. Values are coerced: `true`/`false` → bool, integer/float → number, `{...}` / `[...]` → JSON, otherwise string.

JSON files may use VS Code's JSON-with-Comments style; the script's standard JSON parser handles only pure JSON. Files containing comments should be edited through the editor or a JSONC-aware tool.

## Commands

```powershell
pwsh -File scripts/vscode-cli.ps1 info
pwsh -File scripts/vscode-cli.ps1 ext list
pwsh -File scripts/vscode-cli.ps1 ext locate --Id ms-python.python
pwsh -File scripts/vscode-cli.ps1 ext install --Id ms-python.python
pwsh -File scripts/vscode-cli.ps1 ext install --Path D:\downloads\some-extension.vsix

pwsh -File scripts/vscode-cli.ps1 settings path
pwsh -File scripts/vscode-cli.ps1 settings get
pwsh -File scripts/vscode-cli.ps1 settings set --FontSize 16 --Apply
pwsh -File scripts/vscode-cli.ps1 settings set --Scope project --ProjectPath D:\projects\demo --FormatOnSave true --Apply
pwsh -File scripts/vscode-cli.ps1 settings smoke

pwsh -File scripts/vscode-cli.ps1 python make-venvs --ProjectPath D:\projects\demo
pwsh -File scripts/vscode-cli.ps1 python set-interpreter --ProjectPath D:\projects\demo --VenvName .venv
pwsh -File scripts/vscode-cli.ps1 python verify --ProjectPath D:\projects\demo --ExpectedVenvName .venv

pwsh -File scripts/vscode-cli.ps1 ssh smoke --HostName localhost
pwsh -File scripts/vscode-cli.ps1 ssh open --HostName devbox --LinuxPath /home/user/project
pwsh -File scripts/vscode-cli.ps1 wsl list
pwsh -File scripts/vscode-cli.ps1 wsl open --Distro Ubuntu-24.04 --LinuxPath /home/user/project
```

CLI resolution order: explicit env (`VSCODE_CODE_CLI` / `VSCODE_INSIDERS_CLI`) → `config.products.<product>.cliPath` → `Get-Command code.cmd` (PATH) → `Get-Command code` (PATH) → `%LOCALAPPDATA%\Programs\Microsoft VS Code\bin\code.cmd` (Windows default). Generic products fail clearly when `products.<product>.cliPath` is absent; they are never silently mapped to VS Code.

## Templates and Bundled Content

The skill ships with curated content under `references/`:

* `settings-index.md` — 80 most-used settings with type, default, scope.
* `settings-precedence.md` — 11-layer precedence model + multi-root workspace behavior.
* `tasks-templates.md` + `templates/tasks/*.json` — 10 ready-made `tasks.json` for Node, TypeScript, Python, Go, Rust, Docker, Make.
* `launch-templates.md` + `templates/launch/*.json` — 9 ready-made `launch.json` for the same languages plus Chrome.
* `extension-packs.md` — 8 curated stacks (frontend-web, backend-python, backend-node, data-science, systems, devops, polyglot-baseline, ai-coding).
* `keybindings-cheatsheet.md` — 50 most-remapped shortcuts.

```powershell
# List available tasks templates
python scripts/vscode_skill.py tasks list

# Generate .vscode/tasks.json from a template (refuses to overwrite without --Force)
python scripts/vscode_skill.py tasks init --Template python-pytest --ProjectPath /path/to/project --Apply

# Same shape for launch templates
python scripts/vscode_skill.py launch init --Template python-current-file --ProjectPath /path/to/project --Apply

# Curated extension stacks
python scripts/vscode_skill.py extensions stacks
python scripts/vscode_skill.py extensions recommend --Stack frontend-web
python scripts/vscode_skill.py extensions install --Stack backend-python
python scripts/vscode_skill.py extensions pin --Stack polyglot-baseline --ProjectPath /path/to/project
```

## Profiles, Settings Sync, Multi-root Workspaces

```powershell
# Inspect profiles (read-only)
python scripts/vscode_skill.py profile list
python scripts/vscode_skill.py profile show --Profile <name>

# Check whether settings sync storage exists locally (does not read payloads)
python scripts/vscode_skill.py settings-sync status

# Multi-root workspace helpers
python scripts/vscode_skill.py workspace info --ProjectPath /path/to/project
python scripts/vscode_skill.py workspace folder-settings-get --ProjectPath /path --Folder frontend
python scripts/vscode_skill.py workspace folder-settings-set --ProjectPath /path --Folder frontend --SettingKey editor.defaultFormatter --SettingValue dbaeumer.vscode-eslint --Apply
```

Settings Sync is **never enabled or disabled programmatically** — the skill only reports whether the sync storage folder exists. Enable/disable it via the VS Code Accounts UI to avoid accidental data leaks.

## Remote Development

- `ssh open` builds a `vscode-remote://ssh-remote+<host><path>` URI and launches the resolved CLI with `--folder-uri`.
- `wsl open` builds a `vscode-remote://wsl+<distro><path>` URI similarly.
- `ssh smoke` runs `ssh -V`, `ssh -G <host>`, and `Test-NetConnection` to confirm the lower layer; it does **not** guarantee the Remote-SSH extension is installed or that the VS Code server has started.

For deeper remote troubleshooting, check `Help → Toggle Developer Tools`, the Remote-SSH extension output channel, or the workspaceStorage entry of the relevant product.

## Testing

The bundled `run_vscode_skill_tests.py` runs safe no-write checks by default:

```powershell
python -X utf8 scripts/run_vscode_skill_tests.py --basic
```

Optional groups (require the corresponding environment):

```powershell
python -X utf8 scripts/run_vscode_skill_tests.py --include-python-venv
python -X utf8 scripts/run_vscode_skill_tests.py --clean
```

Tests write temporary artifacts to an isolated subdirectory under `%TEMP%\vscode-skill-tests\` (or `$VSCODE_SKILL_TEMP` if set), never to user settings or project files outside the temp root.

Validation against the Agent Skills spec:

```powershell
python -X utf8 scripts\quick_validate.py .
```

(`quick_validate.py` is the standalone script in the skill-creator reference; clone or vendor it into this skill if you do not have it locally.)

## See Also

- [references/settings-index.md](references/settings-index.md) — curated 80-setting reference.
- [references/settings-precedence.md](references/settings-precedence.md) — 11-layer precedence + multi-root.
- [references/tasks-templates.md](references/tasks-templates.md) — 10 tasks templates.
- [references/launch-templates.md](references/launch-templates.md) — 9 launch templates.
- [references/extension-packs.md](references/extension-packs.md) — 8 curated extension stacks.
- [references/keybindings-cheatsheet.md](references/keybindings-cheatsheet.md) — 50 most-remapped shortcuts.
- [references/vscode-config-files.md](references/vscode-config-files.md) — project-config file formats reference.

## Cleanup

After running tests:

- Delete the temp root (`%TEMP%\vscode-skill-tests\` by default).
- If a settings write was rolled back by `settings smoke`, the original file is restored in-place; no extra cleanup needed.
