# VS Code Settings Precedence

A reference for understanding which setting wins when multiple sources define the same key. Use this when a user reports "I set X but it's still Y" — most "settings not working" issues are caused by a higher-precedence layer overriding the lower one.

## Precedence Layers (low → high)

1. **Default settings** — built into VS Code; not user-visible.
2. **User settings** — `settings.json` in the user data directory.
3. **Remote settings** — `[remoteName]` keyed blocks; active in remote (SSH/WSL/Container) windows.
4. **Workspace settings** — `.vscode/settings.json` (single-root) or `.code-workspace` file (multi-root).
5. **Workspace Folder settings** — multi-root only; targets a specific folder.
6. **Language-specific default settings** — built-in defaults per language ID.
7. **Language-specific user settings** — `"[languageId]": { ... }` block in user `settings.json`.
8. **Language-specific remote settings** — same idea, remote scope.
9. **Language-specific workspace settings** — same idea, workspace scope.
10. **Language-specific workspace folder settings** — multi-root + language combination.
11. **Policy settings** — installed by a system administrator; **always wins**.

## Merge Rules

When the same key appears in multiple layers, two outcomes are possible:

* **Primitive or array types** — entirely replaced by the higher-precedence value.
* **Object types** — merged key-by-key, with higher-precedence values winning on conflicts.

Examples:

```jsonc
// User settings (layer 2)
{
  "files.exclude": {
    "**/.git": true,
    "**/.DS_Store": true
  }
}

// Workspace settings (layer 4)
{
  "files.exclude": {
    "**/node_modules": true  // added
    // **/.git and **/.DS_Store are kept (object merge)
  }
}
```

```jsonc
// User settings
{
  "editor.fontSize": 14  // primitive — entirely replaced below
}

// Workspace settings
{
  "editor.fontSize": 16  // wins
}
```

## Multi-root Workspaces

Multi-root workspaces (`.code-workspace` file or "Save Workspace As...") introduce **Workspace Folder settings**, which apply to a single folder inside the workspace.

```jsonc
// my-project.code-workspace
{
  "folders": [
    { "path": "frontend" },
    { "path": "backend" }
  ],
  "settings": {
    // workspace settings (apply to all folders)
    "editor.formatOnSave": true
  },
  "extensions": {
    "recommendations": ["dbaeumer.vscode-eslint"]
  }
}
```

For per-folder overrides, use the **folder-scoped** settings editor (right-click a folder in Explorer → "Settings"). These are stored as folder-scoped entries in the `.code-workspace` file:

```jsonc
{
  "folders": [
    { "path": "frontend", "settings": { "editor.defaultFormatter": "dbaeumer.vscode-eslint" } },
    { "path": "backend",  "settings": { "editor.defaultFormatter": "ms-python.black-formatter" } }
  ]
}
```

## Language-Specific Scopes

A block like `"[python]": { ... }` is itself a key in the JSON, but its precedence follows the language-specific layer of its parent scope. Combined scopes:

```jsonc
{
  "[javascript][typescript]": { ... }   // applies to both JS and TS (full string match)
  "[jsonc]": { ... }                    // JSON with comments
}
```

The scope string is matched **as a whole string**, not per-language. `"[javascript][typescript]"` does **not** apply to plain JavaScript or plain TypeScript in isolation — VS Code matches the full string against the file's current language scope.

## User-only Settings (Security)

Some settings are restricted to user scope and cannot be set in workspace or workspace-folder layers. These are typically:

* Executable paths (`terminal.external.*Exec`, `git.path`, `python.pythonPath` since v2024)
* Trust-related settings (`security.*`)
* Privacy and telemetry settings (`telemetry.*`)
* Authentication-related settings

If a workspace-scoped setting is silently ignored, check the live docs for the user-only designation.

## Policy Settings (Layer 11)

System administrators can install policies via:

* Windows: registry keys under `HKLM\Software\Policies\Microsoft\VisualStudio\...`
* macOS: managed preferences via MDM profiles
* Linux: `/etc/vscode/policies/` JSON files

Policies always win. If a user reports that they cannot change a setting, verify that no policy is in effect before debugging the precedence chain.

## Debugging Precedence Issues

1. Open **Settings** (Ctrl+,) and search for the key.
2. Note the scope dropdown next to the setting — VS Code shows which layer is currently winning.
3. Right-click a setting → "Modified Elsewhere" shows all layers that set this key.
4. Use `Developer: Inspect Editor Tokens and Scopes` (Ctrl+Shift+P) for language-scope debugging.

## Settings Sync

Settings Sync shares user-scope settings, keybindings, and installed extensions across machines. It does **not** sync:

* Workspace-scoped settings (these stay per-machine)
* Profiles
* Remote-specific settings
* Extensions installed in remote (SSH/WSL) windows

When the same key has been edited on multiple machines between syncs, the most-recent edit wins.

## See Also

* [settings-index.md](settings-index.md) — the curated ~80-setting reference.
* [extension-packs.md](extension-packs.md) — recommended extension bundles.
* [keybindings-cheatsheet.md](keybindings-cheatsheet.md) — keyboard shortcut customization.
* Live docs: <https://code.visualstudio.com/docs/getstarted/settings#_settings-precedence>