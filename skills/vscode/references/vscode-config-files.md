# VS Code-Compatible Configuration Files

This reference covers the shared configuration model used by VS Code-family editors. It applies directly to VS Code and VS Code Insiders, and conditionally to derived or compatible products such as Cursor, VSCodium, Trae, Qoder, and CodeBuddy when their local CLI and data paths are configured.

Official VS Code references:

- Settings: https://code.visualstudio.com/docs/configure/settings
- Command line: https://code.visualstudio.com/docs/configure/command-line
- Keybindings: https://code.visualstudio.com/docs/configure/keybindings
- Tasks: https://code.visualstudio.com/docs/debugtest/tasks
- Launch config: https://code.visualstudio.com/docs/debugtest/debugging-configuration
- Snippets: https://code.visualstudio.com/docs/editing/userdefinedsnippets
- Variables: https://code.visualstudio.com/docs/reference/variables-reference
- Profiles: https://code.visualstudio.com/docs/configure/profiles

## Product Matrix

| Product slug | Typical CLI | User settings path on Windows | Extension path on Windows | Support level |
|---|---|---|---|---|
| `vscode` | `code` / `code.cmd` | `%APPDATA%\Code\User\settings.json` | `%USERPROFILE%\.vscode\extensions` | Built-in auto-detection. |
| `vscode-insiders` | `code-insiders` / `code-insiders.cmd` | `%APPDATA%\Code - Insiders\User\settings.json` | `%USERPROFILE%\.vscode-insiders\extensions` | Built-in auto-detection. |
| `cursor` | `cursor` / `cursor.cmd` | `%APPDATA%\Cursor\User\settings.json` | `%USERPROFILE%\.cursor\extensions` | Configure through `products.cursor.*`; CLI may already be on PATH. |
| `vscodium` | `codium` / `codium.cmd` | `%APPDATA%\VSCodium\User\settings.json` | `%USERPROFILE%\.vscode-oss\extensions` | Configure through `products.vscodium.*`. |
| `trae-cn` | `trae-cn.cmd` or product-specific launcher | `%APPDATA%\Trae CN\User\settings.json` | `%USERPROFILE%\.trae-cn\extensions` | VS Code-compatible config only unless a separate Trae adapter is documented. |
| `qoder` | `qoder` / `qoder.cmd` when installed | `%APPDATA%\Qoder\User\settings.json` | `%USERPROFILE%\.qoder\extensions` | Config-only example; proprietary AI features are out of scope. |
| `codebuddy-cn` | `codebuddy` / `codebuddy.cmd` when installed | `%APPDATA%\CodeBuddy CN\User\settings.json` | `%USERPROFILE%\.codebuddycn\extensions` | Config-only example; proprietary AI features and marketplace state are out of scope. |

For any slug other than `vscode` and `vscode-insiders`, set at least:

```json
{
  "products": {
    "codebuddy-cn": {
      "cliPath": "C:\\Users\\you\\AppData\\Local\\Programs\\CodeBuddy CN\\bin\\codebuddy.cmd",
      "userDataPath": "C:\\Users\\you\\AppData\\Roaming\\CodeBuddy CN\\User",
      "extensionsPath": "C:\\Users\\you\\.codebuddycn\\extensions"
    }
  }
}
```

Generic products intentionally fail when `cliPath` is missing. Do not silently map Qoder, CodeBuddy, Trae, Cursor, or VSCodium to the normal VS Code CLI; that would modify or inspect the wrong product.

## Scope Layers

Common settings precedence from broad to specific:

- Default settings: product-provided, not edited directly.
- User settings: current user across windows.
- Profile settings: current profile.
- Workspace or project settings: usually `.vscode/settings.json`.
- Language-specific settings such as `[python]` and `[markdown]`.

Use user settings for personal preferences such as fonts, themes, and window behavior. Use project settings for shared formatter, linter, test, language-server, and file-exclude rules. Do not commit machine-local absolute paths, accounts, tokens, private servers, or temporary directories unless the repository is explicitly a single-machine workspace.

## Project `.vscode` Files

`.vscode/settings.json`

- Stores project-level editor and extension settings.
- Good for formatter, lint, type checking, tests, language tools, and file exclusions.
- Bad for personal themes, fonts, machine paths, account state, or secrets.

`.vscode/launch.json`

- Stores debugger configurations.
- Common fields: `name`, `type`, `request`, `program`, `args`, `cwd`, `env`, `preLaunchTask`.
- Do not place real secrets in `env`; reference environment variables or local untracked files.

`.vscode/tasks.json`

- Stores build, test, script, and external-command tasks.
- Common fields: `label`, `type`, `command`, `args`, `group`, `problemMatcher`, `dependsOn`.
- `launch.json` can call tasks through `preLaunchTask`.

`.vscode/extensions.json`

- Stores recommended and unwanted extensions.
- Recommendations are advisory and do not imply automatic installation.

## Common Settings Keys

- `editor.fontFamily`: editor font.
- `editor.fontSize`: font size.
- `editor.lineHeight`: line height.
- `editor.wordWrap`: wrapping mode, such as `on`, `off`, `wordWrapColumn`, or `bounded`.
- `editor.tabSize`: tab width.
- `editor.formatOnSave`: format on save.
- `editor.defaultFormatter`: default formatter extension.
- `files.autoSave`: auto save mode, such as `off`, `afterDelay`, `onFocusChange`, or `onWindowChange`.
- `files.exclude`: Explorer hide rules.
- `search.exclude`: Search exclude rules.
- `workbench.colorTheme`: color theme.
- `workbench.iconTheme`: file icon theme.
- `workbench.productIconTheme`: product icon theme.
- `terminal.integrated.defaultProfile.windows`: Windows terminal profile.
- `python.defaultInterpreterPath`: Python extension default interpreter.

## Variables

`tasks.json` and `launch.json` commonly use:

- `${workspaceFolder}`: current workspace root.
- `${file}`: active file absolute path.
- `${fileBasename}`: active file name.
- `${relativeFile}`: active file path relative to workspace.
- `${env:NAME}`: environment variable.
- `${config:KEY}`: VS Code setting value.
- `${command:COMMAND_ID}`: command result.

Variables reduce absolute paths but do not remove security requirements. Secrets should still come from environment variables or local private files.

## JSON Notes

VS Code settings often use JSON with Comments, including comments and trailing commas. PowerShell `ConvertFrom-Json` and Python's standard JSON parser only handle strict JSON. Before automated edits, confirm the file is strict JSON or use a JSONC-aware tool.

When modifying settings:

- Preserve unrelated keys.
- Do not rewrite unknown objects as empty objects.
- Read, modify, and write only the intended target.
- Verify target keys after writing.

## Product Boundaries

VS Code-compatible products may share `.vscode` project configuration while using different command names, user data paths, extension roots, and remote server folders.

- Keep this skill on the editor/configuration layer.
- Treat product-specific AI chats, agents, accounts, models, proprietary marketplaces, local databases, tokens, and cache/state files as out of scope.
- Add a separate adapter only when the user provides official product-specific documentation and explicitly asks for that product's private surface.
