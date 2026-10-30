# VS Code Settings Index

A curated reference of the ~80 most-used VS Code settings, grouped by area. Use this index when an agent or user asks "which key controls X" or wants to batch-edit a category.

For the full list (~1000+ settings), see the live documentation at <https://code.visualstudio.com/docs/getstarted/settings>.

## How to Use

* Each entry lists the **key**, **default value**, **type**, and a one-line description.
* `scope` tells you whether the setting is allowed in user-scope, workspace-scope, or both. Some settings are user-only for security reasons (e.g., `terminal.external.*Exec`).
* When the skill needs to **change** a setting, prefer the `settings set` command over hand-editing JSON, so the write is auditable and reversible.
* When a key is not in this index, search the live docs: <https://code.visualstudio.com/search?settings=1>.

## Editor — Appearance

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `editor.fontFamily` | platform default | string | user | Font family for the editor. |
| `editor.fontSize` | 14 | int | both | Font size in pixels. |
| `editor.fontLigatures` | false | bool | both | Enable font ligatures. |
| `editor.fontWeight` | "normal" | string | both | "normal" or "bold" or a number 1-1000. |
| `editor.lineHeight` | 0 | number | both | Line height in px; 0 = auto. |
| `editor.letterSpacing` | 0 | number | both | Letter spacing in px. |
| `editor.cursorStyle` | "line" | enum | both | line / block / underline / line-thin / block-outline / underline-thin. |
| `editor.cursorBlinking` | "blink" | enum | both | blink / smooth / phase / expand / solid. |
| `editor.cursorWidth` | 0 | int | both | Cursor width in px; 0 = auto. |
| `editor.renderWhitespace` | "selection" | enum | both | none / boundary / selection / all / trailing. |
| `editor.renderLineHighlight` | "all" | enum | both | none / gutter / line / all. |
| `editor.renderControlCharacters` | false | bool | both | Show control characters. |
| `editor.wordWrap` | "off" | enum | both | off / on / wordWrapColumn / bounded. |
| `editor.wordWrapColumn` | 80 | int | both | Column for wordWrapColumn/bounded. |
| `editor.minimap.enabled` | true | bool | both | Show minimap. |
| `editor.minimap.maxColumn` | 120 | int | both | Minimap width in columns. |
| `editor.minimap.renderCharacters` | true | bool | both | Render actual characters on minimap. |
| `editor.overviewRulerBorder` | true | bool | both | Border around overview ruler. |
| `editor.scrollBeyondLastLine` | true | bool | both | Allow scrolling past the last line. |
| `editor.smoothScrolling` | false | bool | both | Animate scrolling. |
| `editor.mouseWheelZoom` | false | bool | both | Ctrl + wheel zooms font size. |
| `editor.tabSize` | 4 | int | both | Tab size in spaces. |
| `editor.insertSpaces` | true | bool | both | Insert spaces when pressing Tab. |
| `editor.detectIndentation` | true | bool | user | Auto-detect indentation on file open. |
| `editor.formatOnSave` | false | bool | both | Run formatter on save. |
| `editor.formatOnPaste` | false | bool | both | Run formatter on paste. |
| `editor.formatOnType` | false | bool | both | Run formatter while typing. |
| `editor.defaultFormatter` | null | string | both | Default formatter ID. |
| `editor.codeActionsOnSave` | {} | object | both | Run code actions on save (e.g. organize imports). |
| `editor.bracketPairColorization.enabled` | false | bool | both | Colorize matching brackets. |
| `editor.guides.bracketPairs` | "active" | enum | both | active / always / false. |
| `editor.stickyScroll.enabled` | false | bool | both | Show sticky scroll header. |
| `editor.inlineSuggest.enabled` | true | bool | both | Show inline suggestions. |

## Editor — Behavior

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `editor.acceptSuggestionOnCommitCharacter` | true | bool | both | Accept suggestion on commit character. |
| `editor.acceptSuggestionOnEnter` | "on" | enum | both | on / smart / off. |
| `editor.suggestSelection` | "first" | enum | both | first / recentlyUsed / values. |
| `editor.snippetSuggestions` | "inline" | enum | both | top / bottom / inline / none. |
| `editor.tabCompletion` | "off" | enum | both | on / off / onlySnippets. |
| `editor.quickSuggestions` | {"other": true, "comments": false, "strings": false} | object | both | When to show quick suggestions. |
| `editor.parameterHints.enabled` | true | bool | both | Show parameter hints. |
| `editor.hover.enabled` | true | bool | both | Show hover. |
| `editor.lightbulb.enabled` | true | bool | both | Show code action lightbulb. |
| `editor.foldingStrategy` | "auto" | enum | both | auto / indentation / languageDefined. |
| `editor.showFoldingControls` | "mouseover" | enum | both | always / never / mouseover. |
| `editor.gotoLocation.multiple` | "alt" | enum | both | Default modifier for multi-cursor goto. |
| `editor.multiCursorModifier` | "alt" | enum | both | Modifier for adding cursors. |
| `editor.accessibilitySupport` | "auto" | enum | both | auto / on / off. |

## Files

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `files.autoSave` | "off" | enum | both | off / afterDelay / onFocusChange / onWindowChange. |
| `files.autoSaveDelay` | 1000 | int | both | Delay in ms for autoSave "afterDelay". |
| `files.encoding` | "utf8" | string | both | Default encoding. |
| `files.eol` | "\n" | enum | both | Default EOL: "\n" or "\r\n" or "auto". |
| `files.trimTrailingWhitespace` | false | bool | both | Trim trailing whitespace on save. |
| `files.insertFinalNewline` | false | bool | both | Insert final newline on save. |
| `files.trimFinalNewlines` | false | bool | both | Trim final newlines on save. |
| `files.exclude` | { ... } | object | both | Glob patterns to hide from explorer. |
| `files.watcherExclude` | { ... } | object | both | Globs to exclude from file watcher. |
| `files.associations` | {} | object | both | Map file extension to language ID. |
| `files.defaultLanguage` | null | string | both | Default language for untitled files. |

## Workbench

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `workbench.colorTheme` | "Default Dark+" | string | user | UI theme. |
| `workbench.iconTheme` | "vs-seti" | string | user | File icon theme. |
| `workbench.productIconTheme` | "Default" | string | user | Product icon theme. |
| `workbench.editor.enablePreview` | true | bool | user | Open files in preview mode. |
| `workbench.editor.preferHistoryBasedLanguageAssociations` | true | bool | user | Pick language based on history. |
| `workbench.editor.restoreViewState` | true | bool | user | Restore editor view state on reopen. |
| `workbench.startupEditor` | "welcomePage" | enum | user | none / welcomePage / readme / newUntitledFile / welcomePageInEmptyWorkbench / terminal. |
| `workbench.layoutControl.enabled` | true | bool | user | Show layout control in title bar. |
| `workbench.secondarySideBar.defaultVisibility` | "hidden" | enum | user | hidden / visible / maximized. |
| `workbench.panel.defaultLocation` | "bottom" | enum | user | bottom / left / right / top. |
| `workbench.sideBar.location` | "left" | enum | user | left / right. |
| `workbench.statusBar.visible` | true | bool | user | Show status bar. |
| `workbench.activityBar.visible` | true | bool | user | Show activity bar. |
| `workbench.tips.enabled` | true | bool | user | Show tips on startup. |
| `workbench.settings.editor` | "ui" | enum | user | ui / json. |
| `workbench.settings.enableNaturalLanguageSearch` | true | bool | user | Use natural language in settings search. |
| `workbench.commandPalette.history` | 50 | int | user | Number of recent commands to keep. |
| `workbench.fontAliasing` | "default" | enum | user | default / antialiased / none / grayscale. |

## Window

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `window.title` | "${dirty}${activeEditorShort}${separator}${rootName}" | string | both | Title bar format. |
| `window.titleBarStyle` | platform default | enum | user | native / custom / tabs. |
| `window.openFilesInNewWindow` | "off" | enum | user | on / off / default. |
| `window.dialogStyle` | "native" | enum | user | native / custom. |
| `window.restoreFullscreen` | false | bool | user | Restore fullscreen state. |
| `window.zoomLevel` | 0 | number | user | Zoom level. |
| `window.autoDetectColorScheme` | true | bool | user | Auto-switch light/dark based on OS. |
| `window.systemColorTheme` | "auto" | enum | user | auto / default / light / dark. |

## Terminal

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `terminal.integrated.defaultProfile.windows` | platform default | string | user | Default terminal profile on Windows. |
| `terminal.integrated.defaultProfile.linux` | platform default | string | user | Default terminal profile on Linux. |
| `terminal.integrated.defaultProfile.osx` | platform default | string | user | Default terminal profile on macOS. |
| `terminal.integrated.fontFamily` | platform default | string | both | Terminal font. |
| `terminal.integrated.fontSize` | platform default | int | both | Terminal font size. |
| `terminal.integrated.lineHeight` | 1.0 | number | both | Terminal line height multiplier. |
| `terminal.integrated.cursorStyle` | "block" | enum | both | block / underline / line. |
| `terminal.integrated.cursorBlinking` | false | bool | both | Cursor blinking. |
| `terminal.integrated.scrollback` | 1000 | int | both | Scrollback lines. |
| `terminal.integrated.copyOnSelection` | false | bool | both | Copy to clipboard on selection. |
| `terminal.integrated.enableFileLinks` | "on" | enum | both | on / off / onDetect. |
| `terminal.integrated.gpuAcceleration` | "auto" | enum | both | auto / on / off. |
| `terminal.integrated.shellIntegration.enabled` | true | bool | both | Enable shell integration. |
| `terminal.external.windowsExec` | null | string | user | External terminal binary (user-only for security). |

## Source Control

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `git.enabled` | true | bool | user | Enable Git. |
| `git.path` | null | string | user | Git binary path. |
| `git.autofetch` | false | bool | both | Auto-fetch from remotes. |
| `git.autofetchPeriod` | 180 | int | both | Autofetch period in seconds. |
| `git.confirmSync` | true | bool | user | Confirm before sync. |
| `git.enableSmartCommit` | true | bool | both | Commit all without explicit stage. |
| `git.smartCommitChanges` | "all" | enum | both | all / tracked. |
| `git.inputValidationSubjectLength` | 72 | int | user | Subject line max length. |
| `git.branchSortOrder` | "committerdate" | enum | user | Sort branches by. |
| `scm.diffDecorations` | "all" | enum | both | Diff gutter decorations: all / gutter / overview / minimap / none. |

## Extensions

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `extensions.supportUntrustedWorkspaces` | {} | object | user | Per-extension untrusted workspace support. |
| `extensions.webWorkers` | true | bool | user | Run extensions in web workers. |
| `extensions.checkForProposedApi` | false | bool | user | Show proposed API warnings. |

## Security

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `security.workspace.trust.enabled` | true | bool | user | Enable workspace trust. |
| `security.workspace.trust.startupPrompt` | "oneOnDomainMismatch" | enum | user | always / oneOnDomainMismatch / never. |
| `security.workspace.trust.emptyWindow` | true | bool | user | Trust empty windows by default. |
| `security.workspace.trust.untrustedFiles` | "prompt" | enum | user | prompt / open / silent. |
| `security.workspace.trust.banner` | "show" | enum | user | show / alwaysShow / never. |

## Search

| Key | Default | Type | Scope | Description |
|---|---|---|---|---|
| `search.exclude` | { ... } | object | both | Exclude patterns from search. |
| `search.useGlobalIgnoreFiles` | false | bool | both | Use .gitignore. |
| `search.followSymlinks` | true | bool | both | Follow symlinks. |
| `search.smartCase` | false | bool | both | Smart case search. |
| `search.globalFindClipboard` | false | bool | user | Global find uses clipboard. |
| `search.showLineNumbers` | true | bool | both | Show line numbers in results. |

## Notes on Coverage Gaps

The above is a curated subset. Settings that did not fit here but may matter for specific workflows:

* **Language-specific settings** — language IDs prefix the key (e.g., `typescript.preferences.importModuleSpecifier`, `[python] { ... }` in settings.json).
* **Per-extension settings** — the extension marketplace shows them in the extension's detail page.
* **Telemetry and privacy** — `telemetry.telemetryLevel` and related settings change frequently; check the live docs.

For the **canonical, always-current** list, use <https://code.visualstudio.com/docs/getstarted/settings> as the live source.