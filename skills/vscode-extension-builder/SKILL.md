---
name: vscode-extension-builder
description: Use this skill whenever the user asks to create, scaffold, build, or generate a VS Code extension or Visual Studio Code extension — e.g. "Create a VSCode extension", "Create a Visual Studio Code extension", "build me a vscode extension that does X", "make a VS Code plugin/theme/snippet extension". Fully automates scaffolding, npm dependency installation, TypeScript compiling, packaging with vsce, and local installation into the user's VS Code — the user never installs any package or tool by hand. Also covers publishing an already-built extension to the VS Code Marketplace when explicitly asked.
license: Complete terms in LICENSE.txt
---

# VS Code Extension Builder

Builds a working, installed VS Code extension end-to-end from a single user
request. The user should never be told to run `npm install`, install `yo`,
`generator-code`, or `vsce` themselves — you do all of it.

## Workflow

### 1. Understand what to build

If the user only said "create a VS Code extension" with no detail, ask ONE
concise question about what the extension should actually do (e.g. a command
it runs, a theme, a snippet pack, a webview panel). Don't ask about
scaffolding mechanics (TypeScript vs JS, folder structure, etc.) — you decide
those. Infer sensible defaults for name/publisher if the user doesn't care:
- `name`: kebab-case slug derived from what it does
- `displayName`: Title Case of the name
- `publisher`: `local-dev` (fine for local install; real publisher id only
  matters if they later want to publish to the Marketplace)

Pick an extension `type` for scaffolding purposes:
- `command` (default) — contributes one or more commands, runs TS logic.
  Use this for anything behavioral (formatting, automation, panels, status
  bar items, etc.) — see `reference/contribution-points.md` for how to wire
  up webviews, menus, keybindings, status bar items, workspace/file watchers,
  etc. inside the same scaffold.
- `theme` — a color theme.
- `snippets` — a snippet pack for one or more languages.

### 2. Check prerequisites (don't skip)

Run these checks yourself; don't ask the user to run them:

```bash
node --version
npm --version
```

If either is missing, Node.js itself is a system-level install — tell the
user and ask before installing it system-wide (e.g. via `winget install
OpenJS.NodeJS.LTS`, `brew install node`, or `apt install nodejs npm`
depending on OS). Everything downstream of this (npm installs inside the new
project folder, `npx vsce`, etc.) is project-local and reversible, so do NOT
ask permission for those — just run them.

Also check for the `code` CLI, needed later to auto-install the built
extension:

```bash
code --version
```

If it's missing, don't block — note it and fall back to giving the user the
`.vsix` path at the end (see step 7).

### 3. Scaffold the project

Pick an output directory (default: a new folder named `<name>` in the
current workspace/working directory, unless the user specified one). Run the
bundled generator — it writes all boilerplate deterministically so you don't
hand-author it from scratch each time:

```bash
node scripts/create-extension.js \
  --name "<kebab-case-name>" \
  --displayName "<Title Case Name>" \
  --description "<one-line description>" \
  --publisher "<publisher-id-or-local-dev>" \
  --type "command|theme|snippets" \
  --dir "<absolute-output-dir>"
```

This generates `package.json`, `tsconfig.json` (for `command` type),
`.vscodeignore`, `.gitignore`, `.vscode/launch.json`, `.vscode/tasks.json`,
`README.md`, `CHANGELOG.md`, `LICENSE`, and a starter source file
(`src/extension.ts` for `command`, a theme JSON for `theme`, a snippets JSON
for `snippets`).

### 4. Implement the actual feature

The generator only produces a minimal skeleton (for `command` type: one
`helloWorld` command). Now edit the generated files to implement what the
user actually asked for:
- `command` type: edit `src/extension.ts` and the `contributes` /
  `activationEvents` sections of `package.json`. Consult
  `reference/contribution-points.md` for the right contribution point
  (commands, menus, keybindings, webviews, status bar, tree views,
  configuration settings, file watchers, etc.) and wire it up properly —
  don't leave the placeholder `helloWorld` command unless the user actually
  wanted a hello-world extension.
- `theme` type: edit the generated theme JSON's `colors`/`tokenColors` to
  match what was requested.
- `snippets` type: edit the generated snippets JSON with the actual
  snippets, and set `contributes.snippets[].language` correctly in
  `package.json`.

### 5. Install dependencies and compile

From inside the generated project directory:

```bash
npm install
```

For `command` type only, compile to catch errors early:

```bash
npm run compile
```

Fix any TypeScript errors before moving on.

### 6. Package with vsce (no global install)

Use `npx` so nothing is installed globally on the user's machine:

```bash
npx --yes @vscode/vsce package --allow-missing-repository
```

This produces `<name>-<version>.vsix` in the project root. If it fails
because of missing `publisher`/`engines.vscode` fields, fix `package.json`
(the generator already sets these, so this should only happen if you edited
them incorrectly).

### 7. Install the extension into the user's VS Code automatically

```bash
code --install-extension "<name>-<version>.vsix"
```

If `code` wasn't on PATH in step 2, try common install locations before
giving up:
- Windows: `%LOCALAPPDATA%\Programs\Microsoft VS Code\bin\code.cmd`, or
  `C:\Program Files\Microsoft VS Code\bin\code.cmd`
- macOS: `/usr/local/bin/code`, or
  `/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code`
- Linux: `/usr/bin/code`, or `/usr/share/code/bin/code`

If none of those work, tell the user the exact `.vsix` path and that they
can install it via VS Code's Extensions view → "…" menu → "Install from
VSIX…", or run `code --install-extension <path>` themselves once `code` is
on PATH (Command Palette → "Shell Command: Install 'code' command in PATH").

### 8. Wrap up

Tell the user:
- The extension is installed; they should reload VS Code
  (Command Palette → "Developer: Reload Window") to activate it.
- For active development/debugging, open the generated folder in VS Code and
  press F5 to launch an Extension Development Host — this is already wired
  up via `.vscode/launch.json` and `.vscode/tasks.json`.
- Where the project lives on disk, and the command/feature entry point they
  asked for.

## Publishing to the Marketplace (only if explicitly requested)

Do NOT attempt this as part of a normal "create an extension" request — it
requires the user's own Azure DevOps account and Personal Access Token,
which you cannot create or obtain on their behalf. Only walk through
`reference/publishing.md` if the user explicitly asks to publish to the
Marketplace, and always have them provide/paste their own PAT interactively
rather than storing it anywhere.
