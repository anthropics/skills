---
name: baoyu-electron-extract
description: Extracts resources and JavaScript from any installed Electron app (`.asar` bundle), restoring original sources from `.js.map` files when available or formatting minified code with Prettier otherwise. Use when user wants to "extract Electron app", "decompile Electron", "get the source code of <app>", "inspect app.asar", "看 Electron 应用源码", "提取 .asar", or asks how a desktop Electron app is built. Skips `node_modules` and supports both macOS and Windows.
version: 1.119.0
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-electron-extract
    requires:
      anyBins:
        - bun
        - npx
---

# Electron App Extract

Extracts resources and code from an installed Electron app's `app.asar`. When a `.js.map` is present, restores the original source files from the embedded `sourcesContent`; otherwise formats the minified code with Prettier. Source-map paths are resolved relative to the `.js.map` file first, so bundled paths like `../../src/main.ts` restore to readable paths such as `restored/src/main.ts` instead of hashed placeholders. Always skips `node_modules`. Works on macOS and Windows.

## User Input Tools

When this skill prompts the user, follow this tool-selection rule (priority order):

1. **Prefer built-in user-input tools** exposed by the current agent runtime — e.g., `AskUserQuestion`, `request_user_input`, `clarify`, `ask_user`, or any equivalent.
2. **Fallback**: if no such tool exists, emit a numbered plain-text message and ask the user to reply with the chosen number/answer for each question.
3. **Batching**: if the tool supports multiple questions per call, combine all applicable questions into a single call; if only single-question, ask them one at a time in priority order.

Concrete `AskUserQuestion` references below are examples — substitute the local equivalent in other runtimes.

## Script Directory

Scripts in `scripts/` subdirectory. `{baseDir}` = this SKILL.md's directory path. Resolve `${BUN_X}` runtime: if `bun` installed → `bun`; if `npx` available → `npx -y bun`; else suggest installing bun. Replace `{baseDir}` and `${BUN_X}` with actual values.

| Script            | Purpose                                                                        |
| ----------------- | ------------------------------------------------------------------------------ |
| `scripts/main.ts` | App discovery + asar extraction + source-map restoration + Prettier formatting |

## When to use

Use this skill whenever the user wants to look inside an installed Electron application or inspect its bundled code. Trigger phrases include:

- "extract Electron app", "decompile this Electron app", "unpack app.asar"
- "show me the source of <app>", "look inside <app>", "how is <app> built"
- "get the source code of Codex / Cursor / Discord / Slack / VS Code / Notion / Obsidian / ChatGPT desktop"
- "提取 Electron 应用", "看 <app> 的源码", "反编译 Electron", "解包 app.asar", "还原 source map"

Both **app name** (e.g., `Codex`) and **absolute path** (e.g., `/Applications/Codex.app`, a `.asar` file, or a Windows install dir) are accepted. The script handles discovery for both platforms.

## Workflow

**1. Determine the input.** Ask the user for the app name or path if they haven't given one. If they want a custom output directory, ask for that too.

**2. Run the script.**

```bash
${BUN_X} {baseDir}/scripts/main.ts "<app>" [--output <dir>] [--asar <path>] [--force]
```

Start with `--dry-run` first if you're unsure whether discovery will find the right bundle — it prints the resolved paths and exits without touching the filesystem.

**3. Handle the result.**

- **Success** → report the output paths and the counts (extracted / restored / formatted).
- **Multiple matches** → the script lists candidates and exits non-zero. Show the user the candidates, ask which one to use (via `AskUserQuestion` or the runtime equivalent), then re-run with the chosen absolute path.
- **Existing non-empty output dir** → the script refuses without `--force`. Ask the user whether to overwrite (`--force`) or pick a new `--output` path.
- **Unsupported platform / no match** → suggest passing `--asar /full/path/to/app.asar` if the user knows where the bundle lives.

**4. Point the user at the result.** The default output dir is `~/Downloads/<AppName>-electron-extract/`. The most interesting subdirectory depends on what was found:

- `restored/` exists → the original source tree was reconstructed from `.js.map` files; this is what to read first.
- Only `extracted/` exists (no maps) → the JS/CSS in `extracted/` was Prettier-formatted in place; read from there.

## Source-map path restoration

The script should preserve original source names and directory structure as much as the source map allows:

- Resolve each `sources[]` entry with `sourceRoot` when present, then relative to the `.js.map` file's directory inside `extracted/`.
- Collapse normal bundler-relative paths into the restored project tree. For example, `.vite/main/index.js.map` + `../../src/main.ts` becomes `restored/src/main.ts`.
- If a source path climbs above `extracted/`, keep the readable remaining path under `restored/` instead of hashing it. For example, `.vite/main/index.js.map` + `../../../shared/src/lib/foo.ts` becomes `restored/shared/src/lib/foo.ts`.
- Strip URL/query decorations from source names, including common `webpack://`, `file://`, and `?loader` suffixes.
- Use `restored/__unknown/<hash>.<ext>` only when the source name is empty or cannot be reduced to a safe file path.
- Continue skipping `node_modules` and `webpack/runtime/*` entries; these are bundler/runtime noise, not app sources.

## Usage

```bash
# Extract by app name (default output: ~/Downloads/Codex-electron-extract/)
${BUN_X} {baseDir}/scripts/main.ts Codex

# Extract by absolute path (works for .app bundles, install dirs, or .asar files)
${BUN_X} {baseDir}/scripts/main.ts "/Applications/Visual Studio Code.app"
${BUN_X} {baseDir}/scripts/main.ts "C:\Users\you\AppData\Local\Programs\codex"
${BUN_X} {baseDir}/scripts/main.ts --asar /Applications/Codex.app/Contents/Resources/app.asar Codex

# Custom output
${BUN_X} {baseDir}/scripts/main.ts Codex --output ~/work/codex-source

# Preview discovery without writing anything
${BUN_X} {baseDir}/scripts/main.ts Codex --dry-run

# Overwrite an existing output dir
${BUN_X} {baseDir}/scripts/main.ts Codex --force

# Machine-readable result (one JSON line on stdout)
${BUN_X} {baseDir}/scripts/main.ts Codex --json
```

## Options

| Option           | Short | Description                                                     | Default                                  |
| ---------------- | ----- | --------------------------------------------------------------- | ---------------------------------------- |
| `<app>`          |       | App name or absolute path. Required unless `--asar` is given.   | —                                        |
| `--output`       | `-o`  | Output directory                                                | `~/Downloads/<AppName>-electron-extract` |
| `--asar`         |       | Override the resolved `.asar` path                              | auto-discovered                          |
| `--force`        | `-f`  | Allow writing into a non-empty existing output dir              | false                                    |
| `--skip-format`  |       | Skip Prettier formatting                                        | false                                    |
| `--skip-restore` |       | Skip source-map restoration                                     | false                                    |
| `--no-unpacked`  |       | Don't copy `app.asar.unpacked/` alongside                       | false                                    |
| `--dry-run`      |       | Print resolved paths and exit without writing                   | false                                    |
| `--json`         |       | Emit one JSON-line summary on stdout (suppresses normal output) | false                                    |

## Output layout

```
~/Downloads/<AppName>-electron-extract/
├── extract-report.json          # JSON summary: counts, warnings, resolved paths
├── extracted/                   # raw asar contents (JS/CSS Prettier-formatted when no map)
│   └── ...                      # node_modules left untouched (skipped from format)
├── extracted.unpacked/          # copied from <asar>.unpacked/ if present
│   └── ...                      # native modules (.node), large assets
└── restored/                    # only present if at least one .js.map was usable
    └── <original/source/tree>   # rebuilt from sourcesContent in each .js.map
```

## Notes

- **node_modules** is always skipped — both for source-map restoration and Prettier formatting — because vendored dependencies are noise when inspecting an app.
- **Source-map restoration** only works when the `.js.map` embeds `sourcesContent`. This is the common case for modern bundlers (webpack, esbuild, Vite, rollup). If a map references external `.ts`/`.js` files without embedding them, that map is skipped and the corresponding `.js` is Prettier-formatted instead. Skipped maps are listed in `extract-report.json` under `warnings`.
- **Readable paths over hashes** — don't treat `../` segments in source-map paths as automatically unsafe. First resolve them from the map location and then sanitize the final output path so it still stays under `restored/`. Hash fallback is only for unusable source names.
- **App discovery** searches `/Applications` + `~/Applications` on macOS, and `%LOCALAPPDATA%\Programs`, `%PROGRAMFILES%`, `%PROGRAMFILES(X86)%`, `%APPDATA%` on Windows. If discovery finds multiple matches, the script exits and lists them — re-run with an absolute path. On Linux or other platforms, pass `--asar /path/to/app.asar` explicitly.
- **Safety** — the script refuses to write to `/`, the user home directly, or the current working directory, and refuses to populate an existing non-empty output dir without `--force`.
- **No global installs** — `@electron/asar` and `prettier` are resolved on-the-fly via `npx -y`. First run will be slower while npx caches them.
