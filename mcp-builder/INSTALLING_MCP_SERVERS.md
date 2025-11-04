# Installing MCP servers in VS Code / VS Code Insiders

This short guide explains the two common ways VS Code can register an MCP (Model Context Protocol) server and why they produce different `mcp.json` entries. It also recommends a preferred approach and shows how to pin and verify versions.

Summary
- "Command-line" / one-liner `code --add-mcp ...` — quick and minimal. It registers a name and command but doesn't add UI inputs or marketplace metadata. Good for ad-hoc/local installs or simple overrides.
- "Marketplace" extension install — richer metadata (inputs, gallery URL, version), and the extension can provide configurable inputs and default values. It also supports updates via the Extensions marketplace.

Why they differ
- The `code --add-mcp` command simply appends the minimal configuration you pass to the local `mcp.json` file. It does not (and cannot) inject extension-provided metadata like `gallery`, `version` or `inputs` unless you include those manually in the JSON you write.
- Installing the MCP server via the VS Code Extensions marketplace registers the MCP entry using metadata bundled with the extension. That metadata can include:
  - `gallery` — the MCP extension gallery URL
  - `version` — a version string the extension supplies
  - `inputs` — prompts and default values (so VS Code can prompt you for values used as ${input:...})
  - additional CLI args with `${input:...}` placeholders

Example: "simple" (one-liner) entry
```json
"chrome-devtools": {
  "command": "npx",
  "args": ["chrome-devtools-mcp@latest"],
  "type": "stdio"
}
```
- Minimal and explicit. VS Code will run `npx chrome-devtools-mcp@latest` when starting the MCP server.
- No interactive inputs or metadata are provided by VS Code.

Example: "marketplace" entry (what an extension might install)
```json
"chromedevtools/chrome-devtools-mcp": {
  "type": "stdio",
  "command": "npx",
  "args": [
    "chrome-devtools-mcp@latest",
    "--browserUrl",
    "${input:browser_url}",
    "--headless",
    "${input:headless}",
    "--isolated",
    "${input:isolated}",
    "--channel",
    "${input:chrome_channel}"
  ],
  "gallery": "https://api.mcp.github.com/2025-09-15",
  "version": "0.0.1-seed"
},
"inputs": [ /* prompts & defaults shown here */ ]
```
- The extension provides prompts (the `inputs` block) so VS Code will display input prompts for the placeholders used in the `args` array.
- The `gallery` and `version` fields come from the extension's metadata.

Which should I use?
- Marketplace install (preferred) when:
  - A marketplace extension exists for the MCP server and you want the richer UX (config prompts, defaults).
  - You want the extension to be able to ship updates via the marketplace.
- Manual `code --add-mcp` (useful) when:
  - You want a quick local registration or need to customize the exact command-line yourself.
  - You want to pin a specific version inline or control args explicitly without involving an extension.

How to pin a version (recommended for reproducibility)
- In the simple one-liner you can pin by replacing `@latest` with a specific semver, e.g. `"chrome-devtools-mcp@1.2.3"`.
- In the marketplace-installed entry the extension may include a `version` field, but it’s controlled by the extension publisher. If you need a pinned version, prefer adding a manual entry to `mcp.json` or ask the extension author to expose a way to choose a pinned version.

How to check which version is running
- Ideal: the MCP server prints its version on startup. If it doesn't, you can try:
  - Run the binary manually to inspect its version: `npx chrome-devtools-mcp@latest --version` or `npx chrome-devtools-mcp@1.2.3 --version` (if the CLI supports `--version`).
  - Inspect the installed extension's `mcp.json` entry for a `version` field (marketplace install may add it).
  - Check the extension's marketplace page or repository release tags for the published version.

Suggested small improvements (for extension authors & maintainers)
- Print the package name and version to stdout/stderr when the MCP server starts. That makes the startup logs help users quickly identify which package/version is being launched.
- If the extension offers runtime flags via `${input:...}`, include helpful default values and descriptions in the `inputs` block so users are guided when configuring the server.

If you want to open a PR
- This repository's `mcp-builder` docs can be updated to include this file (or link to it). It’s a safe, low-risk documentation improvement we can submit as a PR.

Troubleshooting tips
- If you see two entries in `mcp.json` after installing both ways, remove the one you don't want (the marketplace entry uses the extension id as the key). If you prefer the extension-managed entry, remove the manual one to avoid duplicate names/ambiguity.
- If the server behaves differently between installs, check the `args` array for extra flags the extension adds (e.g., `--headless`, `--isolated`) and replicate them in your manual entry if desired.

