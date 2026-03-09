---
name: webpilot
description: Skill for LLM agents to drive a real browser through the Webpilot CLI and shared WebSocket runtime.
---

# Webpilot Skill

Use Webpilot as a browser tool.

It gives you a local browser runtime, a CLI, and a WebSocket command surface. Your job is not to guess. Your job is to inspect page state, choose a safe action, run it, and verify the result.

## Runtime

```bash
npx h17-webpilot start
npx h17-webpilot start -d
```

If the runtime is already running, use `npx h17-webpilot -c '...'` directly.

Use `npx h17-webpilot start -d` when you want an append-only session log.

- default path: `~/h17-webpilot/webpilot.log`
- config override: `framework.debug.sessionLogPath`

## Operating Loop

Use this order every time:

1. Inspect.
2. Act.
3. Verify.

Do not skip the inspect step unless you already have fresh page state from the immediately preceding command.

## Inspect

Use these first:

- `npx webpilot -c 'html'`: read the current page DOM, title, and URL
- `npx webpilot -c 'discover'`: list interactive elements and their handles
- `npx webpilot -c 'q <selector>'`: query specific elements
- `npx webpilot -c 'wait <selector>'`: wait for a known state change
- `npx webpilot -c 'ss'`: take a screenshot when visual context matters

## Act

Use the safest matching action:

- `npx webpilot -c 'click <selector|handleId>'`
- `npx webpilot -c 'type [selector] <text>'`
- `npx webpilot -c 'clear <selector>'`
- `npx webpilot -c 'key <name>'`
- `npx webpilot -c 'sd [px] [selector]'`
- `npx webpilot -c 'su [px] [selector]'`
- `npx webpilot -c 'go <url>'`
- `npx webpilot -c 'cookies load ./cookies.json'` when the task requires restoring an existing session

`click` goes through the human action pipeline. If the runtime refuses the action, respect the refusal and re-inspect the page.

## Verify

After navigation or interaction, confirm the new state:

- `npx webpilot -c 'wait <selector>'`
- `npx webpilot -c 'url'`
- `npx webpilot -c 'title'`
- `npx webpilot -c 'html'`
- `npx webpilot -c 'q <selector>'`

## Safe Usage Rules

- Never guess selectors when `html` or `discover` can tell you the real ones.
- Never assume a click worked. Verify it.
- Never treat `{ "clicked": false }` as something to brute-force through.
- Never confuse DOM reading with interaction. Read first, then act.
- Re-query stale handles instead of reusing them blindly.

## Raw Protocol

If you need a protocol action that the shorthand CLI does not expose directly, send it through raw mode:

```bash
npx webpilot -c 'dom.queryAllInfo {"selector": "a[href]"}'
npx webpilot -c 'human.scroll {"selector": ".feed", "direction": "down"}'
npx webpilot -c 'framework.getConfig {}'
```

You can also send a full JSON message:

```bash
npx webpilot -c '{"action": "tabs.navigate", "params": {"url": "https://example.com"}}'
```

## Strategy Notes

- Prefer `html`, `discover`, and `q` over `eval` when DOM inspection is enough.
- Use `wait` after page-changing actions.
- Use handle IDs when you already have a fresh element from `discover` or `q`.
- Use screenshots when layout or visibility is the uncertainty, not HTML structure.
- If the task needs a preloaded authenticated session, load cookies first or use config boot commands.

## MCP Server

An MCP adapter is available for environments that support the Model Context Protocol (e.g. Claude Desktop, Cursor, Windsurf).

Claude Desktop config (`~/Library/Application Support/Claude/claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "webpilot": {
      "command": "npx",
      "args": ["webpilot-mcp"]
    }
  }
}
```

The MCP server connects to the same WebSocket runtime (`ws://localhost:7331`). Start the runtime first with `npx webpilot start`, then the MCP tools become available in the host application automatically.

## Limits

- Public defaults are generic and uncalibrated.
- This tool does not give you task strategy, retries, route doctrine, or tuned behavior profiles.
- Advanced outcomes depend on how well you choose selectors, waits, verification steps, and configuration.
