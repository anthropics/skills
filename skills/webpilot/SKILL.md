---
name: webpilot
description: Skill for LLM agents to drive a real browser through the Webpilot CLI and shared WebSocket runtime.
license: Complete terms in LICENSE.txt
---

# Webpilot Skill

Use Webpilot as a browser tool.

It gives you a local browser runtime, a CLI, and a WebSocket command surface. Your job is not to guess. Your job is to inspect page state, choose a safe action, run it, and verify the result.

**Do not default to screenshots.** Webpilot exposes the live DOM directly. Screenshots are slow, expensive, and unnecessary for most tasks. Use `html`, `discover`, and `q` to read page state. Reserve `ss` for cases where layout or visual rendering is the actual question.

## Runtime

```bash
npx h17-webpilot start
npx h17-webpilot start -d
```

If the runtime is already running, use `npx h17-webpilot -c '...'` directly.

Once the runtime is running, list all available commands:

```bash
npx h17-webpilot -c '.help'
```

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

- `npx h17-webpilot -c 'html'`: read the current page DOM, title, and URL
- `npx h17-webpilot -c 'discover'`: list interactive elements and their handles
- `npx h17-webpilot -c 'q <selector>'`: query specific elements
- `npx h17-webpilot -c 'wait <selector>'`: wait for a known state change
- `npx h17-webpilot -c 'ss'`: last resort — only when layout or visual rendering is the actual question, not DOM structure

## Act

Use the safest matching action:

- `npx h17-webpilot -c 'click <selector|handleId>'`
- `npx h17-webpilot -c 'type [selector] <text>'`
- `npx h17-webpilot -c 'clear <selector>'`
- `npx h17-webpilot -c 'key <name>'`
- `npx h17-webpilot -c 'sd [px] [selector]'`
- `npx h17-webpilot -c 'su [px] [selector]'`
- `npx h17-webpilot -c 'go <url>'`
- `npx h17-webpilot -c 'cookies load ./cookies.json'` when the task requires restoring an existing session

`click` goes through the human action pipeline. If the runtime refuses the action, respect the refusal and re-inspect the page.

## Verify

After navigation or interaction, confirm the new state:

- `npx h17-webpilot -c 'wait <selector>'`
- `npx h17-webpilot -c 'url'`
- `npx h17-webpilot -c 'title'`
- `npx h17-webpilot -c 'html'`
- `npx h17-webpilot -c 'q <selector>'`

## Safe Usage Rules

- Never guess selectors when `html` or `discover` can tell you the real ones.
- Never assume a click worked. Verify it.
- Never treat `{ "clicked": false }` as something to brute-force through.
- Never confuse DOM reading with interaction. Read first, then act.
- Re-query stale handles instead of reusing them blindly.

## Raw Protocol

If you need a protocol action that the shorthand CLI does not expose directly, send it through raw mode:

```bash
npx h17-webpilot -c 'dom.queryAllInfo {"selector": "a[href]"}'
npx h17-webpilot -c 'human.scroll {"selector": ".feed", "direction": "down"}'
npx h17-webpilot -c 'framework.getConfig {}'
```

You can also send a full JSON message:

```bash
npx h17-webpilot -c '{"action": "tabs.navigate", "params": {"url": "https://example.com"}}'
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

The MCP server connects to the same WebSocket runtime (`ws://localhost:7331`). Start the runtime first with `npx h17-webpilot start`, then the MCP tools become available in the host application automatically.

## Limits

- Public defaults are generic and uncalibrated.
- This tool does not give you task strategy, retries, route doctrine, or tuned behavior profiles.
- Advanced outcomes depend on how well you choose selectors, waits, verification steps, and configuration.
