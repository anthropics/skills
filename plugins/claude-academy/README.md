# Claude Academy

Learn Claude with Claude. This plugin helps Claude point you to the right
[Claude Academy](https://academy.claude.com) course, tutorial, or use case
when you ask how to use Claude, and lets Claude search and read Academy
content directly.

It has two parts:

- **The `academy-guide` skill.** When you ask how to use Claude or one of
  its products (for example "how do I get started with projects?" or "teach
  me Claude Code"), Claude answers your question and then, only when there
  is a strong match, mentions one or two matching Academy items. The skill
  reads the live Academy catalog, so it never recommends content from
  memory.
- **The Claude Academy connector.** `.mcp.json` points at the Claude Academy
  MCP server at `https://academy.claude.com/mcp`. It is read-only and needs
  no sign-in. It gives Claude three tools: search Academy content, read a
  specific item, and list what is available.

## Install

**Claude Code**

```
/plugin marketplace add anthropics/skills
/plugin install claude-academy@anthropic-agent-skills
```

Once the plugin is enabled, the `claude-academy` server appears in `/mcp`.

## Try asking

- "How do I get started with Claude projects?"
- "What can Claude Code do? I've never used it."
- "Is there a course on rolling Claude out to my team?"
- "Search Claude Academy for anything about skills and connectors."

## Structure

```
claude-academy/
├── .claude-plugin/
│   └── plugin.json          # Plugin metadata
├── .mcp.json                # Claude Academy MCP server
├── skills/
│   └── academy-guide/
│       ├── SKILL.md         # The academy-guide skill
│       └── LICENSE.txt
└── README.md
```

## Notes for maintainers

- `skills/academy-guide/` in this plugin is a copy of the top-level
  [`skills/academy-guide`](../../skills/academy-guide) in this repository,
  which remains the canonical version and is what the standalone
  `academy-guide` marketplace entry installs. When the skill changes, update
  both copies and bump `version` in `plugin.json`. There is no need to
  install the standalone `academy-guide` plugin alongside this one; that
  would load the same skill twice.
- The MCP server is optional. The plugin works with the skill alone; the
  server adds search over the full Academy catalog.

## License

Apache-2.0. See `skills/academy-guide/LICENSE.txt`.
