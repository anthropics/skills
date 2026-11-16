# Claude Agent SDK — short reference

**Boundary.** This skill does not generate Claude Agent SDK code. It
covers the Claude API and Managed Agents (options 1-3 in SKILL.md's
"Building an Agent: Four Approaches"). For Agent SDK-specific
implementation, use the Agent SDK's own documentation and the bundled
package type declarations. This reference provides package
identification, installation guidance, and documentation discovery
only. Do not substitute Claude API Tool Runner implementations for
Agent SDK integrations, or vice versa.

## Is the request SDK-shaped?

Route here when the user asks about the Agent SDK `query()` entry
point, `Options` / `AgentDefinition` types, installing the SDK
package, or a batteries-included coding/filesystem agent with
built-in tools (Read/Write/Edit/Bash/Glob/Grep/WebSearch/WebFetch),
MCP, and subagents running on their own infra. That is option 4 in
SKILL.md — harness only, you host.

## Package

- npm: `@anthropic-ai/claude-agent-sdk`
- Python: `claude-agent-sdk`

Verified version (npm, 2026-11-14): **0.3.325**. The `.d.ts` line
numbers below are for that release — run `npm view
@anthropic-ai/claude-agent-sdk version` to check the latest before
installing, and re-verify the lines if the version changes.

```bash
npm install @anthropic-ai/claude-agent-sdk@0.3.325
```

Peer dependencies (confirm with `npm view
@anthropic-ai/claude-agent-sdk@0.3.325 peerDependencies`):

- `zod` `^4.0.0`
- `@anthropic-ai/sdk` `>=0.93.0`
- `@modelcontextprotocol/sdk` `^1.29.0`

## Read the types before the docs

Extract the bundled declarations (no dummy project needed):

```bash
npm pack @anthropic-ai/claude-agent-sdk@0.3.325
tar -xzf anthropic-ai-claude-agent-sdk-0.3.325.tgz package/sdk.d.ts
grep -nE 'export declare type (Options|AgentDefinition)|export declare function query' package/sdk.d.ts
```

In release 0.3.325, `package/sdk.d.ts` has:

- line 38 — `export declare type AgentDefinition = {`
- line 1651 — `export declare type Options = {`
- line 3458 — `export declare function query(_params: { prompt: string | AsyncIterable<SDKUserMessage>; options?: Options; }): Query;`

Inspect the surrounding declarations, not just the matching lines.
The `.d.ts` workflow is npm-specific; for Python, introspect the
installed `claude-agent-sdk` package instead.

## Readable docs

The HTML overview page is too large to fetch in one read
(`https://code.claude.com/docs/en/agent-sdk`, 240,095 bytes,
verified 2026-11-14). Fetch the Markdown version instead:

- Agent SDK overview (7,382 bytes):
  `https://code.claude.com/docs/en/agent-sdk.md`
- Documentation index (58,222 bytes):
  `https://code.claude.com/docs/llms.txt`

Rule of thumb for this docs site: when a link points at
`https://code.claude.com/docs/.../<page>`, append `.md` (or change
`.html` to `.md`) before fetching — the HTML pages are oversized,
the Markdown versions are not.

## Retrieval order

1. Identify the package and language.
2. Install the pinned (verified) version.
3. Inspect the bundled `.d.ts` (npm) or the installed package
   (Python).
4. Check peer-dependency metadata.
5. Fetch the compact `.md` page.
6. Use `llms.txt` only when the single page does not answer the
   question.
