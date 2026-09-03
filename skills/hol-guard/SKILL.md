---
name: hol-guard
description: Use when setting up HOL Guard to protect Claude Code before tool execution, reviewing Guard approvals or evidence, or scanning Claude skills, plugins, and MCP packages before use or release.
license: Apache-2.0
---

# HOL Guard

HOL Guard is local runtime security for AI coding agents. Use the real `hol-guard` CLI for harness protection and the separate `plugin-scanner` CLI for package verification.

## Safety rules

- Never read `.env` files or expose secrets while checking a workspace.
- Never bypass a Guard approval to make a blocked action proceed.
- Do not claim Claude Code is protected until Guard status/doctor output proves it.
- Prefer Guard-owned setup commands over manual edits to Claude configuration.
- Treat deny, review, error, or unavailable Guard outcomes as blocked. Do not run the protected action afterward.
- Preserve existing user changes and inspect repository state before making edits.

## Install and verify

Try the CLI first:

```bash
hol-guard --version
```

If it is not installed and the user asked for runtime protection, prefer an isolated CLI install:

```bash
pipx install hol-guard
```

Then inspect the current environment:

```bash
hol-guard status
hol-guard detect --json
```

`plugin-scanner` is a separate distribution. For skill, plugin, MCP, or marketplace verification:

```bash
plugin-scanner --version
```

If it is missing and scanning is requested:

```bash
pipx install plugin-scanner
```

## Protect Claude Code

Claude Code is a first-class HOL Guard harness target. Use Guard-owned setup rather than hand-editing Claude hooks or approval configuration:

```bash
hol-guard bootstrap
hol-guard install claude-code
hol-guard run claude-code --dry-run
hol-guard run claude-code
hol-guard doctor claude-code --json
hol-guard status
```

Use this flow when the workspace contains Claude Code settings, hooks, agents, skills, or MCP configuration and the user wants runtime protection before tools execute.

The `claude` harness alias maps to `claude-code`, but prefer the explicit `claude-code` name in instructions and evidence.

## Handle approvals

When Guard blocks or queues an action, inspect it before deciding:

```bash
hol-guard approvals
hol-guard approvals open
hol-guard receipts
hol-guard diff claude-code
```

For terminal-only resolution:

```bash
hol-guard approvals approve <request-id>
hol-guard approvals deny <request-id>
```

Only approve after the risk reason and requested scope are understood. Never infer approval from a successful previous command.

## Produce evidence

Use Guard evidence commands when the user needs an audit trail or handoff artifact:

```bash
hol-guard receipts
hol-guard inventory
hol-guard abom --format json
hol-guard events
hol-guard explain <artifact-id>
```

Cloud connectivity is optional and user-directed:

```bash
hol-guard connect
hol-guard connect status
hol-guard sync
```

## Scan skills, plugins, and MCP packages

Use scanner mode for Claude skills, Claude Code plugins, MCP server packages, and marketplace bundles:

```bash
plugin-scanner lint <path>
plugin-scanner verify <path>
```

For the current workspace:

```bash
plugin-scanner lint .
plugin-scanner verify .
```

Scan the package root so its manifests, `SKILL.md`, MCP configuration, hooks, and related files can be evaluated together. A scanner failure is not permission to continue; inspect the reported finding first.

## Command inspection versus harness protection

`hol-guard command test` is side-effect-free command inspection. It is useful for examining a command decision, but it is not a substitute for Guard-owned Claude Code harness installation and runtime protection when the user asks to enforce policy before tools execute.

## Report results

When using HOL Guard, report only evidence-backed state:

- the Guard/scanner command that ran;
- what it found or blocked;
- any approval or risk that remains unresolved;
- the receipt, doctor, or scanner evidence that proves the result;
- the exact next user action only when one is actually required.

Do not claim protection, approval, or release readiness without command output proving it.
