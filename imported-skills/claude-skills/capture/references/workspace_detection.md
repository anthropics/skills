# Workspace Detection Tactics

This reference answers exactly one decision: **how does the capture skill verify Section 3 connections without fabricating them, across the four contexts the skill might run in?**

Pair with `scripts/workspace_inventory.py` for the deterministic Glob+Grep implementation.

## The Core Rule

Section 3 ("Connections") earns the skill its keep. It also breaks the skill faster than anything else if it lies. The rule:

> **Only surface connections that were actually verified by Glob, Grep, Read, or an equivalent retrieval call this turn.**

If you can't verify, you say "no workspace accessible" or "no connections found" — never invent something plausible-sounding.

## Context 1: Claude Code CLI (filesystem-native)

**Tools available:** `Glob`, `Grep`, `Read`, `Bash`.

**Tactics, in order:**

1. **Extract keywords from the dump.** Pull domain nouns, project names, file-format hints (`.md`, `.py`, `auth`, `consensus`, `pricing`).
2. **Glob for filename matches.** `Glob("**/*{keyword}*")` for each keyword. Limit to top-N matches per keyword to avoid noise.
3. **Grep for content matches.** `Grep("{keyword}")` constrained to source extensions.
4. **Read the top-level structure.** `Bash("ls -la")` and `Bash("find . -maxdepth 2 -type d | head -30")` to surface relevant folders.
5. **Stitch the matches into Section 3 entries.** Each entry: `- {file or folder}: {how it relates to dump item N, with evidence}`.

**Example output:**

```
## Connections

- `engineering/grill-me/` — relates to your "build a grill skill" dump item (folder exists, has plugin.json + SKILL.md). Likely the template you'd want to mirror.
- `megaprompts/05-capture-megaprompt.md` — relates to your "convert capture spec to skill" item. The spec file is here.
- `documentation/implementation/` — empty directory, but the location for the implementation plan you mentioned.
```

**What NOT to do:**
- "There's probably a config for that somewhere" — speculation, no verification.
- "Your project likely has an auth module" — guess, no Glob.
- "I see you might have considered X before" — projection, no Grep.

## Context 2: Claude.ai with project knowledge

**Tools available:** Project-knowledge file list, file content reads.

**Tactics:**

1. **List the project knowledge files** — at the start of the run, get the file inventory.
2. **Match by title keyword** — for each dump keyword, find files whose titles contain it.
3. **Open the top matches** and check if the content is actually related (not just title coincidence).
4. **Surface only the verified matches** in Section 3.

**What NOT to do:**
- Cite a file you didn't open — title match alone is not enough.
- Claim a file says X without quoting evidence.

## Context 3: Connected tools (Notion, Drive, GitHub, Slack via MCP)

**Tools available:** Whatever MCP tools the harness has registered for the user's connected services.

**Tactics:**

1. **Check tool availability first** — list the MCP tools surfaced for this session. If no Notion/Drive/GitHub MCP is registered, skip this context.
2. **Search via MCP** — use the search tool for each tool with dump keywords.
3. **Surface verified hits** with the link / ID returned by the tool.

**What NOT to do:**
- Reference a Notion page that wasn't returned by the search.
- Cite a GitHub issue number without confirming via the GitHub MCP.

## Context 4: No accessible workspace

**Signals you're in this context:**
- No filesystem tools loaded
- No project knowledge attached
- No workspace MCPs registered
- `workspace_inventory.py` returns empty + you can't verify any other way

**Required behavior:**

State the limitation explicitly. Ask about the user's setup. Do NOT fabricate connections.

**Template output:**

```
## Connections

No workspace accessible from here, so this section is empty. If you're running
this from Claude Code or have a project with files attached, I can fill it in.

Want to share where this work lives — a repo path, a Notion workspace, an
attached project? I can re-run the connections pass with that context.
```

## Operational Checklist (Per Run)

- [ ] Extract dump keywords (domain nouns, project names, format hints)
- [ ] Determine context (CLI / web project / MCP-connected / inaccessible)
- [ ] Run the context-appropriate tactics; never skip verification
- [ ] If context is "inaccessible", say so explicitly + ask about setup
- [ ] Each Section 3 entry must cite the evidence (filename matched, search hit, etc.)
- [ ] Zero entries with phrasing like "probably", "likely", "you might have" — those are speculation, not connections

## Why This Matters

The single fastest way to lose user trust in capture is to surface a fabricated connection. Once the user catches one — "wait, that file doesn't exist" — they stop trusting the entire output, including the items that were correct. Verification is cheap; fabrication is expensive.
