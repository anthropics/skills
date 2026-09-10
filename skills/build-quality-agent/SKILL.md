---
name: build-quality-agent
description: Claude-powered git pre-push hook that diffs your changes, optionally runs your project's build, and blocks pushes that would fail CI. Use when setting up a new repo, after a wasted Vercel build minute, or before any push to a branch that triggers paid CI.
---

# Build Quality Agent

A pre-push hook for solo founders that runs Claude Haiku 4.5 over the staged diff and decides PASS / BLOCK before code ever reaches a paid CI minute. Catches type errors, missing imports, leftover console.log, and "I forgot to save that file" mistakes locally for ~$0.0006 per push.

## When to use this skill

Invoke this skill when:

- The user is setting up a new repo and wants a pre-push safety net
- A remote build just failed and the user asks "how do I stop pushing broken commits"
- Cloud build minutes are showing up as a top line item in the cost audit
- The user is about to push a large refactor to a branch that auto-deploys to Vercel / Netlify / Fly
- A pre-push hook needs to run the actual project build (`--build` mode) as part of the gate

## What it does

1. **Reads git's pre-push stdin** (`<local_ref> <local_oid> <remote_ref> <remote_oid>`) and constructs the diff for the push range
2. **Filters junk paths** before sending to the LLM — lockfiles, `.next/`, `dist/`, binary assets, generated types
3. **Caps the diff at 50 kB** and sends a Vercel-aware prompt to Claude Haiku 4.5
4. **Optional `--build` mode**: auto-detects the project's build runner per lockfile (bun / pnpm / yarn / npm for JS, `python -m build` for Python, `cargo check` for Rust, `go build ./...` for Go) and pipes failures into the LLM review with `CI=1`
5. **Returns PASS / BLOCK with reasons**. Build failures always BLOCK regardless of LLM verdict
6. **Graceful degradation**: any internal failure (missing key, network, rate limit) defaults to PASS so the hook never traps the operator offline
7. **Logs token usage** to `~/.build-quality-agent/usage.jsonl` so cost-audit-agent can attribute spend

## Examples

### Example 1: Hook catches missing import

User: "Set up build-quality-agent in this Next.js repo"

Skill output:
```
✓ Installed pre-push hook at .git/hooks/pre-push
✓ Detected lockfile: bun.lockb → bun run build
✓ Test push (--dry-run):

Diff summary: 2 files changed, +47/-3
Claude verdict: BLOCK
Reasons:
  1. components/feed/card.tsx imports `motion` from "framer-motion" but
     package.json has no framer-motion dependency
  2. lib/auth.tsx new export `getServerSession` is referenced from 3 routes
     but not exported (typo: getSeverSession on line 84)

Bypass once: BUILD_AGENT_SKIP=1 git push
Activate build mode: BUILD_AGENT_BUILD=1 git push
```

### Example 2: Build mode unifies LLM + compiler output

User: "I keep getting Vercel build failures after I push, can the hook actually run the build first?"

Skill: Enables `--build` flag. On next push, runs `bun run build` locally with a 4-minute timeout, captures stdout+stderr, and pipes both the diff AND the build log to Claude in one call. The unified review surfaces "your tsc error in line 84 is caused by the missing prop in the call site in line 12 of the same diff" — context a raw build log can't give you.

## Guidelines

- **PASS-by-default on internal failure** — a broken hook must never block legitimate work. Missing API key, rate limit, or network error → PASS with a warning log
- **Always include a bypass instruction** in BLOCK output (`BUILD_AGENT_SKIP=1 git push`) — the operator is the final authority
- **Never run the build in `--build` mode against branches that publish artifacts** (e.g., `release/*`) unless the operator has opted in explicitly
- **Log every invocation** to `~/.build-quality-agent/usage.jsonl` with token counts, even on PASS — this is how cost-audit-agent prices the hook
- **Cap diff at 50 kB**. Larger diffs get truncated with `[... 12,438 bytes elided ...]` and a note in the prompt
- **Filter lockfiles, build artifacts, and binary blobs** before sending — they burn tokens and degrade signal
- **Never modify the working tree or stash anything** — the hook is read-only relative to git state

## Configuration

The skill expects:

- `ANTHROPIC_API_KEY` — required for LLM review. If missing, hook PASSes with a warning
- `BUILD_AGENT_SKIP=1` — operator bypass for a single push
- `BUILD_AGENT_BUILD=1` — opt-in to local build runner (`--build` flag equivalent)
- `BUILD_AGENT_MODEL` — override default model (defaults to `claude-haiku-4-5`)

No additional setup beyond `pip install build-quality-agent` and `build-quality-agent install` from inside the target repo.

## Provenance

This skill wraps the open-source [build-quality-agent](https://github.com/alex-jb/build-quality-agent) (MIT, PyPI: `pip install build-quality-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. The Skills Marketplace version embeds the same logic with the YAML-frontmatter wrapper for Claude integration. Currently shipped at v0.5.0 with 24 passing tests including the `parse_known_args` fix for git's positional `origin <url>` args.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, customer support, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
