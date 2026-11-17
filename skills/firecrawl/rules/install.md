---
name: firecrawl-cli-installation
description: |
  Install the official Firecrawl CLI and handle authentication.
  Package: https://www.npmjs.com/package/firecrawl-cli
  Source: https://github.com/firecrawl/cli
  Docs: https://docs.firecrawl.dev/sdks/cli
---

# Firecrawl CLI Installation

## Quick Setup (Recommended)

```bash
npx -y firecrawl-cli@latest init -y --browser
```

This installs `firecrawl-cli` globally, authenticates via browser, and installs core, build, and workflow skills.

This setup is safe to re-run when the CLI is missing, stale, or only partially configured.

If `firecrawl` is already installed and you want to update it first:

```bash
npm update -g firecrawl-cli
```

Skills are installed globally across all detected coding editors by default.

To install skills manually:

```bash
firecrawl setup skills
firecrawl setup workflows
```

## Manual Install

```bash
npm install -g firecrawl-cli@latest
```

## Verify

First check status:

```bash
firecrawl --status
```

`--status` shows auth state, concurrency (max parallel jobs — run parallel operations up to that limit), and remaining API credits.

Then run one small real request to prove install, auth, and output all work:

```bash
mkdir -p .firecrawl
firecrawl scrape "https://firecrawl.dev" -o .firecrawl/install-check.md
```

The install is healthy when both commands succeed.

## Authentication

Authenticate using the built-in login flow:

```bash
firecrawl login --browser
```

This opens the browser for OAuth authentication. Credentials are stored securely by the CLI.

### Auth and credit errors are terminal

An `Unauthorized: Invalid token` or insufficient-credits error is terminal for that call: verify config once with `firecrawl --status`, then report the blocking reason and stop. Retrying the same call yields the same error.

### If authentication fails

Ask the user how they'd like to authenticate:

1. **Login with browser (Recommended)** - Run `firecrawl login --browser`
2. **Enter API key manually** - Run `firecrawl login --api-key "<key>"` with a key from firecrawl.dev

If you cannot obtain a key and the user cannot sign up, search, scrape, and interact still work without an API key on the keyless free tier (rate-limited). Commands that need an account — `crawl`, `map`, `download`, `agent`, `monitor`, `credit-usage`, and the feedback commands — prompt an interactive login when no credentials are set. Browser login or an API key remains preferred for the best results. See [agent onboarding](https://www.firecrawl.dev/agent-onboarding/SKILL.md) for the full set of onboarding paths.

### Command not found

If `firecrawl` is not found after installation:

1. Ensure npm global bin is in PATH
2. Try: `npx firecrawl-cli@latest --version`
3. Reinstall: `npm install -g firecrawl-cli@latest`
