---
name: multisage
description: Query Multisage for multi-expert AI answers from Claude, GPT, and Gemini. Use this skill whenever the user wants multiple AI perspectives on a question, says "ask multisage", "multisage this", "get expert opinions", wants a multi-AI consultation, or needs a well-rounded answer that considers different viewpoints. Also use for deep research queries that need comprehensive analysis from multiple AI providers in parallel.
user-invocable: true
context: fork
allowed-tools: Bash, Read
---

# Multisage Skill

Query the Multisage API for multi-expert AI answers. Multisage sends your question to Claude, GPT, and Gemini simultaneously, then synthesizes their responses into a single, well-rounded answer — highlighting where they agree, disagree, and what unique insights each provides.

## Prerequisites

The `multisage` CLI must be installed globally:

```bash
npm install -g multisage
```

An API key is required. Get one at https://multisage.ai/settings (under "API Keys").

### API Key Setup (Do This First)

Before running any multisage command, you must ensure `MULTISAGE_API_KEY` is available in your shell. The env var is often NOT inherited automatically — check and load it explicitly:

```bash
# 1. Check if it's already set
echo "${MULTISAGE_API_KEY:0:8}"

# 2. If empty, look for it in common locations
grep MULTISAGE_API_KEY .env 2>/dev/null || grep MULTISAGE_API_KEY ~/.env 2>/dev/null

# 3. Export it (replace with actual key found above)
export MULTISAGE_API_KEY="msk_..."
```

If you get a timeout or authentication error, the most likely cause is a missing API key — always verify it's set before debugging further.

## Running from Claude (Important)

When running multisage from Claude or any non-interactive context, always use the **`-q`** flag to suppress the interactive spinner (doesn't render in tool output).

Redirect output to a file with `>` instead of piping through `tee`, which can cause issues in non-TTY contexts:

```bash
# Correct — redirect to file
multisage -q "your question" > /tmp/multisage-output.txt 2>&1
cat /tmp/multisage-output.txt

# Wrong — tee can cause issues in non-TTY contexts
multisage -q "your question" | tee output.txt  # DON'T DO THIS
```

## Standard Query

For most questions, run a standard query. This consults all three AI providers and returns a synthesized answer with stage breakdown:

```bash
multisage -q "your question here"
```

The default output shows each stage: quick answer, expert synthesis, and debate (if the experts disagree). This costs 1 credit.

## Deep Research

For questions that need thorough, in-depth analysis — research topics, complex technical questions, literature reviews — use deep research mode. This launches 3 parallel deep research sessions (one per provider) and synthesizes the results:

```bash
multisage -q --deep-research "your question here"
```

Deep research costs 5 credits and takes 5-25 minutes. The CLI streams progress updates as each provider completes. You can detach with Ctrl+C and check results later.

## Output Options

| Flag | What it does |
|------|-------------|
| `-q` | Suppress spinner (always use from Claude) |
| `-f, --full` | Show everything: quick answer, individual expert responses, synthesis, debate |
| `--final-only` | Show only the final synthesized answer (skip stages) |
| `-j, --json` | Output as structured JSON |
| `--deep-research` | Use deep research mode (5 credits, 5-25 min) |

Combine flags as needed. For example, `-f -q` gives full output without a spinner. `-j` gives structured JSON (useful if you need to parse the response programmatically).

## Managing Deep Research

Deep research runs asynchronously. If you start one and need to check on it later:

```bash
# Check if results are ready
multisage results <threadId>

# Cancel an in-progress query
multisage cancel <threadId>
```

The `threadId` is printed when you start a deep research query.

## When to Use Which Mode

- **Standard** (`multisage -q "..."`) — Good for most questions. Quick (30-90 seconds), costs 1 credit. Best for factual questions, advice, comparisons, code help.
- **Deep Research** (`multisage -q --deep-research "..."`) — For thorough analysis. Each provider does its own deep research with web search, then results are cross-referenced and synthesized. Best for research topics, technical deep-dives, market analysis, literature reviews.

## Typical Usage from Claude

```bash
# Standard query — redirect to file, then read
multisage -q "What are the tradeoffs between SQLite and PostgreSQL for a hobby project?" > /tmp/ms-output.txt 2>&1
cat /tmp/ms-output.txt

# Full output (includes individual expert responses)
multisage -q -f "What are the tradeoffs between SQLite and PostgreSQL for a hobby project?" > /tmp/ms-output.txt 2>&1
cat /tmp/ms-output.txt

# Deep research
multisage -q --deep-research "What are the latest advances in protein folding prediction?"

# JSON output for parsing
multisage -q -j "Is Rust or Go better for CLI tools?" > /tmp/ms-output.txt 2>&1
cat /tmp/ms-output.txt | jq '.answer'
```

## Response Structure

The API returns:
- `answer` — Final synthesized answer
- `experts` — List of expert names (or full details with `-f`)
- `creditsUsed` — Credits consumed (1 for standard, 5 for deep research)
- `stages.quickAnswer` — Initial quick answer before expert consultation
- `stages.synthesis` — Synthesized answer incorporating all expert perspectives
- `stages.debate` — Debate section highlighting disagreements (null if experts agree)

## Limits and Errors

- Questions are truncated to 1000 characters
- 5-minute timeout for standard queries
- API keys must start with `msk_`
- Rate limit: 10 requests/minute, 3 concurrent

| Status | Meaning |
|--------|---------|
| 401 | Invalid or missing API key |
| 402 | Insufficient credits — purchase at https://multisage.ai/pricing |
| 429 | Rate limited or too many concurrent requests (check Retry-After header) |
| 500 | Server error — try again |

## Troubleshooting

**Timeout errors** are almost always caused by a missing API key — the CLI makes an unauthenticated request that hangs instead of returning a clean error. Fix: verify `MULTISAGE_API_KEY` is exported (see API Key Setup above).

**Diagnostic checklist** (run these before retrying):
```bash
# Is the API key set?
[ -n "$MULTISAGE_API_KEY" ] && echo "Key set: ${MULTISAGE_API_KEY:0:8}..." || echo "KEY NOT SET"

# Is the CLI installed?
which multisage && multisage -V

# Quick connectivity test
multisage -q "hello" > /tmp/ms-test.txt 2>&1 && echo "OK" || echo "FAILED — check output:" && cat /tmp/ms-test.txt
```
