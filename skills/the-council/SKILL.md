---
name: the-council
description: Multi-model advisory board using OpenAI Codex CLI and Google Gemini CLI to provide second opinions on code reviews, architecture plans, debugging, and general engineering decisions. Invoke when the user requests a "council" review, wants a second opinion from other AI models, asks for multi-model consensus, or says "ask the council". Also invoke proactively when making high-stakes architectural decisions or when a code review checkpoint is reached.
---

# The Council

Convene OpenAI Codex and Google Gemini as an advisory board. Both run in parallel via their CLIs, with full project context, and return independent analyses that Claude synthesizes.

## Prerequisites

- Project has a `CLAUDE.md` file in the working directory
- At least one of the following CLIs installed and authenticated:
  - `codex` CLI (`npm i -g @openai/codex`)
  - `gemini` CLI (`npm i -g @google/gemini-cli`)
- Gemini experimental plan mode enabled in `~/.gemini/settings.json` (if using Gemini):
  ```json
  { "experimental": { "plan": true } }
  ```

## Workflow

### 0. Preflight Check (First Invocation Only)

On the first council invocation in a session, run the preflight script to detect available advisors:

```bash
bash <skill_dir>/scripts/council_preflight.sh
```

Parse the output (key=value lines) and determine the operating mode:

| Codex Auth | Gemini Auth | Mode |
|------------|-------------|------|
| `true` | `true` | **Full Council** — both advisors in parallel |
| `true` | `false` | **Codex-only** — single advisor mode |
| `false` | `true` | **Gemini-only** — single advisor mode |
| `false` | `false` | **Abort** — show installation instructions below |

**If no advisors are available**, display this help and stop:

```
Neither Codex nor Gemini CLI is available. To use The Council, install at least one:

  Codex:  npm i -g @openai/codex && codex auth
  Gemini: npm i -g @google/gemini-cli && gemini   (authenticates via OAuth on first run)
```

**If one advisor is missing**, note which mode is active and proceed. Example:

```
Council running in Codex-only mode (Gemini CLI not found).
```

The preflight result is cached for 2 hours — subsequent invocations skip this step automatically.

### 1. Sync Project Context

Run the sync script to copy CLAUDE.md content into AGENTS.md (Codex) and GEMINI.md (Gemini):

```bash
bash <skill_dir>/scripts/council_sync.sh <working_directory>
```

This creates/overwrites both files with an advisory preamble + full CLAUDE.md content. Run this once per session or when CLAUDE.md changes.

**Important:** After the council session, clean up the generated files:
```bash
rm <working_directory>/AGENTS.md <working_directory>/GEMINI.md
```

### 2. Compose the Advisory Prompt

Select the appropriate template from [references/prompt-templates.md](references/prompt-templates.md) based on the use case:

| Use Case | Template |
|----------|----------|
| Code review | Code Review |
| Plan/architecture evaluation | Architecture / Planning |
| Bug investigation | Debugging |
| General question | General Advisory |

Write the composed prompt to a temporary file. Include all relevant context inline (diffs, error messages, plan text) — the advisors cannot read Claude's conversation history.

### 3. Invoke The Council

Run the advisors based on the mode determined in Step 0:

**Full Council (both available):**
```bash
bash <skill_dir>/scripts/council_invoke.sh <prompt_file> <working_directory>
```

**Codex-only mode:**
```bash
bash <skill_dir>/scripts/council_invoke.sh --codex-only <prompt_file> <working_directory>
```

**Gemini-only mode:**
```bash
bash <skill_dir>/scripts/council_invoke.sh --gemini-only <prompt_file> <working_directory>
```

The script outputs file paths (last lines of stdout) containing the responses. Read the response file(s).

**Environment overrides:**
- `CODEX_MODEL` — default: `gpt-5.3-codex`
- `GEMINI_MODEL` — default: `gemini-3-pro-preview`
- `COUNCIL_TIMEOUT` — default: `300` (seconds)

### 4. Analyze and Present

#### Full Council Mode (both advisors responded)

**Default mode — Synthesis:** Read both responses, identify areas of agreement and disagreement, then present:

```
## Council Synthesis

**Consensus:** [Points both advisors agree on]

**Divergence:** [Points where they disagree, with each position]

**Claude's Recommendation:** [Your assessment integrating all three perspectives — yours plus both advisors']
```

**Side-by-side mode** (when user requests "show me both" or "side by side"):

```
## Codex (gpt-5.3-codex)
[Full Codex response]

## Gemini (gemini-3-pro-preview)
[Full Gemini response]

## Claude's Take
[Your own assessment]
```

#### Single-Advisor Mode (one advisor responded)

Present the single advisor's response with your own assessment:

```
## Advisory Opinion ({Advisor Name} / {model})
[Full response from the available advisor]

## Claude's Assessment
[Your own perspective, noting this was a single-advisor review]
```

### 5. Cleanup

Remove temporary files after presenting results:
- The prompt file
- The response files (in the temp directory)
- AGENTS.md and GEMINI.md from the working directory

## Permissions and Safety

Both advisors run in **read-only mode** — they can explore the codebase but cannot modify it:

- **Codex**: `--sandbox read-only` — filesystem writes are blocked by the sandbox
- **Gemini**: `--approval-mode plan` — strict read-only mode; only read tools (read_file, glob, search) are allowed; write tools are blocked

This ensures advisors never modify project files. If either CLI updates its permission model, verify read-only enforcement before updating the scripts.

## Model and Effort Configuration

Both advisors run at maximum capability:

- **Codex**: Model `gpt-5.3-codex` with reasoning effort `xhigh` (set via `~/.codex/config.toml` key `model_reasoning_effort = "xhigh"`)
- **Gemini**: Model `gemini-3-pro-preview` with thinking level `HIGH` (set via `~/.gemini/settings.json` in `modelConfigs`)

If the user's config doesn't have these settings, advise them to add:

Codex (`~/.codex/config.toml`):
```toml
model_reasoning_effort = "xhigh"
```

Gemini (`~/.gemini/settings.json`):
```json
{
  "modelConfigs": {
    "customAliases": {
      "council": {
        "modelConfig": {
          "model": "gemini-3-pro-preview",
          "generateContentConfig": {
            "thinkingConfig": { "thinkingLevel": "HIGH" }
          }
        }
      }
    }
  }
}
```

## Error Handling

- If one advisor fails, present the other's response and note the failure
- If both fail, report the errors from the log files and suggest checking CLI authentication
- Timeout defaults to 5 minutes — suggest increasing `COUNCIL_TIMEOUT` for large reviews

## When to Convene The Council

- User explicitly asks for it ("ask the council", "get a second opinion", "council review")
- High-stakes architectural decisions affecting multiple systems
- Debugging sessions stuck after multiple failed attempts
- Before finalizing major implementation plans
- Code review of security-sensitive changes
