---
name: polyflow
description: Use when running parallel multi-model AI workflows — code review, security audit, cross-validation, or any task where consensus across models is more reliable than a single model's answer. Invoke when the user says "run polyflow", "multi-model review", "parallel AI analysis", "compare models", or wants multiple AI perspectives on the same input.
---

Run parallel multi-model AI workflows using the `polyflow` CLI. Multiple models check the same thing simultaneously — consensus findings are more reliable than any single model's output. Describe what you want in plain English, or use one of 22 built-in workflows.

## Setup

```bash
pip install polyflow-ai
export OPENROUTER_API_KEY=sk-or-...   # one key covers Claude + Gemini + GPT-4
polyflow doctor                        # verify setup
```

## Key commands

```bash
# Describe what you want — Polyflow generates the workflow
polyflow new "multiple models audit my API for security issues, vote on findings" -o audit.yaml
polyflow run ./audit.yaml -i "$(cat src/api.py)"

# Or use a built-in workflow directly
polyflow run code-review-multi-model -i "$(git diff HEAD~1)"
polyflow run security-audit -i "$(cat src/auth.py)"
polyflow run cross-validate -i "your design or problem statement"

# Run headlessly — no prompts, auto-approve all checkpoints
polyflow run <workflow> --ci -i "..."

# Browse 22 built-in workflows
polyflow list
polyflow list --tag security

# Validate a custom workflow file
polyflow validate my-workflow.yaml
```

## Workflow selection guide

| Task | Workflow |
|---|---|
| Review a code diff or PR | `code-review-multi-model` |
| Security vulnerability scan | `security-audit` |
| Cross-validate a plan or design | `cross-validate` |
| Triage a bug report | `bug-triage` |
| Generate unit tests | `test-generation` |
| Write a PR description | `pr-description` |
| Architecture decision record | `adr-generator` |

## How multi-model consensus works

Each `type: parallel` step sends the same prompt to multiple models at the same time. The `aggregate` block synthesizes results:

- `mode: vote` — surfaces findings all models agree on (high confidence)
- `mode: diff` — highlights where models disagree (needs human review)
- `mode: summary` — one model synthesizes all outputs into a single report

This is not about humans being smarter than AI. It's about models checking each other — the same principle behind ensemble methods in ML.

## Write a custom consensus workflow

**From natural language (recommended):**

```bash
polyflow new "claude and gemini cross-validate my code logic, diff mode" -o review.yaml
```

**Or write YAML directly:**

```yaml
name: my-consensus-review
steps:
  - id: validate
    type: parallel
    steps:
      - id: claude_view
        model: claude
        prompt: "Review this and list issues: {{input}}"
      - id: gemini_view
        model: gemini
        prompt: "Review this and list issues: {{input}}"
      - id: gpt4_view
        model: gpt-4
        prompt: "Review this and list issues: {{input}}"
    aggregate:
      mode: vote            # high-confidence: all models agree
      model: claude         # Claude synthesizes the final report
      prompt: |
        Multiple models independently reviewed this.
        Synthesize findings. Mark items all models flagged as HIGH CONFIDENCE.
        {{aggregated}}

output:
  format: markdown
  save_to: review.md
```

Run it: `polyflow run ./my-consensus-review.yaml -i "your input"`

## GitHub Actions integration

Add multi-model consensus to any repo:

```yaml
- uses: celesteimnskirakira/polyflow@main
  with:
    workflow: code-review-multi-model
    input: ${{ steps.diff.outputs.content }}
    openrouter-api-key: ${{ secrets.OPENROUTER_API_KEY }}
```

Full examples in [`.github/workflows/`](https://github.com/celesteimnskirakira/polyflow/tree/main/.github/workflows).
