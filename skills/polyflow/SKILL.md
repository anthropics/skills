---
name: polyflow
description: Use when running parallel multi-model AI workflows — code review, security audit, cross-validation, or any task where consensus across models is more reliable than a single model's answer. Invoke when the user says "run polyflow", "multi-model review", "parallel AI analysis", "compare models", or wants multiple AI perspectives on the same input.
---

Run parallel multi-model AI workflows using the `polyflow` CLI. Multiple models check the same thing simultaneously — consensus is more reliable than any single model's output.

## Setup

```bash
pip install polyflow-ai
export OPENROUTER_API_KEY=sk-or-...   # openrouter.ai — 290+ models, one key
polyflow doctor                        # verify setup
```

## Key commands

```bash
# Generate a workflow from natural language
polyflow new "multiple models audit my API for security issues, vote on findings" -o audit.yaml
polyflow run ./audit.yaml -i "$(cat src/api.py)"

# Or use a built-in workflow
polyflow run code-review-multi-model -i "$(git diff HEAD~1)"
polyflow run security-audit -i "$(cat src/auth.py)"
polyflow run cross-validate -i "your design or problem statement"

# Run headlessly in CI/CD
polyflow run <workflow> --ci -i "..."

# Browse 22 built-in workflows
polyflow list
polyflow list --tag security
```

## Workflow selection

| Task | Workflow |
|---|---|
| Code review | `code-review-multi-model` |
| Security scan | `security-audit` |
| Cross-validate a plan | `cross-validate` |
| Bug triage | `bug-triage` |
| Generate tests | `test-generation` |
| PR description | `pr-description` |

## How consensus works

Each `type: parallel` step sends the same prompt to multiple models simultaneously. The `aggregate` block synthesizes results:

- `mode: vote` — only findings all models agree on (high confidence)
- `mode: diff` — where models disagree (needs review)
- `mode: summary` — one model synthesizes all outputs

## Custom workflow example

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
    aggregate:
      mode: vote
      model: claude
      prompt: |
        Multiple models independently reviewed this.
        Mark items all models flagged as HIGH CONFIDENCE.
        {{aggregated}}
```

Run it: `polyflow run ./my-consensus-review.yaml -i "your input"`

Any [OpenRouter model ID](https://openrouter.ai/models) works in the `model` field — 290+ models available.

## GitHub Actions integration

```yaml
- uses: celesteimnskirakira/polyflow-ai@v1
  with:
    workflow: code-review-multi-model
    input: ${{ steps.diff.outputs.content }}
    openrouter-api-key: ${{ secrets.OPENROUTER_API_KEY }}
```
