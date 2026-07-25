# Enforcement Patterns

How to wire the Karpathy principles into your workflow so they're enforced, not just documented.

## Level 1 — Passive (read-only)

Install the plugin. The SKILL.md loads into every Claude Code session as context. The LLM reads it and (usually) follows it.

```
/plugin install karpathy-coder@claude-code-skills
```

**Effectiveness:** ~60%. The LLM sometimes forgets under pressure or for long tasks.

## Level 2 — Active review (on demand)

Run `/karpathy-check` before committing. The review agent catches what the LLM missed.

```
# In Claude Code
/karpathy-check

# Or directly from shell
python scripts/complexity_checker.py src/ --threshold strict
python scripts/diff_surgeon.py
```

**Effectiveness:** ~85%. Catches most violations. Requires the user to remember to run it.

## Level 3 — Automated gate (hook)

Wire `hooks/karpathy-gate.sh` as a pre-commit hook. Non-blocking (warns, doesn't reject) but visible.

### Via Husky (Node.js projects)

```bash
npx husky add .husky/pre-commit "bash path/to/karpathy-gate.sh"
```

### Via Claude Code settings

```json
// .claude/settings.json
{
  "hooks": {
    "PostToolUse": [{
      "matcher": "Bash",
      "hooks": [{
        "type": "command",
        "command": "${CLAUDE_PLUGIN_ROOT}/hooks/karpathy-gate.sh"
      }]
    }]
  }
}
```

### Via pre-commit framework

```yaml
# .pre-commit-config.yaml
repos:
  - repo: local
    hooks:
      - id: karpathy-complexity
        name: Karpathy complexity check
        entry: python engineering/karpathy-coder/scripts/complexity_checker.py
        language: python
        types: [python]
        args: [--threshold, medium]
      - id: karpathy-diff
        name: Karpathy diff surgeon
        entry: python engineering/karpathy-coder/scripts/diff_surgeon.py
        language: python
        always_run: true
```

**Effectiveness:** ~95%. Violations get flagged before they enter the codebase.

## Level 4 — CI integration

Add the tools to your CI pipeline so PRs get Karpathy-reviewed automatically.

### GitHub Actions

```yaml
# .github/workflows/karpathy-review.yml
name: Karpathy Review
on: [pull_request]

jobs:
  karpathy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      - uses: actions/setup-python@v5
        with:
          python-version: "3.11"
      - name: Complexity check
        run: |
          python engineering/karpathy-coder/scripts/complexity_checker.py \
            $(git diff --name-only origin/main...HEAD | grep -E '\.(py|ts|tsx)$' | tr '\n' ' ') \
            --threshold medium --json > complexity.json
      - name: Diff noise check
        run: |
          python engineering/karpathy-coder/scripts/diff_surgeon.py \
            --diff origin/main...HEAD --json > noise.json
      - name: Report
        run: |
          echo "## Karpathy Review" >> $GITHUB_STEP_SUMMARY
          python -c "
          import json
          c = json.load(open('complexity.json'))
          n = json.load(open('noise.json'))
          print(f'Complexity: {c[\"average_score\"]}/100 ({c[\"total_findings\"]} findings)')
          print(f'Diff noise: {n[\"noise_ratio\"]*100:.0f}% ({n[\"verdict\"]})')
          " >> $GITHUB_STEP_SUMMARY
```

## Team adoption

1. **Start with Level 1** for a week. Let the team see the principles in action.
2. **Add Level 2** when reviewing PRs. Run `/karpathy-check` on every PR.
3. **Add Level 3** when the team agrees the principles are useful. Gate commits.
4. **Add Level 4** for repos with multiple contributors or LLM-heavy workflows.

**Anti-pattern:** Going straight to Level 4 without team buy-in. The principles are opinionated — teams should experience them before enforcing them.
