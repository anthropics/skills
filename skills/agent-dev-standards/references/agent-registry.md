# Agent Registry
Single source of truth for all Agent metadata and dependencies.
## Registry Schema (registry.yaml)
```yaml
agents:
  - name: code-reviewer
    version: 2.1.0
    description: Automated code review agent
    prompt_ref: agents/code-reviewer/prompt.md@1.2.0
    tools:
      - search_code
      - read_file
      - comment
    dependencies:
      - shared/coding-standards@1.1.0
      - shared/output-format@2.0.0
    evaluation:
      golden_suite: tests/golden/code-reviewer/
      min_score: 0.85
    cost_baseline:
      input_tokens: 2500
      output_tokens: 800
      cost_per_call: 0.012
    owner: team-ai
    tags: [production, code-review]
```
## Dependency Impact Analysis
When a shared prompt changes, the registry answers: which agents depend on it, what version do they pin, which need re-evaluation.
## Registry Operations
- Register: Add new agent entry
- Update: Bump version, update dependency refs
- Impact: List affected agents for a given dependency change
- Validate: Check all prompt_refs exist and versions match