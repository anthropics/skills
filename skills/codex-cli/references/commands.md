# Codex CLI - Comprehensive Command Reference

Complete reference for all Codex CLI flags, options, and workflows.

## Table of Contents

1. [Basic Commands](#basic-commands)
2. [Model Selection](#model-selection)
3. [Reasoning Effort](#reasoning-effort)
4. [Output Formats](#output-formats)
5. [Safety & Approval](#safety--approval)
6. [Advanced Options](#advanced-options)
7. [Workflows](#workflows)
8. [Error Handling](#error-handling)
9. [Performance & Cost](#performance--cost)
10. [CI/CD Integration](#cicd-integration)

---

## Basic Commands

### Interactive Mode (REPL)

```bash
# Simple prompt with approval prompts
codex "explain the repo layout"

# Interactive session (stays open for multiple prompts)
codex

# Exit interactive session
exit
# or Ctrl+C
```

**Use when:** Exploring, iterating, or wanting confirmation before actions.

### Non-Interactive Mode (Batch)

```bash
# Execute without prompts
codex exec "generate unit tests for src/utils.py"

# Non-interactive with output file
codex exec -o tests.py "generate tests"

# Non-interactive piped input
echo "explain src/router.ts" | codex exec -
```

**Use when:** Scripting, CI/CD, or automation.

### Basic Syntax

```bash
codex [options] [command]

# Options come before command
codex -m gpt-5 --reasoning high "your prompt"

# Command can be a prompt or -
codex exec "your prompt"
codex exec - < prompt.txt
```

---

## Model Selection

### Available Models

| Model | Best For | Context | Reasoning Levels | Cost |
|---|---|---|---|---|
| **gpt-5-codex** | Complex code work, architecture | Up to 4096 tokens | low, medium, high | Higher |
| **gpt-5** | General tasks, simple code, docs | Up to 16000 tokens | minimal, low, medium, high | Medium |
| **gpt-5-mini** | Quick tasks, simple edits | Up to 4096 tokens | minimal, low, medium | Lower |

### Model Selection by Task

```bash
# Architecture/deep code review → gpt-5-codex + high reasoning
codex -m gpt-5-codex --reasoning high "Audit src/ for security issues"

# Non-trivial refactoring → gpt-5-codex + medium reasoning
codex -m gpt-5-codex --reasoning medium "Refactor to dependency injection"

# Small patches/docs → gpt-5 + minimal/low reasoning
codex -m gpt-5 --reasoning low "Add docstrings to utils/"

# Quick extraction → gpt-5 + minimal reasoning
codex -m gpt-5 --reasoning minimal --json "Extract endpoints from swagger.yaml"
```

### Set Default Model

```toml
# ~/.codex/config.toml
model = "gpt-5-codex"
reasoning_effort = "medium"
```

Override per command:
```bash
codex -m gpt-5 "your prompt"
codex --model gpt-5-codex "your prompt"
```

---

## Reasoning Effort

Reasoning effort controls how long the model thinks before responding.

### Reasoning Levels

**Minimal** (gpt-5 only)
- Fastest, lowest cost
- Instant responses
- Use for: simple tasks, quick extraction

```bash
codex -m gpt-5 --reasoning minimal "Extract JSON from logs"
```

**Low**
- Fast, low cost
- Brief thinking
- Use for: simple code, straightforward edits

```bash
codex -m gpt-5 --reasoning low "Add error handling to this function"
```

**Medium (default)**
- Balanced reasoning and speed
- 5-30 second thinking
- Use for: most coding tasks, standard refactoring

```bash
codex -m gpt-5-codex --reasoning medium "Refactor this module"
```

**High**
- Deep reasoning, higher cost
- 30-120 second thinking
- Use for: complex problems, architecture, security

```bash
codex -m gpt-5-codex --reasoning high "Design microservices architecture"
```

### When to Use Each Level

```bash
# High reasoning: Complex architectural decisions
codex -m gpt-5-codex --reasoning high "Plan migration from monolith to microservices"

# Medium reasoning: Typical code reviews and refactoring (default)
codex -m gpt-5-codex "Review src/ for security issues"

# Low reasoning: Simple edits and fixes
codex -m gpt-5 --reasoning low "Fix the indentation in this file"

# Minimal reasoning: Extraction and formatting
codex -m gpt-5 --reasoning minimal "Convert this YAML to JSON"
```

---

## Output Formats

### Text Output (Default)

```bash
# Output to stdout
codex exec "your prompt"

# Output to file
codex exec -o output.txt "your prompt"
codex exec --output output.txt "your prompt"

# Strip ANSI codes (for clean text files)
codex exec --color=never "your prompt" > output.txt

# Show progress (default: true)
codex exec --progress=false "your prompt"  # suppress progress
```

**Use when:** Human reading, logs, documentation.

### JSON Output

```bash
# Stream JSON events (JSONL format - one JSON object per line)
codex exec --json "your prompt"

# Save JSON events to file
codex exec --json --output events.jsonl "your prompt"

# Parse last event (the final response)
codex exec --json "your prompt" | tail -n1 | jq .

# Extract just the content from final event
codex exec --json "your prompt" | tail -n1 | jq -r '.content'

# Pretty-print final response
codex exec --json "your prompt" | tail -n1 | jq '.'
```

**JSON Event Structure:**
```json
{
  "type": "message|done|error",
  "content": "text response",
  "role": "assistant",
  "timestamp": "2025-01-01T00:00:00Z"
}
```

**Use when:** Parsing in scripts, pipelines, data extraction.

### JSONL Stream

Raw event stream useful for real-time processing:

```bash
# Monitor events as they arrive
codex exec --json "your prompt" | while read line; do
  echo "Event: $line" | jq .type
done

# Count events
codex exec --json "your prompt" | jq -s 'length'

# Extract all thinking steps
codex exec --json "your prompt" | jq -s 'map(select(.type=="thinking")) | .[] .content'
```

### Final Output Only

```bash
# Save only final message (not progress)
codex exec -o output.txt "your prompt"

# vs. redirect which may include progress
codex exec "your prompt" > output.txt  # may include progress bars
```

---

## Safety & Approval

### Approval Modes

**Ask (Default)**
```bash
codex "delete all test files"
# Prompts for confirmation before dangerous actions

# Override with --full-auto
codex --full-auto "delete all test files"
```

**Full Auto**
```bash
codex --full-auto "make these changes"
# No prompts, executes all changes

# Set in config
# approval_mode = "full-auto"
```

**Dangerous Mode (YOLO)**
```bash
codex --yolo "make dangerous changes"
# Use ONLY in fully sandboxed environments
# Not recommended for most use cases
```

### Risky Action Examples

Actions that may prompt for confirmation:
- File deletion or modification
- Database schema changes
- Security/permission changes
- External API calls
- System-level changes

### Safe Automation Strategy

```bash
#!/bin/bash
set -e

# Plan first (review output)
codex exec -o plan.md -m gpt-5-codex --reasoning high "Plan: migrate database"

# Review the plan
cat plan.md
read -p "Continue? (y/n)" -n 1
[[ $REPLY =~ ^[Yy]$ ]] || exit 1

# Execute with approval
codex exec --full-auto -m gpt-5-codex "Execute migration based on this plan: $(cat plan.md)"
```

---

## Advanced Options

### Color & Formatting

```bash
# Disable color output
codex --color=never "your prompt"
codex --no-color "your prompt"

# Enable color (default)
codex --color "your prompt"

# Control progress display
codex --progress "your prompt"      # show progress (default)
codex --progress=false "your prompt" # hide progress
```

### Timeout

```bash
# Set timeout in seconds
codex --timeout 300 "your prompt"  # 5 minutes

# Default is 120 seconds
# Some complex reasoning tasks may need longer
```

### Token Limits

```bash
# Set max tokens for response
codex --max-tokens 2000 "your prompt"

# Models have different limits:
# gpt-5-codex: up to 4096
# gpt-5: up to 16000
```

### Temperature (Randomness)

```bash
# Default: 0.7 (balanced)
# Lower (0.0): deterministic, focused
# Higher (2.0): more random, creative

codex --temperature 0.3 "write a unit test"     # focused/deterministic
codex --temperature 0.7 "explain the code"      # balanced (default)
codex --temperature 1.5 "brainstorm ideas"      # creative
```

### Top-P (Diversity)

```bash
# Default: 1.0
# Lower (0.1): diverse but focused
# Higher (1.0): all tokens considered

codex --top-p 0.9 "your prompt"
```

---

## Workflows

### Architecture Planning

```bash
#!/bin/bash

echo "1. Creating detailed plan..."
codex exec \
  -o plan.md \
  -m gpt-5-codex \
  --reasoning high \
  "Plan: migrate from monolith to microservices
   Include:
   1. Risk analysis
   2. Step-by-step implementation
   3. Testing strategy
   4. Rollback plan"

echo "2. Review plan..."
cat plan.md

echo "3. Creating implementation guide..."
codex exec \
  -o implementation.md \
  -m gpt-5-codex \
  --reasoning medium \
  "Based on this plan, create detailed implementation guide: $(cat plan.md)"

echo "Done! Check plan.md and implementation.md"
```

### Code Review Workflow

```bash
#!/bin/bash

echo "1. Analyze codebase..."
ISSUES=$(codex exec --json \
  -m gpt-5-codex \
  --reasoning high \
  "Security review of src/:
   1. Input validation issues
   2. Authentication gaps
   3. Injection vulnerabilities
   4. Sensitive data exposure" | tail -n1 | jq -r '.content')

echo "2. Generate report..."
cat > review-report.md << EOF
# Security Review Report
Generated: $(date)

## Issues Found
$ISSUES

## Recommendations
[recommendations here]
EOF

echo "3. Summary:"
wc -l review-report.md
```

### Refactoring Workflow

```bash
#!/bin/bash

# 1. Analyze current code
echo "Analyzing current code structure..."
codex exec \
  -o analysis.md \
  "Analyze src/handlers.ts:
   - Current design patterns
   - Testability score (1-10)
   - Dependencies and coupling
   - Refactoring opportunities"

# 2. Propose refactoring
echo "Proposing refactoring..."
codex exec \
  -o refactoring-plan.md \
  -m gpt-5-codex \
  --reasoning high \
  "Propose refactoring for src/handlers.ts:
   Goal: improve testability and reduce coupling

   For each change:
   - Before/after code
   - Migration steps
   - Breaking changes"

# 3. Generate tests for new structure
echo "Generating tests..."
codex exec \
  -o test-plan.ts \
  "Generate comprehensive tests for the refactored handlers based on:
   $(cat refactoring-plan.md)"
```

### Documentation Workflow

```bash
#!/bin/bash

# 1. Extract API information
echo "Extracting API endpoints..."
codex exec \
  --json \
  "Extract all REST endpoints from src/api/:
   Format as JSON with: path, method, params, description"

# 2. Generate documentation
echo "Generating documentation..."
codex exec \
  -o API.md \
  "Write API documentation based on these endpoints:
   $(codex exec --json "Extract endpoints from src/api/" | tail -n1 | jq '.content')"

# 3. Add examples
echo "Adding examples..."
codex exec \
  -o API-WITH-EXAMPLES.md \
  "Add practical request/response examples to:
   $(cat API.md)"
```

### Debugging Workflow

```bash
#!/bin/bash

# 1. Collect information
echo "Analyzing error..."

# Run tests to capture errors
npm test 2>&1 | head -50 > errors.log

# 2. Ask Codex to diagnose
codex exec \
  -o diagnosis.md \
  -m gpt-5-codex \
  --reasoning high \
  "Diagnose these test failures:
   $(cat errors.log)

   Provide:
   1. Root cause analysis
   2. Why each test is failing
   3. Step-by-step fixes
   4. Verification steps"

echo "Diagnosis saved to diagnosis.md"
```

---

## Error Handling

### Common Errors

**Authentication Error**
```
Error: not authenticated
Fix: Run `codex login` first
```

**Model Not Available**
```
Error: model not found
Fix: Check spelling, use `codex models list`
```

**Timeout**
```
Error: request timeout
Fix: Use `codex --timeout 300 "prompt"` for longer timeout
```

**Rate Limiting**
```
Error: rate limited
Fix: Wait before retrying, or spread requests over time
```

### Retry Logic

```bash
#!/bin/bash

# Simple retry with exponential backoff
retry() {
  local n=1
  local max=5
  local delay=2
  while true; do
    "$@" && break || {
      if [[ $n -lt $max ]]; then
        ((n++))
        echo "Attempt $n failed. Waiting ${delay}s..."
        sleep $delay
        delay=$((delay * 2))
      else
        return 1
      fi
    }
  done
}

# Usage
retry codex exec "your prompt"
```

### Error Recovery

```bash
#!/bin/bash

# Check if previous run succeeded
if [ -f output.md ]; then
  echo "Task already completed"
  exit 0
fi

# Run task with error handling
if codex exec -o output.md "your prompt"; then
  echo "Success!"
else
  echo "Failed. Trying with different parameters..."
  codex exec -o output.md -m gpt-5 "your prompt"
fi
```

---

## Performance & Cost

### Cost Estimation

| Model | Reasoning | Est. Cost | Speed | Use For |
|---|---|---|---|---|
| gpt-5-mini | minimal | $$ | Very Fast | Quick tasks |
| gpt-5 | minimal | $ | Fast | Simple tasks |
| gpt-5 | medium | $$$ | Medium | Standard tasks |
| gpt-5-codex | medium | $$$$ | Medium | Code work |
| gpt-5-codex | high | $$$$$$ | Slow | Complex work |

### Cost Optimization

```bash
# Use minimal reasoning for simple tasks
codex -m gpt-5 --reasoning minimal "Extract JSON"

# Use lower-cost model first, upgrade if needed
codex -m gpt-5 "your prompt" || codex -m gpt-5-codex "your prompt"

# Cache results for similar tasks
# Store output to avoid re-running
if [ ! -f output.md ]; then
  codex exec -o output.md "expensive prompt"
fi
```

### Performance Tips

```bash
# Faster: disable progress output
codex exec --progress=false "your prompt"

# Faster: use lower reasoning level
codex --reasoning low "your prompt"

# Faster: use gpt-5-mini for simple tasks
codex -m gpt-5-mini "your prompt"

# Parallel processing: run multiple prompts concurrently
codex exec -o result1.txt "task 1" &
codex exec -o result2.txt "task 2" &
wait
```

---

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Code Quality

on: [pull_request]

jobs:
  codex-review:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install Codex
        run: npm install -g @openai/codex

      - name: Setup Auth
        run: echo "${{ secrets.OPENAI_API_KEY }}" | codex login --with-api-key

      - name: Run Code Review
        run: |
          codex exec \
            -o review.md \
            -m gpt-5-codex \
            --reasoning high \
            "Review these changes for security issues:
             $(git diff HEAD~1)"

      - name: Comment on PR
        uses: actions/github-script@v6
        with:
          script: |
            const review = require('fs').readFileSync('review.md', 'utf8');
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: review
            });
```

### GitLab CI Example

```yaml
code-review:
  stage: quality
  script:
    - npm install -g @openai/codex
    - echo "$OPENAI_API_KEY" | codex login --with-api-key
    - |
      codex exec \
        -o review.md \
        -m gpt-5-codex \
        --reasoning high \
        "Review changes in this branch"
    - cat review.md
  artifacts:
    paths:
      - review.md
```

### Pre-Commit Hook

```bash
#!/bin/bash
# .git/hooks/pre-commit

if [ -f .codex-precommit-enabled ]; then
  echo "Running Codex pre-commit check..."

  # Check staged files
  STAGED=$(git diff --cached --name-only)

  codex exec \
    -o precommit-review.txt \
    -m gpt-5 \
    --reasoning low \
    "Quick review of staged changes - identify obvious issues:
     Files: $STAGED
     Changes: $(git diff --cached)"

  # Show results
  cat precommit-review.txt

  # Optionally fail on critical issues
  if grep -i "critical\|dangerous" precommit-review.txt; then
    echo "Critical issues found. Commit aborted."
    exit 1
  fi
fi
```

### Batch Processing

```bash
#!/bin/bash

# Process multiple files with progress tracking
for file in src/**/*.ts; do
  echo "Processing $file..."

  codex exec \
    -o "review-$(basename $file).md" \
    --progress=false \
    "Review $file for potential bugs"

  echo "✓ $file"
done

echo "All reviews complete!"
```

---

## Configuration File Reference

**Location:** `~/.codex/config.toml`

```toml
# Model (gpt-5-codex, gpt-5, gpt-5-mini)
model = "gpt-5-codex"

# Reasoning level (low, medium, high, minimal)
reasoning_effort = "medium"

# Approval mode (ask, full-auto)
approval_mode = "ask"

# Output format (text, json, jsonl)
format = "text"

# Color output (true/false)
color = true

# Show progress (true/false)
progress = true

# Timeout in seconds
timeout = 120

# Max tokens per response
max_tokens = 4096

# Temperature (0.0-2.0, default 0.7)
temperature = 0.7

# Top-P (0.0-1.0, default 1.0)
top_p = 1.0

# Verbose logging (true/false)
verbose = false
```

---

## Quick Reference Table

| Task | Command | Model | Reasoning |
|---|---|---|---|
| Code review (security) | `./scripts/codex-review.sh` | gpt-5-codex | high |
| Architecture planning | `./scripts/codex-plan.sh` | gpt-5-codex | high |
| Refactoring analysis | `./scripts/codex-refactor.sh` | gpt-5-codex | medium |
| Documentation | `./scripts/codex-document.sh` | gpt-5 | medium |
| Debug analysis | `./scripts/codex-debug.sh` | gpt-5-codex | medium |
| Quick fixes | `codex` | gpt-5 | low |
| Data extraction | `codex --json` | gpt-5 | minimal |
