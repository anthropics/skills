# CI/CD Workflows and Security Scanning Guide

Comprehensive documentation of GitHub Actions workflows for automated security scanning, validation, and quality checks.

## Overview

This repository uses GitHub Actions for continuous integration with a focus on code security, documentation quality, and repository consistency.

### Workflows

| Workflow | Trigger | Purpose | Tools |
|----------|---------|---------|-------|
| **CodeQL Advanced** | Push to main, PRs, weekly schedule | Security scanning for JavaScript/TypeScript and Python | GitHub CodeQL |
| **Lint and Validate** | Changes to docs/config, PRs | YAML linting, Markdown formatting, JSON schema validation, SKILL.md structure | yamllint, markdownlint, custom validators |
| **SLSA Generic Generator** | Manual dispatch, releases | Supply chain integrity and provenance generation | SLSA Framework v1.4.0 |

## CodeQL Security Scanning

### Configuration

**File:** `.github/workflows/codeql-optimized.yml`

**Languages analyzed:**
- JavaScript/TypeScript
- Python

**Query packs enabled:**
- `security-and-quality` — Detects security vulnerabilities and code quality issues

**Schedule:** 
- On every push to main
- On all pull requests
- Weekly (Monday, 2 AM UTC)

### Features

✅ **Up-to-date actions** — Uses v3 and v4 (latest stable versions)
✅ **Security + quality queries** — Enables `security-and-quality` pack for comprehensive analysis
✅ **SARIF upload** — Uploads results to GitHub's Security tab for visibility
✅ **Fail-safe job** — Explicit check for critical findings
✅ **Full fetch** — Analyzes complete history for better context

### SARIF Upload

CodeQL results are automatically uploaded to GitHub Security tab (Actions → Security → Code scanning alerts). This provides:
- Dashboard of all found issues
- Severity levels (Critical, High, Medium, Low)
- Detailed explanation and fix recommendations
- Integration with GitHub's branch protection

### Handling CodeQL Failures

**If CodeQL analysis fails on a PR:**

1. **Check the Security tab** for detailed findings
2. **Review findings** to understand the issue
3. **Common issues:**
   - Missing variable declarations
   - Unchecked external input (potential injection)
   - Type mismatches
   - Dead code
4. **Fix** the code or apply suggested remediation
5. **Re-run** the workflow (automatically on new commits)

**For false positives:**
- Add `// lgtm` comment (for simple suppressions)
- Use `.lgtm.yml` for per-repository suppression config
- Document why it's a false positive in commit message

## Linting and Validation Workflow

### Configuration

**File:** `.github/workflows/lint-and-validate.yml`

**Scope:** Runs on changes to:
- `skills/**/*.md` — SKILL.md and reference documentation
- `skills/**/*.yml` — Configuration files
- `skills/**/*.json` — Evals and example files
- `*.md` — Repository documentation
- `.github/workflows/*.yml` — CI/CD workflows

### Checks

#### 1. YAML Linting (`yamllint`)

**Configuration:** `.github/workflows/lint-and-validate.yml` (inline config)

**Rules:**
- Line length max 120 chars (warning above that)
- Consistent indentation
- Valid YAML structure
- Comment formatting

**Directories scanned:**
- `skills/` — All SKILL.md and config files
- `.github/workflows/` — This CI/CD configuration

**Common YAML issues:**
```yaml
# ❌ Wrong: Inconsistent indentation
- name: Test
  run: echo "hello"
    echo "world"  # Extra indent!

# ✅ Correct: Consistent indentation
- name: Test
  run: |
    echo "hello"
    echo "world"

# ❌ Wrong: Trailing spaces
- name: Test  [spaces here]
  run: echo test

# ✅ Correct: No trailing spaces
- name: Test
  run: echo test
```

#### 2. Markdown Linting (`markdownlint`)

**Configuration:** `.markdownlintrc.json`

**Rules:**
- Consistent heading style
- Line length 120 chars (soft limit)
- No hard tabs
- No trailing spaces
- Proper list formatting

**Common Markdown issues:**
```markdown
# ❌ Wrong: Inconsistent heading levels
# Heading 1
### Heading 3  (skipped level 2!)

# ✅ Correct: Consistent heading hierarchy
# Heading 1
## Heading 2
### Heading 3

# ❌ Wrong: Multiple spaces between words
This  has   extra    spaces

# ✅ Correct: Single spaces
This has single spaces
```

#### 3. Evaluation File Validation (`validate-evals`)

**Validates:** All `skills/*/evals/evals.json` files

**Required fields (root level):**
- `skill_name` — Unique identifier
- `evals` — Array of evaluation objects

**Required fields (each eval):**
- `id` — Unique eval ID (e.g., "eval-1")
- `name` — Descriptive name
- `prompt` — User task prompt
- `expected_output` — Description of success
- `expectations` — Array of assertion criteria

**Schema example:**
```json
{
  "skill_name": "my-skill",
  "evals": [
    {
      "id": "eval-1",
      "name": "simple-workflow",
      "prompt": "User request here",
      "expected_output": "What success looks like",
      "expectations": [
        "Specific assertion 1",
        "Specific assertion 2"
      ]
    }
  ]
}
```

#### 4. SKILL.md Structure Validation (`validate-skills`)

**Validates:** All `skills/*/SKILL.md` files

**Required elements:**

1. **YAML frontmatter** (between `---` delimiters)
   ```yaml
   ---
   name: skill-identifier
   description: What this skill does
   license: Apache 2.0
   ---
   ```

2. **Required frontmatter fields:**
   - `name` — Lowercase with hyphens (e.g., `my-skill`)
   - `description` — Clear description of purpose and triggers

3. **Optional frontmatter fields:**
   - `license` — Apache 2.0, Proprietary, etc.
   - `compatibility` — Dependencies or requirements

4. **Content section** — Markdown body after frontmatter

**Common issues:**
```markdown
# ❌ Wrong: Missing frontmatter
# Skill Name
Content here...

# ✅ Correct: Valid frontmatter
---
name: skill-name
description: What this skill does
---

# Skill Name
Content here...

# ❌ Wrong: Name with spaces and capitals
name: My Skill

# ✅ Correct: Lowercase with hyphens
name: my-skill
```

## Configuration Files

### `.markdownlintrc.json`

Markdown linting configuration with settings for:
- Line length limits (120 chars, soft)
- Heading style consistency
- List marker spacing
- No inline HTML in most cases (allowed for flexibility)
- Code fence language requirements

### `.github/workflows/*.yml`

**Best practices for workflow files:**
- Keep lines under 120 chars
- Use consistent indentation (2 spaces)
- Include descriptive step names
- Add comments explaining complex logic
- Use job dependencies with `needs:`
- Always specify action versions (never use `@main`)

## Optimization Recommendations

### 1. Caching for Faster Builds

**Current:** CodeQL re-analyzes entire codebase each run
**Suggested:** Enable CodeQL caching (GitHub Actions feature)
```yaml
- name: Initialize CodeQL
  uses: github/codeql-action/init@v3
  with:
    languages: ${{ matrix.language }}
    # Caching available in v3+
```

### 2. Separate CI/CD for Different File Types

**Current:** Single monolithic workflow
**Suggested:** Separate workflows for:
- Security scanning (CodeQL) — separate from validation
- Validation (linting, schema) — faster, non-blocking
- Provenance (SLSA) — only on releases

This allows validation checks to fail without blocking security scanning.

### 3. Required Status Checks

Recommended branch protection rules:
- ✅ CodeQL analysis must pass
- ⚠️ Linting should pass (or warning-only)
- ⚠️ SLSA provenance (informational only)

Configure in Settings → Branches → Branch Protection Rules.

### 4. Notifications for Security Findings

**Currently:** Results visible only in GitHub Security tab
**Suggested improvements:**
- Email notifications on critical findings
- Slack notifications to #security channel
- Automatic issue creation for critical findings

### 5. Dependency Updates

**Current:** Manual action version updates
**Suggested:** Enable Dependabot for Actions
```yaml
# In .github/dependabot.yml
version: 2
updates:
  - package-ecosystem: "github-actions"
    directory: "/"
    schedule:
      interval: "weekly"
```

### 6. License Scanning

**Current:** No license scanning
**Suggested:** Add FOSSA or similar for dependency licenses
- Ensure all dependencies have compatible licenses
- Prevent GPL/incompatible licenses in proprietary code

## Troubleshooting

### CodeQL Analysis Slow or Times Out

**Cause:** Large codebase or complex logic
**Solutions:**
- Use larger runners (GitHub Teams/Enterprise only)
- Disable analysis for non-critical languages
- Use `fetch-depth: 0` to get full history (as currently configured)

### Markdown Linting Produces Too Many Warnings

**Cause:** Overly strict config
**Solution:** Adjust `.markdownlintrc.json`
```json
"MD013": {
  "line_length": 120,
  "level": "warning"
}
```

### evals.json Validation Fails

**Cause:** Missing required fields or incorrect format
**Solution:** Verify structure matches schema in EVALUATION_GUIDE.md

Example valid file:
```json
{
  "skill_name": "test-skill",
  "evals": [
    {
      "id": "eval-1",
      "name": "test-case",
      "prompt": "Test prompt",
      "expected_output": "Expected output",
      "expectations": ["assertion 1"]
    }
  ]
}
```

### SKILL.md Validation Fails

**Cause:** Missing frontmatter or invalid format
**Solution:** Ensure file starts with:
```yaml
---
name: skill-name
description: Clear description of what this skill does
---
```

## Running Workflows Manually

### Trigger CodeQL on Demand
```bash
# Via GitHub CLI
gh workflow run codeql-optimized.yml

# Or via GitHub web UI:
# Actions → CodeQL Advanced → Run workflow
```

### Trigger Linting on Demand
```bash
# Via GitHub CLI
gh workflow run lint-and-validate.yml
```

### Trigger SLSA Provenance on Demand
```bash
# Via GitHub CLI
gh workflow run generator-generic-ossf-slsa3-publish.yml
```

## Best Practices

✅ **Do:**
- Run validation checks on every PR
- Review CodeQL findings before merging
- Keep actions up-to-date with Dependabot
- Document custom validation rules
- Test workflow changes in a feature branch first

❌ **Don't:**
- Ignore CodeQL warnings (especially security findings)
- Use `@main` or `@latest` for action versions
- Allow validation failures to merge (set as required)
- Store secrets in workflow files (use GitHub Secrets)
- Modify workflows without testing

## Related Documentation

- **EVALUATION_GUIDE.md** — Evaluation framework and testing
- **CLAUDE.md** — Repository structure and guidelines
- **TESTING_EXAMPLES.md** — Concrete test examples

---

**Last Updated:** August 9, 2026  
**Workflows Location:** `.github/workflows/`  
**Configuration:** `.markdownlintrc.json`

For questions or issues with CI/CD, check GitHub Actions logs or create an issue in the repository.
