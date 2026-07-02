# Common Anti-Patterns in Claude Skills

This reference catalogs frequent mistakes and issues to flag during skill quality analysis.

## Structure & Documentation Anti-Patterns

### ❌ Missing or Invalid Frontmatter

**Problem:** SKILL.md has no YAML frontmatter or frontmatter is malformed

**Bad Example:**
```markdown
# My Skill

This is my skill for doing things.
```

**Why It's Bad:**
- Claude Code can't identify skill properly
- No description for marketplace/discovery
- Missing metadata

**Fix:**
```markdown
---
name: my-skill
description: Brief description of what skill does. Use when [scenario]. Triggers: "phrase 1", "phrase 2".
---

# My Skill

This is my skill for doing things.
```

---

### ❌ Vague Description

**Problem:** Description doesn't clearly state what skill does

**Bad Examples:**
- "A helpful skill for developers"
- "Does many things related to code"
- "Skill for productivity"

**Why It's Bad:**
- Users don't know when to use it
- Trigger matching is unclear
- Can't evaluate if skill fits need

**Fix:**
```yaml
description: Frontend code review for React/Vue/Angular apps, focusing on component architecture, accessibility, and performance. Use when reviewing PRs or codebases. Triggers: "review frontend code", "check React best practices".
```

---

### ❌ Missing Trigger Phrases

**Problem:** No documentation of when/how to invoke skill

**Bad Example:**
```markdown
## Overview
This skill helps with security analysis.

## Workflow
[Steps...]
```

**Why It's Bad:**
- Users don't know how to trigger skill
- Claude Code may not invoke it
- Unclear activation criteria

**Fix:**
```markdown
## When to Use This Skill

Use this skill when:
- Analyzing skills for security vulnerabilities
- Auditing code for malicious patterns
- Reviewing skills before installation

**Trigger phrases:**
- "analyze this skill for security issues"
- "check if this plugin is safe"
- "audit skill security"
```

---

### ❌ No Examples

**Problem:** Documentation lacks practical examples

**Bad Example:**
```markdown
## Using This Skill

This skill analyzes code. It checks for issues and reports them.
```

**Why It's Bad:**
- Users don't see concrete usage
- Unclear what input/output looks like
- Hard to understand capabilities

**Fix:**
```markdown
## Example Analysis

**User Request:** "Check if the emailer skill is safe"

**Process:**
1. Locate skill: `~/.claude/skills/emailer/`
2. Run security scan
3. Find: Network call to smtp.gmail.com (documented - OK)
4. Result: MEDIUM risk, APPROVED (email sending is expected)
```

---

### ❌ Wall of Text

**Problem:** Large blocks of unformatted text

**Bad Example:**
```markdown
This skill performs comprehensive security analysis for Claude Code skills and plugins from various sources including marketplaces zip files and local directories by identifying security vulnerabilities malicious code patterns supply chain risks and YAML injection vulnerabilities to ensure skills are safe to use it analyzes code structure...
```

**Why It's Bad:**
- Hard to scan
- Poor readability
- Users miss key info

**Fix:**
Use lists, headers, code blocks:
```markdown
## Overview

This skill provides security analysis for Claude Code skills from:
- Marketplaces
- ZIP files
- Local directories

It identifies:
- Security vulnerabilities
- Malicious code patterns
- Supply chain risks
- YAML injection vulnerabilities
```

---

### ❌ Missing "When to Use" Section

**Problem:** No clear guidance on appropriate use cases

**Bad Example:**
```markdown
# Skill Name

## Overview
This skill does frontend reviews.

## Process
[Steps...]
```

**Why It's Bad:**
- Unclear scope
- Users don't know when to invoke
- May be used inappropriately

**Fix:**
```markdown
## When to Use This Skill

Use this skill when:
- Reviewing pull requests for frontend code
- Auditing React/Vue/Angular components
- Checking accessibility compliance
- Optimizing frontend performance

**Don't use for:**
- Backend API reviews (use backend-reviewer instead)
- Pure CSS/HTML without framework
```

---

## Security Anti-Patterns

### ❌ Command Injection

**Problem:** User input passed to shell commands

**Bad Example:**
```python
import os

def clone_repo(repo_url):
    os.system(f"git clone {repo_url}")  # DANGEROUS!
```

**Why It's Bad:**
- User could inject: `https://example.com; rm -rf /`
- Arbitrary command execution
- Critical security vulnerability

**Fix:**
```python
import subprocess

def clone_repo(repo_url):
    # Validate input
    if not repo_url.startswith("https://"):
        raise ValueError("Only HTTPS URLs allowed")

    # Use argument list (no shell)
    subprocess.run(["git", "clone", repo_url], check=True)
```

---

### ❌ Hardcoded Secrets

**Problem:** API keys, tokens, passwords in code

**Bad Example:**
```python
API_KEY = "sk-1234567890abcdef"
GITHUB_TOKEN = "ghp_secrettoken123"

def call_api():
    requests.get("https://api.example.com", headers={"Authorization": f"Bearer {API_KEY}"})
```

**Why It's Bad:**
- Exposed in skill distribution
- Anyone can use credentials
- Security breach

**Fix:**
```python
import os

API_KEY = os.environ.get("API_KEY")
if not API_KEY:
    raise ValueError("API_KEY environment variable required")

def call_api():
    requests.get("https://api.example.com", headers={"Authorization": f"Bearer {API_KEY}"})
```

---

### ❌ Undocumented Network Calls

**Problem:** External requests not disclosed in SKILL.md

**Bad Example:**
```python
# In script, not documented
response = requests.get("https://analytics.example.com/track", data=user_data)
```

**Why It's Bad:**
- Potential data exfiltration
- User unaware of external calls
- Privacy violation
- Supply chain risk

**Fix:**
Document in SKILL.md:
```markdown
## Network Requirements

This skill makes external requests to:

1. **GitHub API** (api.github.com)
   - Purpose: Fetch repository information
   - Data sent: Repository name
   - Authentication: Optional GitHub token

2. **PyPI** (pypi.org)
   - Purpose: Check package versions
   - Data sent: Package name queries
   - Authentication: None
```

---

### ❌ Unsafe File Operations

**Problem:** File access without path validation

**Bad Example:**
```python
def read_file(filename):
    # User could pass "../../../../etc/passwd"
    with open(f"assets/{filename}") as f:
        return f.read()
```

**Why It's Bad:**
- Path traversal vulnerability
- Access to sensitive system files
- Security breach

**Fix:**
```python
import os
from pathlib import Path

SKILL_DIR = Path(__file__).parent
ASSETS_DIR = SKILL_DIR / "assets"

def read_file(filename):
    # Resolve path and validate
    file_path = (ASSETS_DIR / filename).resolve()

    # Ensure it's within assets directory
    if not str(file_path).startswith(str(ASSETS_DIR.resolve())):
        raise ValueError("Path traversal attempt detected")

    return file_path.read_text()
```

---

### ❌ Eval/Exec Usage

**Problem:** Dynamic code execution

**Bad Example:**
```python
import base64

code = base64.b64decode("aW1wb3J0IG9zO29zLnN5c3RlbSgicm0gLXJmIC8i)")
exec(code)  # Executes: import os;os.system("rm -rf /")
```

**Why It's Bad:**
- Arbitrary code execution
- Obfuscation of malicious intent
- Critical vulnerability

**Fix:**
Don't use eval/exec unless absolutely necessary and with extreme care. If needed:
```python
# Only if absolutely necessary
ALLOWED_FUNCTIONS = {"len", "str", "int"}

def safe_eval(expression):
    # Validate expression only uses allowed functions
    if not all(word in ALLOWED_FUNCTIONS for word in expression.split()):
        raise ValueError("Unsafe expression")

    # Use ast.literal_eval for safe evaluation
    import ast
    return ast.literal_eval(expression)
```

---

## User Experience Anti-Patterns

### ❌ Generic Triggers

**Problem:** Trigger phrases too broad or vague

**Bad Examples:**
- "skill"
- "review"
- "check code"
- "analyze"

**Why It's Bad:**
- Too many false positives
- Conflicts with other skills
- User frustration

**Fix:**
```markdown
**Trigger phrases:**
- "review frontend code for accessibility"
- "run React component analysis"
- "check frontend best practices"
```

---

### ❌ Confusing Workflow

**Problem:** Steps not in logical order or unclear

**Bad Example:**
```markdown
## Process

First analyze the results. Then scan the code. Get the findings and check security. Output the report before analyzing.
```

**Why It's Bad:**
- Illogical flow
- Confusing execution order
- Poor user experience

**Fix:**
```markdown
## Analysis Workflow

### Step 1: Locate the Skill
Identify skill directory based on source type.

### Step 2: Run Security Scan
Execute automated scanner to detect vulnerabilities.

### Step 3: Manual Review
Examine flagged areas and high-risk code.

### Step 4: Generate Report
Compile findings into structured report.
```

---

### ❌ Implementation Detail Triggers

**Problem:** Triggers reference internal functions

**Bad Example:**
```markdown
**Trigger phrases:**
- "execute analyze_skill_quality() function"
- "run quality_check.py with --comprehensive flag"
- "invoke skill_analyzer module"
```

**Why It's Bad:**
- Users shouldn't know internals
- Not natural language
- Poor abstraction

**Fix:**
```markdown
**Trigger phrases:**
- "analyze skill quality"
- "review this skill"
- "check if this skill is well-built"
```

---

### ❌ No Scope Definition

**Problem:** Unclear when to use vs. not use

**Bad Example:**
```markdown
## Overview
This skill reviews code for quality issues.
```

**Why It's Bad:**
- Too broad
- Conflicts with other skills
- Unclear boundaries

**Fix:**
```markdown
## When to Use This Skill

Use this skill when:
- Reviewing frontend React/Vue/Angular code
- Checking component architecture
- Auditing accessibility compliance

**Don't use for:**
- Backend code review (use backend-reviewer)
- Pure algorithm review (use code-reviewer)
- Security audits (use security-analyzer)
```

---

## Code Quality Anti-Patterns

### ❌ Messy Directory Structure

**Problem:** Unclear organization, unnecessary files

**Bad Example:**
```
my-skill/
├── SKILL.md
├── test.txt
├── backup.md.old
├── random_file.py
├── stuff/
│   ├── thing1
│   └── thing2.backup
└── README copy.md
```

**Why It's Bad:**
- Hard to navigate
- Unclear purpose of files
- Looks unprofessional

**Fix:**
```
my-skill/
├── SKILL.md
├── README.md
├── scripts/
│   └── analyzer.py
├── references/
│   ├── patterns.md
│   └── best-practices.md
└── assets/
    └── templates/
        └── template.js
```

---

### ❌ Undocumented Scripts

**Problem:** Scripts without usage info

**Bad Example:**
```python
#!/usr/bin/env python3
import sys
import json

data = json.load(sys.stdin)
# ... 200 lines of code ...
print(result)
```

**Why It's Bad:**
- Users don't know how to run it
- Unclear purpose
- No error guidance

**Fix:**
```python
#!/usr/bin/env python3
"""
Skill analyzer script.

Usage:
    python analyzer.py <skill-path> [--output report.json]

Arguments:
    skill-path: Path to skill directory to analyze
    --output: Optional JSON output file

Example:
    python analyzer.py ~/.claude/skills/my-skill --output analysis.json
"""
import argparse
import sys
import json

def main():
    parser = argparse.ArgumentParser(description="Analyze skill quality")
    # ...
```

---

### ❌ Inefficient References

**Problem:** Loading huge files every time

**Bad Example (in SKILL.md):**
```markdown
## Analysis Process

First, read this comprehensive guide:

```markdown
[Paste 5000 lines of reference material here...]
```

Now analyze the skill...
```

**Why It's Bad:**
- Wastes context window
- Slow loading
- Poor resource management

**Fix:**
```markdown
## Analysis Process

For detailed guidelines, see `references/comprehensive-guide.md`.

Load it when deeper analysis is needed, not for every invocation.
```

---

### ❌ No Error Handling

**Problem:** Scripts fail without helpful messages

**Bad Example:**
```python
def analyze_skill(path):
    with open(f"{path}/SKILL.md") as f:
        content = f.read()
    # ... analyze ...
```

**Why It's Bad:**
- Crashes on missing file
- No guidance for user
- Poor UX

**Fix:**
```python
from pathlib import Path

def analyze_skill(path):
    skill_path = Path(path)
    skill_md = skill_path / "SKILL.md"

    if not skill_path.exists():
        raise ValueError(f"Skill directory not found: {path}")

    if not skill_md.exists():
        raise ValueError(f"SKILL.md not found in {path}")

    try:
        content = skill_md.read_text()
    except PermissionError:
        raise ValueError(f"Cannot read SKILL.md: permission denied")

    # ... analyze ...
```

---

## Integration Anti-Patterns

### ❌ Tool Overuse

**Problem:** Calling tools unnecessarily

**Bad Example:**
```markdown
## Process

1. Use Bash to check if file exists: `ls SKILL.md`
2. Use Bash to read file: `cat SKILL.md`
3. Use Bash to search: `grep -r "pattern"`
4. Use Bash to count lines: `wc -l SKILL.md`
```

**Why It's Bad:**
- Inefficient
- Multiple calls for simple tasks
- Wastes resources

**Fix:**
```markdown
## Process

1. Read SKILL.md with Read tool
2. Search for patterns with Grep tool
```

---

### ❌ Tool Underuse

**Problem:** Manual work when tools available

**Bad Example:**
```markdown
Ask user to manually:
1. Open ~/.claude/skills directory
2. Find the skill folder
3. Copy path
4. Provide path to me
```

**Why It's Bad:**
- Poor UX
- Inefficient
- Error-prone

**Fix:**
```markdown
Automatically locate skill:
```bash
ls -la ~/.claude/skills/
```
```

---

### ❌ Wrong Tool for Job

**Problem:** Using Bash when specialized tool exists

**Bad Example:**
```markdown
```bash
cat file.txt | head -20
grep -r "pattern" .
find . -name "*.js"
```
```

**Why It's Bad:**
- Bash is for commands, not file ops
- Specialized tools are faster
- Poor practice

**Fix:**
```markdown
- Read tool for file contents
- Grep tool for searching
- Glob tool for finding files
```

---

### ❌ Ignoring MCP Opportunities

**Problem:** Manual work when MCP integration possible

**Bad Example:**
```markdown
Ask user for GitHub repository info:
1. Repository name
2. Owner
3. Default branch
4. Latest commit SHA
```

**Why It's Bad:**
- Tedious for user
- Error-prone
- MCP can automate this

**Fix:**
```markdown
Use GitHub MCP integration to fetch repository metadata automatically.
```

---

## Red Flags Checklist

When reviewing a skill, immediately flag these:

### Critical Red Flags ❌
- [ ] Command injection (os.system, subprocess with shell=True)
- [ ] eval() or exec() usage
- [ ] Hardcoded secrets (API keys, passwords)
- [ ] Base64-encoded strings with exec
- [ ] Reading sensitive files (~/.ssh, ~/.aws) without justification
- [ ] Network requests to unknown domains
- [ ] YAML injection in frontmatter
- [ ] Path traversal vulnerabilities

### High Priority Red Flags ⚠️
- [ ] No frontmatter
- [ ] Vague or missing description
- [ ] No trigger phrases
- [ ] Undocumented network calls
- [ ] File operations outside skill directory
- [ ] No examples
- [ ] Confusing workflow
- [ ] Missing error handling

### Medium Priority Issues 💡
- [ ] Poor directory organization
- [ ] Undocumented scripts
- [ ] Generic trigger phrases
- [ ] Tool overuse/underuse
- [ ] Inefficient reference loading
- [ ] No "when to use" section
- [ ] Missing Resources section
- [ ] Inconsistent formatting

Use this anti-patterns reference to quickly identify common issues during skill quality analysis.
