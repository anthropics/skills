---
name: skill-quality-analyzer
description: Comprehensive quality analysis tool for Claude Skills. Evaluates skills from GitHub URLs, marketplace links, ZIP files, or local directories across five dimensions (structure, security, UX, code quality, integration) using balanced scoring and three output modes (comprehensive report, interactive review, pass/fail certification). Triggers on "analyze skill quality", "review this skill", "evaluate skill", or "skill quality check".
---

# Claude Skill Quality Analyzer

## Overview

This skill provides comprehensive quality analysis for Claude Skills from any source (GitHub, marketplaces, ZIP files, local directories). It evaluates skills across five critical dimensions using a balanced approach that weighs security, architecture, user experience, code quality, and integration equally.

## Output Modes

Users select one of three analysis modes:

1. **Comprehensive Report** - Detailed markdown report with numerical scores (0-100) across all dimensions
2. **Interactive Review** - Step-by-step analysis with specific, actionable recommendations for improvement
3. **Pass/Fail Certification** - Binary quality assessment with specific issues blocking certification

## When to Use This Skill

Use this skill when:
- Evaluating a skill before installation from any source
- Reviewing skills for quality and best practices adherence
- Auditing existing skills for improvement opportunities
- Validating skills before publishing or sharing
- Comparing multiple skills for quality
- Certifying skills meet quality standards

**Trigger phrases:**
- "Analyze skill quality for [skill-name]"
- "Review this skill: [url/path]"
- "Evaluate skill from [source]"
- "Run skill quality check on [skill]"
- "Is this skill well-built?"
- "Certify skill quality for [skill-name]"

## Evaluation Dimensions

### 1. Structure & Documentation (20%)

**What we evaluate:**
- SKILL.md exists and follows best practices
- Proper YAML frontmatter (name, description fields)
- Clear, comprehensive description with trigger phrases
- Well-organized sections (Overview, When to Use, Workflow, Resources)
- Examples, templates, and usage guidance provided
- References directory organization
- README if applicable

**Scoring criteria:**
- 90-100: Exemplary documentation, comprehensive examples, clear workflows
- 70-89: Good documentation with minor gaps
- 50-69: Basic documentation present but lacking detail
- 0-49: Missing critical documentation or poorly structured

### 2. Security (30%)

**What we evaluate:**
- Uses skill-security-analyzer skill for automated scanning
- No malicious code patterns (command injection, data exfiltration)
- No YAML injection vulnerabilities
- Safe file operations (scoped to skill directory)
- No hardcoded secrets or credentials
- Proper input validation
- No supply chain risks
- No code obfuscation

**Scoring criteria:**
- 90-100: No security issues, follows all best practices
- 70-89: Minor best practice violations, no critical issues
- 50-69: Some security concerns requiring review
- 0-49: Critical security vulnerabilities present

**Note:** Security analysis leverages the skill-security-analyzer skill for automated vulnerability detection.

### 3. User Experience (20%)

**What we evaluate:**
- Clear, specific trigger phrases
- Well-documented workflow with step-by-step guidance
- Helpful, practical examples
- Appropriate use of references/ for detailed info
- Good logical organization
- Clear scope definition (when to use vs. not use)
- Actionable output format

**Scoring criteria:**
- 90-100: Exceptional UX, immediately clear how to use
- 70-89: Good UX with minor confusion points
- 50-69: Usable but requires effort to understand
- 0-49: Confusing, unclear, or poorly organized

### 4. Code Quality (15%)

**What we evaluate:**
- Follows skill development best practices
- Proper resource organization (references/, scripts/, assets/)
- Clear, maintainable structure
- Scripts are well-documented and safe
- No unnecessary complexity
- Consistent formatting and style
- Appropriate use of templates/assets

**Scoring criteria:**
- 90-100: Exemplary code quality and organization
- 70-89: Good quality with minor issues
- 50-69: Acceptable but could be improved
- 0-49: Poor quality, hard to maintain

### 5. Integration & Tools (15%)

**What we evaluate:**
- Appropriate tool/skill invocation patterns
- Proper MCP integration (if applicable)
- Efficient resource usage
- Scripts properly integrated
- No tool overuse or underuse
- Clear integration documentation

**Scoring criteria:**
- 90-100: Perfect tool integration and efficiency
- 70-89: Good integration with minor improvements possible
- 50-69: Basic integration, missing optimization opportunities
- 0-49: Poor integration or misuse of tools

## Analysis Workflow

### Step 1: Understand the Source & Mode

**Get the skill source:**

Ask user for:
1. **Source type:** GitHub URL, marketplace link, ZIP file, or local directory
2. **Analysis mode:** Comprehensive report, interactive review, or pass/fail certification

**Fetch the skill:**

For GitHub URLs:
```bash
git clone <github-url> /tmp/skill-analysis/<skill-name>
```

For marketplace links:
```bash
# Marketplace skills are in ~/.claude/plugins/marketplaces/*/
# or ~/.claude/skills/ for user skills
ls -la ~/.claude/skills/
ls -la ~/.claude/plugins/marketplaces/*/
```

For ZIP files:
```bash
unzip <path-to-zip> -d /tmp/skill-analysis/<skill-name>
```

For local directories:
```bash
# Use path directly
ls -la <local-path>
```

### Step 2: Understand the Skill's Purpose

Read SKILL.md to understand:
- What the skill is supposed to do
- Intended use cases
- Stated capabilities
- Documented workflow

This context is critical for evaluating if the skill achieves its stated goals effectively.

### Step 3: Run Security Analysis

**ALWAYS use the skill-security-analyzer skill first:**

Invoke the security analyzer skill to get a comprehensive security report. This provides:
- Automated vulnerability detection
- Malicious code pattern identification
- YAML injection checks
- Supply chain risk assessment
- Risk rating (CRITICAL/HIGH/MEDIUM/LOW/SAFE)

**Parse security results:**
- CRITICAL findings = 0-40 security score
- HIGH findings = 50-69 security score
- MEDIUM findings = 70-89 security score
- LOW/SAFE = 90-100 security score

### Step 4: Evaluate Structure & Documentation

**Check SKILL.md:**
```bash
cat <skill-path>/SKILL.md
```

**Evaluate:**
- YAML frontmatter present and valid
- Description is clear (1-2 sentences max)
- Trigger phrases documented
- Sections well-organized
- Examples provided
- Resources section present

**Check for README:**
```bash
ls <skill-path>/README.md
```

**Check references organization:**
```bash
ls -la <skill-path>/references/
```

**Score:**
- Frontmatter valid: +20 points
- Clear description with triggers: +20 points
- Well-organized sections: +20 points
- Examples/templates present: +20 points
- Resources documented: +20 points

### Step 5: Evaluate User Experience

**Review from user perspective:**
- Can I quickly understand what this skill does?
- Are trigger phrases clear and natural?
- Is the workflow easy to follow?
- Are examples practical and helpful?
- Is scope well-defined?

**Check for anti-patterns:**
- ❌ Vague description
- ❌ No trigger phrases
- ❌ Missing examples
- ❌ Unclear workflow
- ❌ Overly complex instructions

**Score:**
- Clear purpose and triggers: +30 points
- Well-documented workflow: +30 points
- Practical examples: +20 points
- Good organization: +20 points

### Step 6: Evaluate Code Quality

**Check directory structure:**
```bash
tree <skill-path>
```

Expected structure:
```
skill-name/
├── SKILL.md (required)
├── README.md (optional)
├── scripts/ (optional - helper scripts)
├── references/ (optional - detailed docs)
└── assets/ (optional - templates, images)
```

**Review scripts (if present):**
```bash
cat <skill-path>/scripts/*.py
cat <skill-path>/scripts/*.sh
```

**Evaluate:**
- Proper organization
- No unnecessary files
- Scripts are safe and documented
- Consistent formatting
- Clear purpose for each file

**Score:**
- Proper structure: +30 points
- Scripts well-documented: +25 points
- Clean, maintainable code: +25 points
- Consistent style: +20 points

### Step 7: Evaluate Integration & Tools

**Check for tool/skill usage patterns:**
```bash
grep -r "Skill\|Task\|Bash\|Read\|Write\|Grep\|Glob" <skill-path>/SKILL.md
```

**Evaluate:**
- Are tools used appropriately?
- Is MCP integration documented (if applicable)?
- Are scripts efficiently integrated?
- Is resource usage optimized?

**Score:**
- Appropriate tool usage: +40 points
- Proper MCP integration: +30 points
- Efficient resource usage: +30 points

### Step 8: Generate Output Based on Mode

#### Mode 1: Comprehensive Report

Generate detailed markdown report:

```markdown
# Skill Quality Analysis Report: [Skill Name]

**Skill:** [skill-name]
**Source:** [URL/path]
**Analyzed:** [ISO date]
**Analyzer:** Skill Quality Analyzer v1.0

## Overall Quality Score: [X/100]

**Grade:** [A+ / A / B+ / B / C+ / C / D / F]
**Recommendation:** [EXCELLENT / GOOD / ACCEPTABLE / NEEDS IMPROVEMENT / POOR]

---

## Dimension Scores

| Dimension | Score | Weight | Weighted Score | Grade |
|-----------|-------|--------|----------------|-------|
| Structure & Documentation | X/100 | 20% | X/100 | A/B/C/D/F |
| Security | X/100 | 30% | X/100 | A/B/C/D/F |
| User Experience | X/100 | 20% | X/100 | A/B/C/D/F |
| Code Quality | X/100 | 15% | X/100 | A/B/C/D/F |
| Integration & Tools | X/100 | 15% | X/100 | A/B/C/D/F |
| **TOTAL** | **X/100** | **100%** | **X/100** | **X** |

---

## 1. Structure & Documentation (X/100)

**Grade:** [A/B/C/D/F]

### Strengths ✅
- [What's done well]

### Issues ⚠️
- [What needs improvement]

### Critical Gaps ❌
- [What's missing]

### Specific Findings:
- **SKILL.md Frontmatter:** [PASS/FAIL] - [Details]
- **Description Quality:** [EXCELLENT/GOOD/POOR] - [Details]
- **Trigger Phrases:** [PRESENT/MISSING] - [Details]
- **Workflow Documentation:** [EXCELLENT/GOOD/POOR] - [Details]
- **Examples:** [COMPREHENSIVE/BASIC/MISSING] - [Details]
- **Resources Section:** [PRESENT/MISSING] - [Details]

---

## 2. Security (X/100)

**Grade:** [A/B/C/D/F]
**Risk Rating:** [SAFE/LOW/MEDIUM/HIGH/CRITICAL]

### Security Analysis Summary
[Security analyzer findings summary]

### Critical Findings ([count])
[List from security analyzer]

### High Priority Findings ([count])
[List from security analyzer]

### Medium Priority Findings ([count])
[List from security analyzer]

### Security Compliance Checklist:
- ✓/✗ No command injection vulnerabilities
- ✓/✗ No data exfiltration attempts
- ✓/✗ No credential theft patterns
- ✓/✗ YAML frontmatter is safe
- ✓/✗ All network calls documented
- ✓/✗ File operations properly scoped
- ✓/✗ Input validation present
- ✓/✗ No obfuscated code

---

## 3. User Experience (X/100)

**Grade:** [A/B/C/D/F]

### Strengths ✅
[What makes it easy to use]

### Confusion Points ⚠️
[What's unclear]

### Critical UX Issues ❌
[What blocks usability]

### UX Evaluation:
- **Clarity of Purpose:** [EXCELLENT/GOOD/POOR] - [Details]
- **Trigger Phrases:** [CLEAR/VAGUE/MISSING] - [Details]
- **Workflow Clarity:** [STEP-BY-STEP/BASIC/CONFUSING] - [Details]
- **Examples:** [PRACTICAL/BASIC/UNHELPFUL] - [Details]
- **Organization:** [LOGICAL/ACCEPTABLE/CHAOTIC] - [Details]

---

## 4. Code Quality (X/100)

**Grade:** [A/B/C/D/F]

### Strengths ✅
[Well-organized aspects]

### Improvement Areas ⚠️
[What could be better]

### Quality Issues ❌
[Poor practices]

### Code Quality Evaluation:
- **Directory Structure:** [EXCELLENT/GOOD/POOR] - [Details]
- **Scripts Quality:** [WELL-DOCUMENTED/BASIC/POOR] - [Details]
- **Organization:** [CLEAN/ACCEPTABLE/MESSY] - [Details]
- **Maintainability:** [HIGH/MEDIUM/LOW] - [Details]

---

## 5. Integration & Tools (X/100)

**Grade:** [A/B/C/D/F]

### Strengths ✅
[Good integrations]

### Improvement Areas ⚠️
[Integration opportunities]

### Integration Issues ❌
[Misuse or missing integrations]

### Integration Evaluation:
- **Tool Usage:** [APPROPRIATE/ACCEPTABLE/POOR] - [Details]
- **MCP Integration:** [N/A or PROPER/MISSING/POOR] - [Details]
- **Resource Efficiency:** [OPTIMIZED/ACCEPTABLE/WASTEFUL] - [Details]

---

## Overall Assessment

**Summary:**
[2-3 sentence summary of overall quality]

**Top 3 Strengths:**
1. [Strength 1]
2. [Strength 2]
3. [Strength 3]

**Top 3 Improvement Priorities:**
1. [Priority 1] - [Impact: HIGH/MEDIUM/LOW]
2. [Priority 2] - [Impact: HIGH/MEDIUM/LOW]
3. [Priority 3] - [Impact: HIGH/MEDIUM/LOW]

**Recommendation:**
[Detailed recommendation for usage/improvement]

---

*Report generated by Skill Quality Analyzer v1.0*
```

#### Mode 2: Interactive Review

Provide step-by-step analysis with specific, actionable recommendations:

```markdown
# Interactive Skill Quality Review: [Skill Name]

I'll walk through each dimension and provide specific recommendations for improvement.

---

## 🏗️ Structure & Documentation Review

### Current State
[What exists now]

### What's Working Well ✅
[Positive aspects]

### Specific Recommendations 💡

**1. [Issue/Opportunity]**
   - **Current:** [What's there now]
   - **Problem:** [Why it's an issue]
   - **Fix:** [Specific action to take]
   - **Example:**
   ```markdown
   [Code example of fix]
   ```

**2. [Next issue/opportunity]**
   [Same format...]

---

## 🔒 Security Review

[Security analyzer findings in actionable format]

### Critical Issues ❌ (Fix Immediately)
**1. [Finding]**
   - **Location:** `file.py:line`
   - **Risk:** [Why it's dangerous]
   - **Fix:**
   ```python
   # Instead of this:
   [Bad code]

   # Do this:
   [Good code]
   ```

### Improvements ⚠️ (Fix Soon)
[Same format...]

---

## 🎨 User Experience Review

### What Works ✅
[Positive UX aspects]

### Quick Wins 💡
**1. [Improvement]**
   - **Why:** [User benefit]
   - **How:** [Specific action]
   - **Example:** [If applicable]

---

## 🔧 Code Quality Review

[Specific file/script recommendations]

---

## 🔌 Integration & Tools Review

[Specific integration improvements]

---

## 📋 Action Plan

Based on this review, here's your prioritized action plan:

### Immediate (Do First)
1. [Action] - **Impact:** HIGH - **Effort:** [LOW/MEDIUM/HIGH]
2. [Action] - **Impact:** HIGH - **Effort:** [LOW/MEDIUM/HIGH]

### Short-term (Do Soon)
1. [Action] - **Impact:** MEDIUM - **Effort:** [LOW/MEDIUM/HIGH]
2. [Action] - **Impact:** MEDIUM - **Effort:** [LOW/MEDIUM/HIGH]

### Long-term (Nice to Have)
1. [Action] - **Impact:** LOW - **Effort:** [LOW/MEDIUM/HIGH]

---

Would you like me to help implement any of these improvements?
```

#### Mode 3: Pass/Fail Certification

Binary assessment with specific blocking issues:

```markdown
# Skill Quality Certification: [Skill Name]

**Certification Status:** [✅ PASS / ❌ FAIL]
**Overall Score:** [X/100]
**Analyzed:** [ISO date]

---

## Certification Criteria (Minimum Requirements)

| Criteria | Status | Score | Minimum | Result |
|----------|--------|-------|---------|--------|
| Structure & Documentation | [PASS/FAIL] | X/100 | 70/100 | ✅/❌ |
| Security | [PASS/FAIL] | X/100 | 80/100 | ✅/❌ |
| User Experience | [PASS/FAIL] | X/100 | 70/100 | ✅/❌ |
| Code Quality | [PASS/FAIL] | X/100 | 60/100 | ✅/❌ |
| Integration & Tools | [PASS/FAIL] | X/100 | 60/100 | ✅/❌ |
| **Overall** | **[PASS/FAIL]** | **X/100** | **70/100** | **✅/❌** |

---

## ❌ Blocking Issues (Must Fix to Pass)

### Critical Security Issues
[List critical security findings]

### Missing Required Components
- ❌ [Component] - **Required for:** [Reason]

### Critical Quality Issues
[List blocking quality issues]

---

## ⚠️ Non-Blocking Issues (Recommended Fixes)

[Issues that don't block certification but should be addressed]

---

## ✅ Passed Requirements

[What meets or exceeds standards]

---

## Certification Decision

**[✅ CERTIFIED / ❌ NOT CERTIFIED]**

**Reasoning:**
[Explanation of why it passed/failed]

**If FAIL, Required Actions:**
1. [Must fix 1]
2. [Must fix 2]
3. [Must fix 3]

**Re-certification:**
Once these issues are resolved, re-run the analyzer for certification.

---

*Certification by Skill Quality Analyzer v1.0*
```

## Grading Scale

### Overall Quality Score
- **90-100 (A+/A):** Excellent - Exemplary skill, best practices
- **80-89 (B+/B):** Good - High quality with minor improvements possible
- **70-79 (C+/C):** Acceptable - Functional but needs improvement
- **60-69 (D):** Needs Improvement - Significant issues present
- **0-59 (F):** Poor - Critical issues, not recommended for use

### Certification Requirements
To pass certification:
- Overall score ≥ 70/100
- Security score ≥ 80/100
- Structure score ≥ 70/100
- UX score ≥ 70/100
- Code Quality score ≥ 60/100
- Integration score ≥ 60/100
- No CRITICAL security findings

## Best Practices Reference

Based on analysis of well-built skills, here are the patterns to follow:

### Excellent SKILL.md Structure
```markdown
---
name: skill-name
description: One clear sentence. Use when [trigger context]. Trigger phrases: "phrase 1", "phrase 2".
---

# Skill Name

## Overview
[2-3 sentences: what it does, why it exists]

## When to Use This Skill
Use this skill when:
- [Specific use case 1]
- [Specific use case 2]

**Trigger phrases:**
- "phrase 1"
- "phrase 2"

## [Primary Section - Workflow/Patterns/etc.]
[Main content with clear structure]

### Subsection 1
[Detailed guidance]

### Subsection 2
[Detailed guidance]

## Resources

### references/file1.md
[What it contains and when to use it]

### scripts/script.py
[What it does]

---

[Footer if applicable]
```

### Excellent Description Format
```
[Action/capability] for [context]. Use when [trigger scenario]. Trigger phrases: "X", "Y", "Z".
```

Examples:
- "Security analysis tool for Claude Code skills. Use when analyzing skills for vulnerabilities. Triggers: 'analyze skill security', 'check if safe'."
- "Frontend code review for React apps. Use when reviewing PRs or code. Triggers: 'review frontend code', 'check React best practices'."

### Excellent Trigger Phrases
- Natural language phrases users would actually say
- 3-5 variations
- Specific enough to avoid false triggers
- Include both formal and casual versions

Examples:
- "analyze this skill for security issues"
- "review this frontend PR"
- "run TDD tests"

## Common Anti-Patterns to Flag

### Structure Issues
- ❌ Missing or invalid frontmatter
- ❌ Vague description without trigger phrases
- ❌ No "When to Use" section
- ❌ Missing examples
- ❌ Undocumented resources

### Security Issues
- ❌ Command injection vulnerabilities
- ❌ Hardcoded secrets
- ❌ Unsafe file operations
- ❌ Undocumented network calls
- ❌ YAML injection risks

### UX Issues
- ❌ Unclear purpose
- ❌ Missing trigger phrases
- ❌ Confusing workflow
- ❌ No examples
- ❌ Overly complex

### Code Quality Issues
- ❌ Messy directory structure
- ❌ Undocumented scripts
- ❌ Inconsistent formatting
- ❌ Unnecessary complexity

### Integration Issues
- ❌ Tool overuse (too many tool calls)
- ❌ Tool underuse (manual when tools available)
- ❌ Inefficient resource loading
- ❌ Missing MCP integration opportunities

## Example Analysis

**User Request:** "Analyze skill quality for https://github.com/user/my-skill"

**Process:**

1. **Fetch skill:**
   ```bash
   git clone https://github.com/user/my-skill /tmp/skill-analysis/my-skill
   ```

2. **Ask for mode:**
   "I'll analyze this skill for quality. Which analysis mode would you like?
   1. Comprehensive Report (detailed scores)
   2. Interactive Review (step-by-step recommendations)
   3. Pass/Fail Certification (binary assessment)"

3. **Read SKILL.md:**
   ```bash
   cat /tmp/skill-analysis/my-skill/SKILL.md
   ```

4. **Run security analysis:**
   Use skill-security-analyzer skill on the skill directory

5. **Evaluate all dimensions:**
   - Structure: Check frontmatter, sections, examples
   - Security: Parse security analyzer results
   - UX: Evaluate clarity, triggers, workflow
   - Code Quality: Review structure, scripts
   - Integration: Check tool usage, MCP integration

6. **Generate report based on mode:**
   Output comprehensive report / interactive review / pass-fail certification

## Resources

### references/quality-checklist.md
Comprehensive checklist for evaluating skills across all dimensions. Load for detailed evaluation criteria.

### references/best-practices-patterns.md
Database of best practices from high-quality skills. Load when providing specific recommendations.

### references/anti-patterns.md
Common mistakes and issues to flag. Load for quick pattern matching.

---

**Important:** This skill uses the skill-security-analyzer skill for security evaluation and provides balanced assessment across structure, security, UX, code quality, and integration. Always start with security analysis before proceeding to other dimensions.
