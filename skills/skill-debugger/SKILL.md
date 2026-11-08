---
name: skill-debugger
version: 1.0.0
last_updated: 2026-01-27
description: Diagnose and fix Claude Code skills that won't trigger. Use when skills exist but Claude ignores them, or when you ask "why isn't my skill working" or "skill not triggering" or "debug skill" or "skill won't activate".
---

# Skill Debugger

Systematic debugging tool for Claude Code skills that aren't triggering as expected. Identifies root causes like poor descriptions, missing trigger words, naming issues, or skill discovery problems.

## Quick Reference

**Most Common Issues**:
1. ❌ Vague description → ✅ Add specific keywords (financial, code review, etc.)
2. ❌ No trigger words → ✅ Include phrases users naturally say
3. ❌ Name mismatch → ✅ Ensure folder name = YAML name
4. ❌ Skill conflicts → ✅ Make descriptions unique

**Quick Commands**:
```bash
"Why isn't my [skill-name] working?"
"Debug skill triggering for [skill-name]"
"Check if [skill-name] conflicts with other skills"
```

**Expected Fix Time**: 5-15 minutes per skill  
**Success Rate**: 80-90% trigger rate after fixes

---

## Capabilities

- **Trigger Analysis**: Examines why a skill isn't being invoked when it should be
- **Description Evaluation**: Checks if skill description clearly communicates when to use it
- **Keyword Detection**: Identifies missing or weak trigger keywords in descriptions
- **Discovery Debugging**: Verifies Claude can find and load the skill
- **Conflict Detection**: Identifies skills with overlapping triggers or descriptions
- **YAML Validation**: Checks frontmatter format and required fields
- **Interactive Diagnosis**: Guides through systematic debugging steps
- **Fix Suggestions**: Provides specific improvements to improve skill triggering

## When to Use

Use this skill when:
- A skill exists but Claude never invokes it automatically
- You need to say the skill name explicitly to trigger it
- Claude says "skill doesn't exist" but you know it's installed
- Wrong skill triggers instead of the one you want
- You're creating a new skill and want to test if it will trigger correctly
- Multiple skills seem to conflict or overlap

**Trigger phrases**: "why isn't my skill working", "skill not triggering", "debug skill", "skill won't activate", "wrong skill triggered"

---

## Common Skill Triggering Problems

### Problem 1: Vague Description
**Symptom**: Skill exists but Claude never uses it
**Root Cause**: Description doesn't mention specific use cases or keywords
**Example**:
```yaml
description: Helps with various tasks  ❌ Too vague
description: Analyzes financial ratios from statement data for investment decisions  ✅ Specific
```

### Problem 2: No Clear Trigger Words
**Symptom**: Need to explicitly mention skill name to invoke it
**Root Cause**: Description lacks keywords that match user queries
**Fix**: Add trigger keywords like "financial analysis", "investment", "ratios"

### Problem 3: Skill Not Discovered
**Symptom**: Claude says skill doesn't exist
**Root Cause**: Wrong installation location or invalid SKILL.md
**Check**: `~/.claude/skills/[name]/SKILL.md` or `.claude/skills/[name]/SKILL.md`

### Problem 4: Name Mismatch
**Symptom**: Skill found but not loaded
**Root Cause**: YAML `name` doesn't match folder name
**Fix**: Ensure `name: skill-name` matches folder `skill-name/`

### Problem 5: Overlapping Skills
**Symptom**: Wrong skill triggers instead
**Root Cause**: Multiple skills with similar descriptions
**Fix**: Make each description unique and specific

## Input Requirements

**Basic Debugging**:
- Skill name or path
- Expected trigger scenario (what you asked that should have triggered it)

**Deep Analysis**:
- All installed skills paths (for conflict detection)
- Recent conversation history (to see what Claude chose instead)

## Output Formats

**Quick Diagnosis**:
```
Skill: code-review
Status: ❌ Not triggering
Root Cause: Description too generic
Fix: Add specific keywords like "review", "code quality", "pull request"
```

**Detailed Report**:
```
=== Skill Debugging Report ===

Skill: financial-analyzer
Path: ~/.claude/skills/financial-analyzer/
Status: ⚠️ Rarely triggers

Issues Found:
1. [CRITICAL] Description missing use case keywords
   - Current: "Analyzes financial data"
   - Should mention: financial ratios, investment analysis, DCF, valuation

2. [HIGH] No "When to Use" section in SKILL.md
   - Claude can't determine clear triggering conditions

3. [MEDIUM] Overlaps with "data-analyzer" skill
   - Both mention "analyzes data"
   - Make this one specific to finance

Recommendations:
1. Update description to: "Calculates financial ratios and performs DCF valuation analysis for investment decisions"
2. Add "When to Use" section with examples: "when analyzing company financials", "for investment analysis"
3. Differentiate from data-analyzer by focusing on financial metrics

Expected Improvement: 90% better triggering with these fixes
```

**Conflict Matrix**:
```
Skills with Overlapping Triggers:

code-review  ←→  quality-analyzer  (both mention "code quality")
  Fix: code-review for PRs, quality-analyzer for metrics

data-analyzer  ←→  financial-analyzer  (both mention "analysis")
  Fix: Make financial-analyzer specific to finance keywords
```

## Debugging Workflow

### Step 1: Verify Skill Exists

```
"Check if my code-review skill is installed correctly"
"Is the financial-analyzer skill discoverable?"
```

Claude will:
- Check file exists at expected location
- Validate SKILL.md format
- Verify YAML frontmatter

### Step 2: Analyze Description Quality

```
"Why isn't my code-review skill triggering?"
"Debug the financial-analyzer skill - I asked about ratios but it didn't trigger"
```

Claude will:
- Examine description for specificity
- Check for relevant keywords
- Compare against your query

### Step 3: Test Trigger Scenarios

```
"What should I ask to trigger the code-review skill?"
"Give me 5 phrases that should invoke financial-analyzer"
```

Claude will:
- Generate test queries based on description
- Identify gaps between description and intended use
- Suggest description improvements

### Step 4: Check for Conflicts

```
"Do any of my skills conflict with code-review?"
"Why does data-analyzer trigger instead of financial-analyzer?"
```

Claude will:
- Compare all skill descriptions
- Identify overlapping keywords
- Suggest differentiation strategies

## Systematic Debugging Questions

When a skill isn't triggering, Claude will ask:

1. **Installation Check**
   - "Is the skill at `~/.claude/skills/[name]/SKILL.md` or `.claude/skills/[name]/SKILL.md`?"
   - "Does `ls ~/.claude/skills/` show your skill folder?"

2. **YAML Validation**
   - "Is the YAML frontmatter properly formatted with `---` delimiters?"
   - "Does the `name:` field match the folder name?"
   - "Is there a `description:` field?"

3. **Description Quality**
   - "Does the description mention specific use cases?"
   - "Does it include keywords you'd naturally use?"
   - "Is it specific enough to avoid confusion with other skills?"

4. **Content Analysis**
   - "Is there a 'When to Use' or 'Use Cases' section?"
   - "Are there clear usage examples?"
   - "Does the first paragraph explain the purpose?"

5. **Conflict Check**
   - "Do other skills have similar descriptions?"
   - "Which skill actually triggered instead?"
   - "How can we differentiate this skill?"

## How to Use

**Quick Fix**:
```
"My code-review skill isn't working"
"Why doesn't Claude use my financial-analyzer?"
"Debug skill triggering for aws-solution-architect"
```

**Detailed Analysis**:
```
"I asked 'analyze this company's financials' but financial-analyzer didn't trigger. Debug it."
"Compare my code-review and quality-analyzer skills - which should trigger when?"
```

**Preventive Check**:
```
"Before I install this skill, check if it will trigger correctly"
"Will my new skill conflict with existing ones?"
```

## Quick Fixes (Top 3)

### Fix 1: Improve Description Specificity
**Before**: `description: Helps with code analysis`
**After**: `description: Performs static code quality analysis with metrics calculation and refactoring suggestions`

**Why it matters**: Specific descriptions help Claude understand exactly when to use the skill.

### Fix 2: Add Trigger Keywords
Add words users would naturally say:
- Financial skill: "ratios", "valuation", "DCF", "investment"
- Code skill: "review", "quality", "refactor", "analyze code"
- Data skill: "visualization", "trends", "insights", "dashboard"

**Why it matters**: Keywords bridge the gap between user queries and skill descriptions.

### Fix 3: Add "When to Use" Section
```markdown
## When to Use

Use this skill when you need to:
- Analyze company financial statements
- Calculate financial ratios (P/E, ROE, ROA, etc.)
- Perform DCF valuation
- Make investment decisions based on financial data
```

**Why it matters**: Explicit use cases make triggering conditions crystal clear.

---

## Advanced Fixes

### Fix 4: Differentiate from Similar Skills
If you have `data-analyzer` and `financial-analyzer`:
- data-analyzer: "for general data analysis and visualization"
- financial-analyzer: "specifically for financial statement analysis and investment metrics"

**Why it matters**: Unique descriptions prevent skill conflicts.

### Fix 5: Fix Name Mismatch
Ensure folder name matches YAML name:
```
Folder: ~/.claude/skills/code-review/
YAML: name: code-review  ✅

Folder: ~/.claude/skills/code-review/
YAML: name: code_review  ❌ Mismatch!
```

**Why it matters**: Name mismatches prevent skill discovery.

## Diagnostic Checklist

When debugging, Claude will check:

- [ ] Skill file exists at correct location
- [ ] SKILL.md has valid YAML frontmatter
- [ ] `name` in YAML matches folder name
- [ ] `description` is 50-150 characters
- [ ] Description includes specific use case keywords
- [ ] Description mentions when/what/who/why
- [ ] No vague words (helps, assists, various, many)
- [ ] "When to Use" or similar section exists
- [ ] At least 3 usage examples present
- [ ] No conflicts with other skill descriptions
- [ ] Trigger keywords match natural language queries

## Integration with Other Skills

**Works with skill-quality-analyzer**:
```bash
"Run quality analysis on financial-analyzer then debug why it's not triggering"
```

**Works with skill-tester**:
```bash
"Test if code-review skill triggers for 'review this PR'"
```

**Complete Workflow Example**:

**Scenario**: Your financial-analyzer skill isn't triggering

**Step 1: Debug the issue**
```bash
"Why isn't my financial-analyzer skill working?"
```
→ skill-debugger identifies: vague description, no trigger keywords

**Step 2: Check overall quality**
```bash
"Run quality analysis on financial-analyzer"
```
→ skill-quality-analyzer scores: 65/100 (needs improvement)

**Step 3: Apply fixes**
- Update description with keywords: "financial ratios", "DCF", "valuation"
- Add "When to Use" section with clear trigger phrases
- Differentiate from similar skills

**Step 4: Test the fix**
```bash
"Test if financial-analyzer triggers for 'calculate P/E ratio'"
```
→ skill-tester confirms: ✅ Triggers correctly

**Expected Timeline**: 10-15 minutes from diagnosis to verified fix

---

## Limitations & Workarounds

- **Cannot Read Claude's Internal Decision Process**: Can only infer based on descriptions
- **No Real-Time Monitoring**: Can't watch skill selection in action
- **Heuristic-Based**: Uses patterns, not guaranteed 100% accurate
- **No Auto-Fix**: Provides recommendations but you must apply them
- **Context-Dependent**: Triggering also depends on conversation context

## When NOT to Use This Skill

- **Skill Works Fine**: No debugging needed
- **Skill Execution Errors**: Use skill-tester for runtime issues
- **Documentation Issues**: Use skill-doc-generator
- **Quality Problems**: Use skill-quality-analyzer

## Success Metrics

After applying fixes, skill should trigger when:
- User query contains description keywords
- Use case matches "When to Use" section
- No more specific skill exists for the query

**Expected Trigger Rate**: 80-90% when query clearly matches intended use case

## Pro Tips

1. **Test Your Descriptions**: Ask "Would I say this naturally?"
2. **Be Specific**: "financial ratio calculation" > "data analysis"
3. **Avoid Overlaps**: Each skill should have unique keywords
4. **Use Examples**: Add 5+ usage examples in SKILL.md
5. **Think Like Users**: What would you actually ask?
6. **Regular Audits**: Run debugger on all skills monthly
7. **Version Descriptions**: Track what works over time
