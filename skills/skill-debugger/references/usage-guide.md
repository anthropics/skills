# How to Use Skill Debugger

## Problem: "My skill never triggers"

### Scenario 1: Vague Description

**Symptom**:
```
User: "Help me analyze this code"
Claude: *Uses general capabilities, not your code-analyzer skill*
```

**Debug**:
```
"Why doesn't my code-analyzer skill trigger?"
```

**Claude's Response**:
```
Analyzing code-analyzer skill...

Issue Found: Description too vague
Current: "Helps analyze code"
Problem: Doesn't mention what kind of analysis or when to use

Fix: Update description to:
"Performs static code quality analysis with complexity metrics, code smell detection, and refactoring suggestions"

This adds keywords: quality, metrics, code smell, refactoring
```

### Scenario 2: Missing Trigger Keywords

**Symptom**:
```
User: "Calculate financial ratios for this company"
Claude: *Doesn't use financial-analyzer skill*
```

**Debug**:
```
"I asked 'calculate financial ratios' but financial-analyzer didn't trigger. Why?"
```

**Claude's Response**:
```
Description Analysis:
Current: "Analyzes financial data"
Missing keywords: ratios, valuation, investment, DCF, ROE, ROA

Your query used: "calculate financial ratios"
Skill description doesn't contain: "ratios" or "calculate"

Fix: Add to description:
"Calculates financial ratios (P/E, ROE, ROA) and performs DCF valuation for investment analysis"
```

### Scenario 3: Skill Conflicts

**Symptom**:
```
User: "Review this code for quality"
Claude: *Uses general code-review, not your specialized quality-analyzer*
```

**Debug**:
```
"Why does code-review trigger instead of quality-analyzer?"
```

**Claude's Response**:
```
Conflict Detected:

code-review: "Reviews code for quality, bugs, and best practices"
quality-analyzer: "Analyzes code quality"

Both mention "code quality" - ambiguous!

Recommendations:
- code-review: "Reviews pull requests for bugs, security, and style"
- quality-analyzer: "Calculates code quality metrics (complexity, maintainability, test coverage)"

Differentiation: code-review for PRs, quality-analyzer for metrics
```

## Step-by-Step Debugging

### Step 1: Verify Installation

```
"Is my aws-solution-architect skill installed correctly?"
```

**Claude checks**:
- File location: `~/.claude/skills/aws-solution-architect/SKILL.md`
- YAML validity
- Name matching

### Step 2: Test Description

```
"What would trigger my financial-analyzer skill?"
```

**Claude generates test queries**:
```
Based on description "Analyzes financial statements", these should trigger:
✓ "Analyze this company's financial statements"
✓ "Help with financial analysis"
✗ "Calculate P/E ratio" - Missing "ratio" keyword
✗ "Perform DCF valuation" - Missing "valuation" keyword

Add missing keywords to description.
```

### Step 3: Compare with Conflicts

```
"Do my skills have conflicting descriptions?"
```

**Claude compares all skills**:
```
Potential Conflicts:
1. data-analyzer ←→ financial-analyzer
   Overlap: Both say "analyzes data"
   Fix: Make financial-analyzer specific to "financial data"

2. code-review ←→ security-scanner
   Overlap: Both mention "security"
   Fix: code-review for "general review", security-scanner for "vulnerability detection"
```

## Real-World Examples

### Example 1: New Skill Not Triggering

**Setup**:
```yaml
# ~/.claude/skills/seo-optimizer/SKILL.md
---
name: seo-optimizer
description: Helps with SEO
---
```

**Problem**:
```
User: "Optimize this article for search engines"
Claude: *Doesn't use seo-optimizer*
```

**Debug Session**:
```
User: "Debug why seo-optimizer didn't trigger for 'optimize for search engines'"

Claude:
Description Analysis:
- Current: "Helps with SEO"
- Your query: "optimize", "search engines"
- Missing from description: "optimize", "search", "keywords", "meta tags"

Description is too brief and vague.

Recommended description:
"Optimizes content for search engines with keyword analysis, meta tag generation, and SEO scoring"

This adds: optimize, search engines, keyword, meta tags, SEO - matching natural queries
```

**After Fix**:
```yaml
description: Optimizes content for search engines with keyword analysis, meta tag generation, and SEO scoring
```

### Example 2: Wrong Skill Triggering

**Setup**:
```yaml
# Skill 1
name: image-editor
description: Edits and processes images

# Skill 2
name: photo-enhancer
description: Enhances photos
```

**Problem**:
```
User: "Enhance this photo's colors"
Claude: *Uses image-editor instead of photo-enhancer*
```

**Debug**:
```
User: "Why does image-editor trigger instead of photo-enhancer for photo enhancement?"

Claude:
Overlap Analysis:
- Both mention image/photo processing
- "image-editor" description is more general
- "photo-enhancer" description doesn't mention "colors", "exposure", etc.

Claude chooses more general skill when uncertain.

Fix:
- image-editor: "Edits images with cropping, resizing, rotation, and format conversion"
- photo-enhancer: "Enhances photo quality with color correction, exposure adjustment, and noise reduction"

Now "enhance photo colors" clearly matches photo-enhancer keywords.
```

## Quick Reference

### Debugging Commands

| Command | What It Does |
|---------|--------------|
| `"Debug [skill-name]"` | Full diagnostic |
| `"Why doesn't [skill-name] trigger?"` | Analyze description |
| `"What triggers [skill-name]?"` | Generate test queries |
| `"Check skill conflicts"` | Find overlapping skills |
| `"Is [skill-name] installed?"` | Verify installation |

### Common Fixes

| Problem | Fix |
|---------|-----|
| Too vague | Add specific keywords and use cases |
| No triggers | Add words users would naturally say |
| Wrong skill triggers | Differentiate descriptions |
| Skill not found | Check installation path and name |
| Never triggers | Add "When to Use" section |

## Pro Tips

1. **Think Like a User**: Would you say these words?
2. **Be Specific**: Don't say "helps with" - say exactly what it does
3. **Add Use Cases**: "for investment analysis" clarifies when to use
4. **Avoid Generics**: "code analysis" → "code quality metrics"
5. **Test Regularly**: Ask Claude to suggest trigger phrases
6. **Iterate**: Debug → Fix → Test → Repeat
