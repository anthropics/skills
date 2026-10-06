# Skill Quality Evaluation Checklist

This comprehensive checklist provides detailed criteria for evaluating Claude Skills across all five quality dimensions.

## 1. Structure & Documentation (20% weight)

### SKILL.md Frontmatter (Critical)
- [ ] **Frontmatter exists** - YAML block at top of SKILL.md
- [ ] **`name` field present** - Skill identifier (lowercase, hyphens)
- [ ] **`description` field present** - Clear one-liner
- [ ] **Frontmatter valid** - Proper YAML syntax, no injection

**Scoring:**
- All present and valid: +20 points
- Missing description: -10 points
- Missing name: -15 points
- Invalid YAML: -20 points (CRITICAL)

### Description Quality (High Priority)
- [ ] **One clear sentence** - Describes what skill does
- [ ] **Context provided** - Explains when to use it
- [ ] **Trigger phrases mentioned** - Lists example triggers
- [ ] **Specific, not vague** - Concrete capability description

**Good Examples:**
- "Security analysis tool for Claude Code skills. Use when analyzing skills for vulnerabilities. Triggers: 'analyze skill security'."
- "Frontend code review for React apps. Use when reviewing PRs. Triggers: 'review frontend code'."

**Bad Examples:**
- "A helpful skill" (too vague)
- "Does many things related to code" (unclear)
- Just listing features without context

**Scoring:**
- Excellent description: +20 points
- Good description: +15 points
- Basic description: +10 points
- Vague/unclear: +5 points
- Missing: 0 points

### Core Sections (High Priority)
- [ ] **Overview section** - 2-3 sentences explaining purpose
- [ ] **"When to Use" section** - Specific use cases listed
- [ ] **Trigger phrases documented** - Natural language examples
- [ ] **Main content section** - Workflow, patterns, or guidance
- [ ] **Resources section** - Documents references/, scripts/, assets/

**Scoring:**
- All sections present and well-written: +20 points
- Missing 1-2 sections: +10 points
- Missing 3+ sections: +5 points
- Only frontmatter: 0 points

### Examples & Guidance (Medium Priority)
- [ ] **Practical examples** - Real-world usage scenarios
- [ ] **Code examples** - Actual commands/code snippets
- [ ] **Templates provided** - In assets/ if applicable
- [ ] **Clear workflow** - Step-by-step process documented

**Scoring:**
- Comprehensive examples: +20 points
- Basic examples: +12 points
- Minimal examples: +6 points
- No examples: 0 points

### References Organization (Medium Priority)
- [ ] **references/ exists** - Directory for detailed docs
- [ ] **Files well-named** - Descriptive filenames
- [ ] **Purpose documented** - Resources section explains each file
- [ ] **Appropriate use** - References loaded when needed, not always

**Scoring:**
- Excellent organization: +20 points
- Good organization: +15 points
- Basic organization: +10 points
- No references: 0 points (not penalized if not needed)

## 2. Security (30% weight)

### Critical Vulnerabilities (Blockers)
- [ ] **No command injection** - subprocess.call/os.system with user input
- [ ] **No data exfiltration** - Undocumented external requests
- [ ] **No credential theft** - Reading ~/.ssh, ~/.aws without disclosure
- [ ] **No YAML injection** - Malicious frontmatter directives
- [ ] **No reverse shells** - Socket connections to external servers
- [ ] **No privilege escalation** - sudo usage without justification

**Scoring:**
- Any CRITICAL finding: 0-40 points (FAIL)
- No critical findings: Proceed to next checks

### High-Risk Issues
- [ ] **No eval/exec** - Unless clearly justified and safe
- [ ] **No obfuscated code** - base64 decoding + exec
- [ ] **Input validation present** - File paths, user data validated
- [ ] **Network calls documented** - All external APIs in SKILL.md
- [ ] **File ops scoped** - Only access skill directory
- [ ] **No hardcoded secrets** - API keys, tokens externalized

**Scoring:**
- No high-risk issues: 90-100 points
- 1-2 high-risk issues: 70-89 points
- 3+ high-risk issues: 50-69 points

### Medium-Risk Issues
- [ ] **Dependencies documented** - All imports explained
- [ ] **No typosquatting** - Well-known package names
- [ ] **Safe subprocess usage** - Argument lists, not shell strings
- [ ] **Path validation** - No "../" without checks
- [ ] **Proper error handling** - Doesn't expose sensitive info

**Scoring:**
- No medium issues: No deduction
- 1-3 medium issues: -5 points each
- 4+ medium issues: -10 points each

### Best Practices
- [ ] **Principle of least privilege** - Minimal permissions requested
- [ ] **Defense in depth** - Multiple validation layers
- [ ] **Secure defaults** - Fail closed, not open
- [ ] **Clear security docs** - Network/file requirements stated

**Scoring:**
- All best practices followed: +10 bonus points
- Most followed: +5 bonus points

## 3. User Experience (20% weight)

### Clarity of Purpose (Critical)
- [ ] **Immediately clear** - User knows what skill does in 5 seconds
- [ ] **Specific scope** - Not trying to do everything
- [ ] **Clear value prop** - Why use this vs. alternatives
- [ ] **Appropriate naming** - Skill name matches function

**Scoring:**
- Immediately clear: +30 points
- Takes effort to understand: +15 points
- Confusing or vague: +5 points

### Trigger Phrases (High Priority)
- [ ] **Natural language** - Phrases users would actually say
- [ ] **Specific enough** - Avoids false triggers
- [ ] **Variety provided** - 3-5 different phrasings
- [ ] **Includes variations** - Formal + casual versions
- [ ] **Documented clearly** - Easy to find in SKILL.md

**Good Examples:**
- "analyze this skill for security issues"
- "check if this plugin is safe"
- "audit [skill-name] security"

**Bad Examples:**
- "skill" (too generic)
- "do the thing with the stuff" (unclear)
- Only one variation

**Scoring:**
- Excellent trigger phrases: +30 points
- Good trigger phrases: +20 points
- Basic trigger phrases: +10 points
- Vague or missing: 0 points

### Workflow Clarity (High Priority)
- [ ] **Step-by-step guidance** - Clear process to follow
- [ ] **Logical flow** - Steps in sensible order
- [ ] **Decision points explained** - When to choose options
- [ ] **Expected output described** - What user will see

**Scoring:**
- Crystal clear workflow: +30 points
- Understandable workflow: +20 points
- Basic workflow: +10 points
- Confusing or missing: 0 points

### Examples & Usability (Medium Priority)
- [ ] **Practical examples** - Real scenarios, not toy cases
- [ ] **Copy-paste ready** - Code/commands work as-is
- [ ] **Common use cases** - Covers frequent scenarios
- [ ] **Edge cases noted** - Explains limitations

**Scoring:**
- Excellent examples: +20 points
- Good examples: +15 points
- Basic examples: +8 points
- No examples: 0 points

### Organization (Low Priority)
- [ ] **Logical structure** - Related info grouped together
- [ ] **Easy scanning** - Headers, lists, formatting
- [ ] **Appropriate length** - Not too verbose or terse
- [ ] **Consistent style** - Same formatting throughout

**Scoring:**
- Excellent organization: +20 points (bonus)
- Good organization: No bonus
- Poor organization: -10 points penalty

## 4. Code Quality (15% weight)

### Directory Structure
- [ ] **SKILL.md present** (required)
- [ ] **README.md** (optional, for GitHub/marketplaces)
- [ ] **references/** (optional, for detailed docs)
- [ ] **scripts/** (optional, for helper scripts)
- [ ] **assets/** (optional, for templates/images)
- [ ] **No unnecessary files** - Clean, focused structure

**Expected Structure:**
```
skill-name/
├── SKILL.md (required)
├── README.md (optional)
├── scripts/ (optional)
│   ├── setup.sh
│   └── helper.py
├── references/ (optional)
│   ├── detailed-guide.md
│   └── patterns.md
└── assets/ (optional)
    ├── templates/
    └── images/
```

**Scoring:**
- Clean, appropriate structure: +30 points
- Acceptable structure: +20 points
- Messy or improper structure: +10 points

### Scripts Quality (if present)
- [ ] **Well-documented** - Comments, docstrings
- [ ] **Single responsibility** - Each script does one thing
- [ ] **Error handling** - Proper try/catch, validation
- [ ] **Safe execution** - No destructive operations without confirmation
- [ ] **Clear purpose** - Name indicates function

**Scoring:**
- Excellent scripts: +25 points
- Good scripts: +18 points
- Basic scripts: +10 points
- Poor scripts: +5 points
- N/A if no scripts: Skip

### Maintainability
- [ ] **Consistent formatting** - Same style throughout
- [ ] **Clear naming** - Files, variables, functions
- [ ] **No duplication** - DRY principle followed
- [ ] **Modular design** - Separate concerns
- [ ] **Comments where needed** - Complex logic explained

**Scoring:**
- Highly maintainable: +25 points
- Maintainable: +18 points
- Acceptable: +12 points
- Hard to maintain: +5 points

### Efficiency
- [ ] **No bloat** - Only necessary files/code
- [ ] **Appropriate references** - Not loading huge files always
- [ ] **Fast execution** - Scripts optimized
- [ ] **Resource-conscious** - Doesn't waste memory/CPU

**Scoring:**
- Very efficient: +20 points
- Efficient: +15 points
- Acceptable: +10 points
- Wasteful: +5 points

## 5. Integration & Tools (15% weight)

### Tool Usage Appropriateness
- [ ] **Right tools for job** - Bash for commands, Read for files, etc.
- [ ] **Not overusing tools** - Doesn't call tools unnecessarily
- [ ] **Not underusing tools** - Uses tools when appropriate vs. manual
- [ ] **Proper tool composition** - Combines tools effectively

**Examples of Good Usage:**
- Using Bash for git commands
- Using Read for file contents
- Using Grep for searching code
- Using Skill for invoking other skills

**Examples of Poor Usage:**
- Using Bash for file reading (use Read instead)
- Calling Read in a loop (use Grep instead)
- Manual text parsing when Grep would work

**Scoring:**
- Optimal tool usage: +40 points
- Good tool usage: +30 points
- Acceptable tool usage: +20 points
- Poor tool usage: +10 points

### MCP Integration (if applicable)
- [ ] **Documented** - MCP usage explained in SKILL.md
- [ ] **Properly configured** - MCP servers referenced correctly
- [ ] **Resource management** - Efficient MCP resource usage
- [ ] **Error handling** - Handles MCP failures gracefully

**Scoring:**
- Excellent MCP integration: +30 points
- Good MCP integration: +22 points
- Basic MCP integration: +15 points
- Poor MCP integration: +8 points
- N/A if no MCP: Skip

### Resource Efficiency
- [ ] **Lazy loading** - References loaded when needed
- [ ] **Minimal context** - Doesn't load unnecessary docs
- [ ] **Efficient searches** - Uses Grep/Glob appropriately
- [ ] **Caching aware** - Doesn't repeat expensive operations

**Scoring:**
- Highly efficient: +30 points
- Efficient: +22 points
- Acceptable: +15 points
- Wasteful: +8 points

## Scoring Summary

### Total Points Calculation

1. **Structure & Documentation (20%)**
   - Frontmatter: 20 points
   - Description: 20 points
   - Core sections: 20 points
   - Examples: 20 points
   - References: 20 points
   - **Max: 100 points** × 0.20 = 20 points weighted

2. **Security (30%)**
   - Critical vulnerabilities: -60 if present
   - High-risk issues: Base 90-100
   - Medium-risk issues: -5 each
   - Best practices bonus: +10
   - **Max: 100 points** × 0.30 = 30 points weighted

3. **User Experience (20%)**
   - Clarity: 30 points
   - Triggers: 30 points
   - Workflow: 30 points
   - Examples: 20 points
   - Organization: 20 points (bonus/penalty)
   - **Max: 100 points** × 0.20 = 20 points weighted

4. **Code Quality (15%)**
   - Structure: 30 points
   - Scripts: 25 points
   - Maintainability: 25 points
   - Efficiency: 20 points
   - **Max: 100 points** × 0.15 = 15 points weighted

5. **Integration & Tools (15%)**
   - Tool usage: 40 points
   - MCP integration: 30 points
   - Resource efficiency: 30 points
   - **Max: 100 points** × 0.15 = 15 points weighted

**Overall Score = Sum of weighted scores (max 100 points)**

### Grade Mapping

- **90-100 (A+/A):** Excellent
- **80-89 (B+/B):** Good
- **70-79 (C+/C):** Acceptable
- **60-69 (D):** Needs Improvement
- **0-59 (F):** Poor

### Certification Thresholds

To achieve certification:
- Overall ≥ 70/100
- Security ≥ 80/100 (CRITICAL)
- Structure ≥ 70/100
- UX ≥ 70/100
- Code Quality ≥ 60/100
- Integration ≥ 60/100
- **No CRITICAL security findings**
