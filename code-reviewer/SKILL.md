---
name: code-reviewer
description: Use this skill to perform systematic code reviews with best practices, checking for bugs, security issues, performance problems, and code quality
license: Apache-2.0
---

# Code Reviewer

A comprehensive code review skill that systematically analyzes code for quality, security, performance, and maintainability issues.

## When to Use

Use this skill when:
- The user explicitly requests a code review
- The user asks to "review", "check", or "analyze" code
- The user wants to improve code quality
- The user needs feedback on their implementation
- You've completed a significant code change and want to validate it

## Review Process

### Step 1: Understand Context

1. **Identify what to review:**
   - If user specified files, review those
   - If no files specified, ask the user which files to review
   - Use Glob to find relevant files if pattern provided

2. **Understand the purpose:**
   - What does this code do?
   - What problem does it solve?
   - What are the requirements?

### Step 2: Systematic Analysis

Review the code in this order, checking each category:

#### 2.1 Correctness & Bugs

- **Logic errors**: Does the code do what it's supposed to?
- **Edge cases**: Are boundary conditions handled?
- **Null/undefined handling**: Are nil values checked?
- **Error handling**: Are errors caught and handled appropriately?
- **Off-by-one errors**: Are array indices and loops correct?

#### 2.2 Security Issues

- **Input validation**: Is user input validated and sanitized?
- **SQL injection**: Are database queries parameterized?
- **XSS vulnerabilities**: Is output properly escaped?
- **Authentication/authorization**: Are permissions checked?
- **Secrets exposure**: Are API keys, passwords, or tokens hardcoded?
- **CSRF protection**: Are state-changing operations protected?
- **Dependency vulnerabilities**: Are dependencies up to date and secure?

#### 2.3 Performance

- **Algorithmic complexity**: Can O(n²) be reduced to O(n)?
- **Database queries**: Are there N+1 query problems?
- **Caching opportunities**: Should results be cached?
- **Memory leaks**: Are resources properly released?
- **Unnecessary work**: Is redundant computation performed?
- **Large data handling**: Are large datasets processed efficiently?

#### 2.4 Code Quality

**Readability:**
- Are variable and function names clear and descriptive?
- Is the code easy to understand?
- Are complex sections commented?
- Is the formatting consistent?

**Maintainability:**
- Is the code DRY (Don't Repeat Yourself)?
- Are functions focused and single-purpose?
- Is complexity manageable (cyclomatic complexity)?
- Are magic numbers replaced with named constants?

**Architecture:**
- Does it follow established patterns?
- Are concerns properly separated?
- Is coupling minimized?
- Is cohesion maximized?

**Testing:**
- Are there adequate tests?
- Are edge cases tested?
- Is error handling tested?
- Are tests clear and maintainable?

#### 2.5 Best Practices

**Language-specific best practices:**

**Python:**
- PEP 8 compliance
- Type hints used where appropriate
- Context managers for resources
- List comprehensions over loops (when clearer)

**JavaScript/TypeScript:**
- Modern ES6+ syntax
- Proper async/await usage
- No var, use const/let
- TypeScript types properly defined

**Go:**
- Proper error handling patterns
- Goroutine and channel usage
- Interface usage appropriate
- defer for cleanup

**Java:**
- Exception handling appropriate
- Stream API usage
- Null handling (Optional)
- Resource management (try-with-resources)

**Rust:**
- Ownership and borrowing correct
- Error handling with Result
- No unnecessary clones
- Lifetime annotations appropriate

### Step 3: Prioritize Findings

Categorize issues by severity:

**Critical (🔴):**
- Security vulnerabilities
- Data loss risks
- Crash/error conditions
- Major bugs

**High (🟡):**
- Performance problems
- Maintainability issues
- Moderate bugs
- Missing error handling

**Medium (🟠):**
- Code quality improvements
- Minor bugs
- Style inconsistencies
- Missing tests

**Low (🟢):**
- Nitpicks
- Optional refactoring
- Documentation suggestions

### Step 4: Provide Constructive Feedback

For each issue found:

1. **Explain the problem** clearly
2. **Show the specific code** location (file:line)
3. **Explain why** it's an issue
4. **Suggest a solution** with example code
5. **Provide context** (e.g., links to best practices)

**Example Format:**

```
🔴 CRITICAL: SQL Injection Vulnerability

Location: src/database/users.py:45

Problem:
The user input is directly interpolated into the SQL query, allowing SQL injection attacks.

Current code:
```python
query = f"SELECT * FROM users WHERE email = '{email}'"
cursor.execute(query)
```

Why it's a problem:
An attacker could input `admin@example.com' OR '1'='1` to bypass authentication.

Recommended fix:
Use parameterized queries:
```python
query = "SELECT * FROM users WHERE email = ?"
cursor.execute(query, (email,))
```

Reference: https://owasp.org/www-community/attacks/SQL_Injection
```

### Step 5: Positive Feedback

Also note what's done well:
- Good practices followed
- Clean code patterns
- Effective solutions
- Well-tested areas

This provides balanced, constructive feedback.

### Step 6: Summary and Recommendations

Provide a summary at the end:

1. **Overall assessment**: Brief quality rating
2. **Critical items**: Must-fix issues
3. **Recommended improvements**: High-priority items
4. **Nice-to-haves**: Optional improvements
5. **Positive notes**: What's done well

## Review Output Format

Structure your review as:

```
# Code Review: [Component/Feature Name]

## Summary
[Brief overview of what was reviewed and overall quality]

## Critical Issues (🔴)
[List critical issues with details]

## High Priority (🟡)
[List high-priority issues with details]

## Medium Priority (🟠)
[List medium-priority issues with details]

## Low Priority (🟢)
[List low-priority suggestions]

## Positive Notes ✅
[What's done well]

## Overall Recommendations
[Summary and next steps]
```

## Guidelines

- **Be constructive**: Focus on improvement, not criticism
- **Be specific**: Reference exact files and line numbers
- **Provide examples**: Show good and bad code
- **Explain reasoning**: Don't just say "this is wrong", explain why
- **Consider context**: Understand project constraints
- **Be balanced**: Note both problems and good practices
- **Prioritize**: Don't overwhelm with minor issues
- **Be actionable**: Give clear steps to fix

## Error Handling

- If files don't exist, inform the user and ask for correct paths
- If code language is unclear, ask for clarification
- If scope is too large, suggest breaking into smaller reviews
- If you don't understand the requirements, ask questions

## Examples

### Example 1: Security Review Request

User: "Review auth.py for security issues"

Response:
1. Read auth.py
2. Focus on security aspects:
   - Authentication implementation
   - Password handling
   - Session management
   - Input validation
3. Provide detailed security findings
4. Prioritize by risk level

### Example 2: General Code Review

User: "Review my recent changes in src/api/"

Response:
1. Use Glob to find files in src/api/
2. Review each file systematically
3. Check all categories (correctness, security, performance, quality)
4. Provide comprehensive feedback
5. Summarize findings

### Example 3: Performance Review

User: "This function is slow, can you review it?"

Response:
1. Read the function code
2. Analyze algorithmic complexity
3. Identify bottlenecks
4. Suggest optimizations with examples
5. Explain expected performance improvement
