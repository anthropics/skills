---
name: code-review-guide
description: Guide structured code reviews with security, performance, and quality checklists. Use when users need to review code changes, provide constructive feedback on pull requests, or establish code review standards. Triggers on requests like "review this code", "code review checklist", "PR feedback", "review standards", or "what to look for in code review".
---

# Code Review Guide

Conduct thorough, constructive code reviews that improve quality without blocking progress.

## Review Priorities

Focus areas in order of importance:

```
1. CORRECTNESS   → Does it work? Does it handle edge cases?
2. SECURITY      → Any vulnerabilities introduced?
3. DESIGN        → Right abstraction? Maintainable?
4. PERFORMANCE   → Obvious inefficiencies?
5. STYLE         → Readable? Follows conventions?
```

## Quick Review Checklist

### Correctness
- [ ] Logic handles expected cases correctly
- [ ] Edge cases considered (null, empty, boundaries)
- [ ] Error conditions handled appropriately
- [ ] Tests cover the changes
- [ ] Changes match the stated intent/ticket

### Security
- [ ] No secrets/credentials in code
- [ ] Input validated before use
- [ ] SQL queries parameterized
- [ ] User input escaped in output (XSS)
- [ ] Authorization checks present
- [ ] Sensitive data not logged

### Design
- [ ] Single responsibility maintained
- [ ] No unnecessary coupling introduced
- [ ] Abstractions at appropriate level
- [ ] No code duplication added
- [ ] Changes are reversible

### Performance
- [ ] No obvious N+1 queries
- [ ] Large datasets paginated
- [ ] Expensive operations cached or async
- [ ] No blocking calls in hot paths

### Readability
- [ ] Names clearly express intent
- [ ] Complex logic has explanatory comments
- [ ] Functions are focused and small
- [ ] Code matches existing patterns

## Comment Guidelines

### Be Specific, Not Vague

```markdown
# Bad
"This is confusing"

# Good
"The variable name `data` doesn't indicate what it contains.
Consider `userProfiles` to match the return type."
```

### Suggest, Don't Demand

```markdown
# Bad
"Change this to use map()"

# Good
"Consider using `map()` here - it would eliminate the
temporary array and express the transformation more directly."
```

### Explain the Why

```markdown
# Bad
"Don't use var"

# Good
"Prefer `const` here since the value never changes.
This signals intent to future readers and prevents accidental reassignment."
```

### Use Conventional Prefixes

| Prefix | Meaning |
|--------|---------|
| `nit:` | Minor style issue, not blocking |
| `suggestion:` | Optional improvement |
| `question:` | Need clarification |
| `issue:` | Needs to be addressed |
| `blocking:` | Must fix before merge |

### Example Comments

```markdown
**blocking:** This SQL query is vulnerable to injection.
Use parameterized queries instead:
`db.query('SELECT * FROM users WHERE id = ?', [userId])`

**suggestion:** Consider extracting this into a named function -
it would improve readability and make testing easier.

**nit:** Missing trailing comma on line 47 (our style guide prefers them).

**question:** What happens if `response.data` is undefined?
Might need a null check.
```

## Security Deep-Dive

### Injection Vulnerabilities

```javascript
// SQL Injection - VULNERABLE
const query = `SELECT * FROM users WHERE id = ${userId}`;

// SQL Injection - SAFE
const query = 'SELECT * FROM users WHERE id = ?';
db.query(query, [userId]);
```

```javascript
// Command Injection - VULNERABLE
exec(`ls ${userInput}`);

// Command Injection - SAFE
execFile('ls', [userInput]);
```

### Cross-Site Scripting (XSS)

```javascript
// XSS - VULNERABLE
element.innerHTML = userComment;

// XSS - SAFE
element.textContent = userComment;
// Or use a sanitization library
```

### Authentication/Authorization

Questions to ask:
- Is the user authenticated for this endpoint?
- Is the user authorized for this specific resource?
- Are admin functions properly protected?
- Is session handling secure?

### Data Exposure

Watch for:
- Logging sensitive data (passwords, tokens, PII)
- Returning more data than needed in API responses
- Error messages revealing system internals
- Stack traces exposed to users

## Performance Patterns

### Database Queries

```python
# N+1 Query - INEFFICIENT
for user in users:
    orders = get_orders(user.id)  # Query per user!

# Eager Loading - BETTER
users = get_users_with_orders()  # Single query with JOIN
```

### Memory Usage

```javascript
// Loading entire dataset - PROBLEMATIC
const allUsers = await db.getAllUsers(); // 1M users in memory!

// Pagination - BETTER
const users = await db.getUsers({ limit: 100, offset: page * 100 });

// Streaming - BEST for large datasets
const stream = db.getUserStream();
stream.on('data', processUser);
```

### Async Operations

```javascript
// Sequential - SLOW
const a = await fetchA();
const b = await fetchB();
const c = await fetchC();

// Parallel - FASTER
const [a, b, c] = await Promise.all([
  fetchA(),
  fetchB(),
  fetchC()
]);
```

## Design Smell Detection

### Too Many Parameters

```python
# Smell: Long parameter list
def create_user(name, email, age, address, city, country, phone, role):
    ...

# Better: Group related data
def create_user(user_info: UserInfo, contact: ContactInfo):
    ...
```

### Mixed Abstraction Levels

```python
# Smell: High and low-level operations mixed
def process_order(order):
    validate(order)
    conn = psycopg2.connect(...)  # Low-level DB details
    cursor = conn.cursor()
    cursor.execute(...)           # SQL in business logic
    send_email(order.customer)

# Better: Consistent abstraction
def process_order(order):
    validate(order)
    repository.save(order)        # Abstracted data access
    notifications.order_confirmed(order)
```

### Boolean Parameter Smell

```python
# Smell: Boolean changes function behavior
def get_users(include_inactive=False):
    ...

# Consider: Explicit separate functions or enum
def get_active_users():
    ...
def get_all_users():
    ...
```

## Review Workflow

### Before Reviewing

1. Understand the context (read PR description, linked issue)
2. Check if tests pass in CI
3. Review the overall change size (large PRs need more time)

### During Review

1. Start with the test files (understand intended behavior)
2. Review main logic changes
3. Check integration points (API changes, database changes)
4. Look for missing edge cases

### Completing Review

- **Approve**: Good to merge, minor feedback can be addressed after
- **Request Changes**: Blocking issues that need resolution
- **Comment**: Questions or discussion, not blocking

### After Review

- Respond promptly to author's questions
- Don't nitpick on follow-up commits
- Trust the author to address feedback appropriately

## Anti-Patterns in Reviews

| Anti-Pattern | Problem | Instead |
|--------------|---------|---------|
| "Just do X" | Dismissive | Explain the reasoning |
| "I would have..." | Preference, not issue | Ask if there's a reason |
| Style crusade | Blocks progress | Use automated linting |
| Rubber stamp | Misses issues | Take time, be thorough |
| Gatekeeping | Demoralizing | Focus on teaching |

## Receiving Reviews

When your code is reviewed:
- Assume good intent
- Ask for clarification if feedback is unclear
- Don't take feedback personally
- Thank reviewers for thorough reviews
- Address all comments (even if just "acknowledged")
