# Quality Patterns

Patterns for clarifications, enforcement checklists, and quality gates.

---

## User Interaction Patterns

### Clarification Questions

Structure clarifications as Required vs Optional:

```markdown
## Required Clarifications

Before proceeding, ask:

1. **Data shape**: "What structure will the input have?"
   ```json
   Example: { items: [...], total: 10 }
   ```

2. **Action type**: "Read-only or write operations?"
   - Read → Simple rendering
   - Write → Need form handling, validation

3. **Output format**: "What should the result look like?"

## Optional Clarifications

4. **Styling**: "Any design preferences?" (ask if complex UI)
5. **Performance**: "Expected data volume?" (ask if potentially large)
```

### Context Awareness

Before asking, check existing context:

```markdown
## Before Asking

1. Review conversation history for prior answers
2. Infer from file names/content when possible
3. Check available data structures
4. Only ask what cannot be determined

Example: If user says "create a progress widget for my course app",
infer it's a Builder skill for education domain before asking.
```

### Graceful Handling

What to do when user doesn't answer:

```markdown
## If User Skips Clarifications

- **Required questions**: Explain why needed, ask again simply
- **Optional questions**: Proceed with sensible defaults
- **Ambiguous answers**: Confirm interpretation before proceeding
```

---

## Official Documentation Links

### Documentation Table Pattern

```markdown
## Official Documentation

| Resource | URL | Use For |
|----------|-----|---------|
| Getting Started | https://docs.example.com/start | Basic setup |
| API Reference | https://docs.example.com/api | Method details |
| Best Practices | https://docs.example.com/best | Patterns |
| Examples | https://github.com/example/examples | Reference code |

For patterns not covered here, fetch from official docs.
```

### Fetch Guidance Pattern

```markdown
## Unlisted Scenarios

For patterns not documented in this skill:

1. Fetch from official docs: [primary URL]
2. Apply same quality standards as this skill
3. Follow established patterns

Examples of when to fetch:
- Complex authentication flows
- Third-party integrations
- Platform-specific features
- New API versions
```

### Version Awareness

```markdown
## Keeping Current

- Official docs: [URL]
- Changelog: [URL]
- Last verified: 2024-12

When docs update:
1. Check for breaking changes
2. Update affected references
3. Verify examples still work
```

---

## Domain Standards Enforcement

### Must Follow / Must Avoid Pattern

```markdown
## Standards Enforcement

### Must Follow
- [ ] WCAG AA contrast (4.5:1 for text, 3:1 for UI)
- [ ] Keyboard navigation for all interactions
- [ ] Focus indicators visible
- [ ] Screen reader labels for icons
- [ ] Error states with clear messages

### Must Avoid
- Color as only indicator
- Mouse-only interactions
- Auto-playing media without controls
- Nested scrolling
- Hardcoded strings
```

### Domain-Specific Examples

**Web Accessibility (WCAG)**:
```markdown
### Must Follow
- [ ] 4.5:1 contrast ratio for text
- [ ] 3:1 contrast ratio for UI components
- [ ] Keyboard accessible
- [ ] Focus visible
- [ ] Alt text for images

### Must Avoid
- Color-only indicators
- Keyboard traps
- Auto-playing audio
```

**API Security (OWASP)**:
```markdown
### Must Follow
- [ ] Input validation on all endpoints
- [ ] Parameterized queries (no SQL injection)
- [ ] Authentication on protected routes
- [ ] Rate limiting
- [ ] HTTPS only

### Must Avoid
- Hardcoded secrets
- SQL string concatenation
- Verbose error messages to clients
- Sensitive data in logs
```

**Code Quality**:
```markdown
### Must Follow
- [ ] TypeScript strict mode
- [ ] Explicit return types
- [ ] Error handling with try/catch
- [ ] Meaningful variable names

### Must Avoid
- `any` type
- Ignored errors
- Magic numbers
- Deep nesting (>3 levels)
```

---

## Quality Gates

### Output Checklist Pattern

```markdown
## Output Checklist

Before delivering, verify ALL items:

### Functional
- [ ] Core feature works as specified
- [ ] Error states handled gracefully
- [ ] Loading states present (if async)
- [ ] Edge cases covered

### Quality
- [ ] Follows naming conventions
- [ ] No hardcoded values
- [ ] Comments where logic is non-obvious
- [ ] Consistent formatting

### Standards
- [ ] Passes domain requirements (above)
- [ ] Tested against acceptance criteria
- [ ] No security vulnerabilities
```

### Skill-Specific Checklists

**Widget Output Checklist**:
```markdown
## Widget Output Checklist

### Functional
- [ ] window.openai data access with null checks
- [ ] Event listener for openai:set_globals
- [ ] Loading state before data
- [ ] Error state when data.isError
- [ ] Empty state when no data

### Visual
- [ ] Theme support (light/dark)
- [ ] System fonts
- [ ] WCAG AA contrast
- [ ] Responsive layout
- [ ] Focus indicators

### UX
- [ ] Follows "Extract, Don't Port"
- [ ] Inline mode unless justified
- [ ] ≤2 actions per card
```

**Script Output Checklist**:
```markdown
## Script Output Checklist

### Functional
- [ ] Runs without errors on sample input
- [ ] Handles missing/invalid input gracefully
- [ ] Produces expected output format
- [ ] Cleans up temporary files

### Quality
- [ ] Clear usage instructions
- [ ] Documented parameters
- [ ] Meaningful error messages
- [ ] Exit codes for automation
```

---

## Good/Bad Examples Pattern

Always include both correct and incorrect patterns:

```markdown
### Good Example
```python
# Correct: Explicit error handling
try:
    result = process_file(path)
    return {"success": True, "data": result}
except FileNotFoundError:
    return {"success": False, "error": "File not found"}
except Exception as e:
    logger.error(f"Processing failed: {e}")
    return {"success": False, "error": "Processing failed"}
```

### Bad Example (Don't Do This)
```python
# Wrong: Silently ignores errors
try:
    result = process_file(path)
except:
    pass  # Never do this - errors are hidden
```
```
