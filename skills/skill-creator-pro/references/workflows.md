# Workflow Patterns

Sequential, conditional, and complex workflow patterns for skills.

---

## Sequential Workflows

Break complex tasks into clear, sequential steps with overview:

```markdown
## Workflow Overview

Processing a document involves:

1. **Validate** - Check file format and permissions
2. **Parse** - Extract content and structure
3. **Transform** - Apply requested changes
4. **Verify** - Confirm output matches expectations
5. **Deliver** - Return result to user
```

### With Scripts

```markdown
Filling a PDF form involves these steps:

1. Analyze the form (run `scripts/analyze_form.py`)
2. Create field mapping (edit `fields.json`)
3. Validate mapping (run `scripts/validate_fields.py`)
4. Fill the form (run `scripts/fill_form.py`)
5. Verify output (run `scripts/verify_output.py`)
```

### With Checkpoints

```markdown
## Data Migration Workflow

### Phase 1: Preparation
1. [ ] Backup existing data
2. [ ] Verify backup integrity
3. [ ] Document current schema

### Phase 2: Migration
4. [ ] Run migration script
5. [ ] Verify row counts match
6. [ ] Validate data integrity

### Phase 3: Verification
7. [ ] Run integration tests
8. [ ] Compare sample records
9. [ ] Sign off on migration
```

---

## Conditional Workflows

Guide through decision points with clear branching:

### Simple Branch

```markdown
## Workflow

1. Determine the operation type:
   - **Creating new content?** → Follow "Creation Workflow" below
   - **Editing existing content?** → Follow "Editing Workflow" below

---

## Creation Workflow
1. Generate template
2. Fill with content
3. Validate structure
4. Save output

---

## Editing Workflow
1. Load existing file
2. Parse current content
3. Apply modifications
4. Validate changes
5. Save updated file
```

### Decision Tree

```markdown
## Authentication Flow

1. Check authentication method:

   **OAuth?**
   ├── Get authorization URL
   ├── Redirect user
   ├── Handle callback
   └── Store tokens

   **API Key?**
   ├── Validate key format
   ├── Check permissions
   └── Store in secure config

   **Username/Password?**
   ├── Validate credentials
   ├── Generate session token
   └── Set secure cookie
```

### With Fallbacks

```markdown
## Content Retrieval

1. Try primary source:
   - **Success** → Return content, done
   - **Failure** → Continue to step 2

2. Try cache:
   - **Hit** → Return cached, done
   - **Miss** → Continue to step 3

3. Try fallback source:
   - **Success** → Return content, update cache
   - **Failure** → Return error with guidance
```

---

## Complex Workflows

### Parallel Steps

```markdown
## Deployment Workflow

### Sequential: Preparation
1. Run tests
2. Build artifacts

### Parallel: Deployment (run simultaneously)
- Deploy to Region A
- Deploy to Region B
- Deploy to Region C

### Sequential: Verification
3. Run smoke tests
4. Enable traffic
```

### State Machine

```markdown
## Order Processing States

```
[Created] → [Validated] → [Processing] → [Completed]
    ↓           ↓             ↓
[Cancelled] [Rejected]    [Failed]
```

### Transitions

| From | To | Trigger |
|------|-----|---------|
| Created | Validated | Validation passes |
| Created | Cancelled | User cancels |
| Validated | Processing | Payment confirmed |
| Validated | Rejected | Validation fails |
| Processing | Completed | Fulfillment done |
| Processing | Failed | Error during fulfillment |
```

### Iterative Workflows

```markdown
## Refinement Workflow

1. Generate initial output
2. Evaluate against criteria
3. If criteria not met:
   - Identify gaps
   - Apply improvements
   - Return to step 2
4. If criteria met:
   - Finalize output
   - Deliver result

**Maximum iterations**: 3 (prevent infinite loops)
```

---

## Workflow Documentation Best Practices

### DO: Clear Entry/Exit Criteria

```markdown
## Workflow: Code Review

### Entry Criteria
- [ ] PR created with description
- [ ] Tests passing
- [ ] No merge conflicts

### Steps
1. Review code changes
2. Check test coverage
3. Verify documentation
4. Provide feedback

### Exit Criteria
- [ ] All comments resolved
- [ ] Approved by reviewer
- [ ] CI/CD passing
```

### DO: Error Recovery

```markdown
## If Step Fails

| Step | Failure | Recovery |
|------|---------|----------|
| 1. Parse | Invalid format | Show format requirements, ask for correct file |
| 2. Validate | Missing fields | List missing fields, request completion |
| 3. Process | Timeout | Retry once, then report with partial results |
| 4. Save | Permission denied | Suggest alternative location |
```

### DON'T: Vague Steps

```markdown
## Bad Example

1. Do the thing
2. Check if it worked
3. Fix problems
4. Finish up
```

### DO: Specific Steps

```markdown
## Good Example

1. Run `validate.py input.json` to check format
2. Verify output shows "Valid: true"
3. If errors shown, fix issues listed in output
4. Run `process.py input.json output.json`
```
