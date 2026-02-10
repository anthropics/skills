# Output Patterns

Template patterns and example-driven guidance for consistent output.

---

## Template Pattern

Provide templates for output format. Match strictness to requirements.

### Strict Template (Exact Format Required)

```markdown
## Report Structure

ALWAYS use this exact template:

```markdown
# [Analysis Title]

## Executive Summary
[One-paragraph overview of key findings - 3-5 sentences]

## Key Findings
1. **Finding 1**: [Description with supporting data]
2. **Finding 2**: [Description with supporting data]
3. **Finding 3**: [Description with supporting data]

## Recommendations
1. [Specific actionable recommendation]
2. [Specific actionable recommendation]
3. [Specific actionable recommendation]

## Appendix
[Supporting data, charts, or detailed analysis]
```
```

### Flexible Template (Guidance with Room for Adaptation)

```markdown
## Report Structure

Default format (adapt sections as needed):

```markdown
# [Analysis Title]

## Executive Summary
[Overview - adjust length based on complexity]

## Key Findings
[Organize by theme, priority, or chronology as appropriate]

## Recommendations
[Tailor to specific context and audience]
```

Adjust sections based on:
- Audience (technical vs executive)
- Complexity (simple vs comprehensive)
- Purpose (decision support vs documentation)
```

---

## Examples Pattern

Show input/output pairs for quality guidance.

### Code Generation Examples

```markdown
## Function Naming

**Example 1:**
Input: Function that validates email format
Output:
```typescript
function validateEmail(email: string): boolean {
  const pattern = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  return pattern.test(email);
}
```

**Example 2:**
Input: Function that fetches user by ID
Output:
```typescript
async function getUserById(id: string): Promise<User | null> {
  const response = await db.users.findUnique({ where: { id } });
  return response;
}
```

Follow this style: verb + noun, camelCase, explicit return types.
```

### Commit Message Examples

```markdown
## Commit Message Format

**Example 1:**
Input: Added user authentication with JWT tokens
Output:
```
feat(auth): implement JWT-based authentication

Add login endpoint and token validation middleware.
Includes refresh token rotation for security.
```

**Example 2:**
Input: Fixed bug where dates displayed incorrectly
Output:
```
fix(reports): correct date formatting in timezone conversion

Use UTC timestamps consistently across report generation.
Fixes #234.
```

Format: `type(scope): brief description`

Types: feat, fix, docs, style, refactor, test, chore
```

---

## Good/Bad Examples Pattern

Show correct and incorrect patterns with explanations.

### Error Handling

```markdown
## Error Handling Examples

### Good Example
```typescript
async function fetchUser(id: string): Promise<Result<User>> {
  try {
    const user = await api.getUser(id);
    if (!user) {
      return { ok: false, error: 'User not found' };
    }
    return { ok: true, data: user };
  } catch (error) {
    logger.error('Failed to fetch user', { id, error });
    return { ok: false, error: 'Failed to fetch user' };
  }
}
```

**Why it's good:**
- Explicit error handling
- Logging for debugging
- Typed return value
- User-friendly error message

### Bad Example (Don't Do This)
```typescript
async function fetchUser(id: string) {
  const user = await api.getUser(id);  // Unhandled rejection
  return user;  // Returns undefined if not found
}
```

**Why it's bad:**
- No error handling
- Caller can't distinguish "not found" from error
- No logging for debugging
```

### Input Validation

```markdown
## Input Validation Examples

### Good Example
```typescript
const CreateUserSchema = z.object({
  name: z.string().min(1, 'Name required').max(100),
  email: z.string().email('Invalid email format'),
  age: z.number().int().min(0).max(150).optional(),
});

function createUser(input: unknown) {
  const result = CreateUserSchema.safeParse(input);
  if (!result.success) {
    return { error: result.error.format() };
  }
  return saveUser(result.data);
}
```

### Bad Example (Don't Do This)
```typescript
function createUser(input: any) {
  // No validation - vulnerable to injection, crashes
  return saveUser(input);
}
```
```

---

## Output Specification Pattern

Define expected output characteristics.

### Widget Output Specification

```markdown
## Widget Output Specification

Every generated widget includes:

### Required Elements
- [ ] Container with theme-aware styles
- [ ] Data binding to window.openai.toolOutput
- [ ] Loading state (shown before data arrives)
- [ ] Error state (shown when data.isError)
- [ ] Empty state (shown when no data)

### Code Structure
```typescript
// Required structure
function Widget() {
  const data = window.openai?.toolOutput;
  const theme = window.openai?.theme ?? 'light';

  if (!data) return <LoadingState />;
  if (data.isError) return <ErrorState message={data.error} />;
  if (isEmpty(data)) return <EmptyState />;

  return <MainContent data={data} theme={theme} />;
}
```

### Style Requirements
- System fonts only (no custom fonts)
- Theme-aware colors (light/dark)
- Responsive breakpoints (mobile + desktop)
- WCAG AA contrast ratios
```

### API Response Specification

```markdown
## API Response Specification

All responses follow this structure:

### Success Response
```json
{
  "success": true,
  "data": { ... },
  "meta": {
    "timestamp": "ISO-8601",
    "requestId": "uuid"
  }
}
```

### Error Response
```json
{
  "success": false,
  "error": {
    "code": "ERROR_CODE",
    "message": "Human-readable message",
    "details": { ... }
  },
  "meta": {
    "timestamp": "ISO-8601",
    "requestId": "uuid"
  }
}
```

### Pagination
```json
{
  "success": true,
  "data": [...],
  "pagination": {
    "page": 1,
    "pageSize": 20,
    "total": 100,
    "hasMore": true
  }
}
```
```

---

## Consistency Patterns

### Naming Conventions

```markdown
## Naming Conventions

| Type | Convention | Example |
|------|------------|---------|
| Files | kebab-case | `user-service.ts` |
| Functions | camelCase | `getUserById` |
| Classes | PascalCase | `UserService` |
| Constants | UPPER_SNAKE | `MAX_RETRIES` |
| Types | PascalCase | `UserResponse` |
| CSS classes | kebab-case | `user-card` |
```

### File Structure

```markdown
## File Structure Convention

```
src/
├── components/       # React components
│   ├── Button/
│   │   ├── Button.tsx
│   │   ├── Button.test.tsx
│   │   └── index.ts
├── hooks/           # Custom hooks
├── services/        # API/business logic
├── utils/           # Helper functions
├── types/           # TypeScript types
└── index.ts         # Public exports
```
```
