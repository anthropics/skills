# Spec Format Guide

Complete reference for writing feature specifications. Every section is explained with examples, rationale, and common mistakes.

---

## The Spec Document Structure

A spec has 8 mandatory sections. If a section does not apply, write "N/A — [reason]" so reviewers know it was considered, not skipped.

```
1. Title and Metadata
2. Context
3. Functional Requirements
4. Non-Functional Requirements
5. Acceptance Criteria
6. Edge Cases and Error Scenarios
7. API Contracts
8. Data Models
9. Out of Scope
```

---

## Section 1: Title and Metadata

```markdown
# Spec: [Feature Name]

**Author:** Jane Doe
**Date:** 2026-03-25
**Status:** Draft | In Review | Approved | Superseded
**Reviewers:** John Smith, Alice Chen
**Related specs:** SPEC-018 (User Registration), SPEC-023 (Session Management)
```

### Status Lifecycle

| Status | Meaning | Who Can Change |
|--------|---------|----------------|
| Draft | Author is still writing. Not ready for review. | Author |
| In Review | Ready for feedback. Implementation blocked. | Author |
| Approved | Reviewed and accepted. Implementation may begin. | Reviewer |
| Superseded | Replaced by a newer spec. Link to replacement. | Author |

**Rule:** Implementation MUST NOT begin until status is "Approved."

---

## Section 2: Context

The context section answers: **Why does this feature exist?**

### What to Include

- The problem being solved (with evidence: support tickets, metrics, user research)
- The current state (what exists today and what is broken or missing)
- The business justification (revenue impact, cost savings, user retention)
- Constraints or dependencies (regulatory, technical, timeline)

### What to Exclude

- Implementation details (that is the engineer's job)
- Solution proposals (the spec says WHAT, not HOW)
- Lengthy background (2-4 paragraphs maximum)

### Good Example

```markdown
## Context

Users who forget their passwords currently have no self-service recovery.
Support handles ~200 password reset requests per week, consuming approximately
8 hours of agent time at $45/hour ($360/week, $18,720/year). Additionally,
12% of users who contact support for a reset never return.

This feature provides self-service password reset via email, eliminating
support burden and reducing user churn from the reset flow.
```

### Bad Example

```markdown
## Context

We need a password reset feature. Users forget their passwords sometimes
and need to reset them. We should build this.
```

**Why it is bad:** No evidence, no metrics, no business justification. "We should build this" is not a reason.

---

## Section 3: Functional Requirements — RFC 2119

### RFC 2119 Keywords

These keywords have precise meanings per [RFC 2119](https://www.ietf.org/rfc/rfc2119.txt). Do not use them casually.

| Keyword | Meaning | Testing Implication |
|---------|---------|---------------------|
| **MUST** | Absolute requirement. The implementation is non-conformant without this. | Must have a passing test. Failure = release blocker. |
| **MUST NOT** | Absolute prohibition. Doing this = broken implementation. | Must have a test proving this cannot happen. |
| **SHOULD** | Strongly recommended. Can be omitted only with documented justification. | Should have a test. Omission requires written rationale. |
| **SHOULD NOT** | Strongly discouraged. Can be done only with documented justification. | Should have a test confirming the behavior does not occur. |
| **MAY** | Truly optional. Implementer's discretion. | Test is optional. Document if implemented. |

### Writing Good Requirements

**Each requirement MUST be:**
1. **Atomic** — One behavior per requirement. Not "The system MUST authenticate users and log them in."
2. **Testable** — You can write a test that proves it works or does not.
3. **Numbered** — Sequential FR-N format for traceability.
4. **Specific** — No ambiguous adjectives ("fast", "secure", "user-friendly").

### Good Requirements

```markdown
- FR-1: The system MUST accept login via email and password.
- FR-2: The system MUST reject passwords shorter than 8 characters.
- FR-3: The system MUST return a JWT access token on successful login.
- FR-4: The system MUST NOT include the password hash in any API response.
- FR-5: The system SHOULD support "remember me" with a 30-day refresh token.
- FR-6: The system MAY display last login time on the dashboard.
```

### Bad Requirements

```markdown
- FR-1: The login system must be fast and secure.
  (Untestable: what is "fast"? What is "secure"?)

- FR-2: The system must handle all edge cases.
  (Vague: which edge cases? This delegates the spec to the implementer.)

- FR-3: Users should be able to log in easily.
  (Subjective: "easily" is not measurable.)
```

---

## Section 4: Non-Functional Requirements

Non-functional requirements define quality attributes. Every requirement needs a **measurable threshold**.

### Categories

#### Performance
```markdown
- NFR-P1: Login API MUST respond in < 500ms (p95) under 1,000 concurrent users.
- NFR-P2: Dashboard page MUST achieve Largest Contentful Paint < 2.5s.
- NFR-P3: Search results MUST return within 200ms for queries under 100 characters.
```

**Bad:** "The system should be fast." (Not measurable.)

#### Security
```markdown
- NFR-S1: All API endpoints MUST require authentication except /health and /login.
- NFR-S2: Failed login attempts MUST be rate-limited to 5 per minute per IP.
- NFR-S3: Passwords MUST be hashed with bcrypt (cost factor >= 12).
- NFR-S4: Session tokens MUST be invalidated on password change.
```

#### Accessibility
```markdown
- NFR-A1: All form inputs MUST have associated labels (WCAG 1.3.1).
- NFR-A2: Color contrast MUST meet 4.5:1 ratio (WCAG 1.4.3).
- NFR-A3: All interactive elements MUST be keyboard-navigable (WCAG 2.1.1).
```

#### Scalability
```markdown
- NFR-SC1: The system SHOULD handle 50,000 registered users.
- NFR-SC2: Database queries MUST use indexes; no full table scans on tables > 10K rows.
```

#### Reliability
```markdown
- NFR-R1: The authentication service MUST maintain 99.9% uptime (< 8.77h downtime/year).
- NFR-R2: Data MUST NOT be lost on service restart (durable storage required).
```

---

## Section 5: Acceptance Criteria — Given/When/Then

Acceptance criteria are the contract between the spec author and the implementer. They define "done."

### The Given/When/Then Pattern

```
Given [precondition — the world is in this state]
When  [action — the user or system does this]
Then  [outcome — this observable result occurs]
And   [additional outcome — and also this]
```

### Rules for Acceptance Criteria

1. **Every AC MUST reference at least one FR-* or NFR-*.** Orphaned criteria indicate missing requirements.
2. **Every AC MUST be testable by a machine.** If you cannot write an automated test, rewrite the criterion.
3. **No subjective language.** Not "should look good" but "MUST render within the design-system grid."
4. **One scenario per AC.** If you have multiple Given/When/Then blocks, split into separate ACs.

### Example: Authentication Feature

```markdown
### AC-1: Successful login (FR-1, FR-3)
Given a registered user with email "user@example.com" and password "P@ssw0rd123"
When they POST /api/auth/login with those credentials
Then they receive a 200 response with a valid JWT token
And the token expires in 24 hours
And the response includes the user's display name

### AC-2: Invalid password (FR-1)
Given a registered user with email "user@example.com"
When they POST /api/auth/login with an incorrect password
Then they receive a 401 response
And the response body contains error "INVALID_CREDENTIALS"
And no token is issued

### AC-3: Short password rejected on registration (FR-2)
Given a new user attempting to register
When they submit a password with 7 characters
Then they receive a 400 response
And the response body contains error "PASSWORD_TOO_SHORT"
And the account is not created
```

### Common Mistakes

| Mistake | Example | Fix |
|---------|---------|-----|
| Vague outcome | "Then the system works correctly" | "Then the response status is 200 and body contains {field: value}" |
| Missing precondition | "When user logs in, then token is issued" | "Given a registered user, when they POST valid credentials, then..." |
| Multiple scenarios | AC with 3 different When clauses | Split into 3 separate ACs |
| No FR reference | "AC-5: User sees dashboard" | "AC-5: User sees dashboard (FR-7)" |

---

## Section 6: Edge Cases and Error Scenarios

### What Counts as an Edge Case

- Invalid or malformed input
- External service failures (API down, timeout, rate-limited)
- Concurrent operations (race conditions)
- Boundary values (empty string, max length, zero, negative numbers)
- State conflicts (already exists, already deleted, expired)

### Format

```markdown
- EC-1: Empty email field → Return 400 with error "EMAIL_REQUIRED". Do not call auth service.
- EC-2: Email exceeds 255 characters → Return 400 with error "EMAIL_TOO_LONG".
- EC-3: OAuth provider returns 503 → Return 503 with "Service temporarily unavailable". Retry after 30s.
- EC-4: Two users register same email simultaneously → First succeeds, second gets 409 Conflict.
- EC-5: User clicks reset link after password was already changed → Show "Link already used."
```

### Coverage Rule

For every external dependency, specify at least one failure:
- Database: connection lost, timeout, constraint violation
- API: 4xx, 5xx, timeout, invalid response
- File system: file not found, permission denied, disk full
- User input: empty, too long, wrong type, injection attempt

---

## Section 7: API Contracts

### Notation

Use TypeScript-style interfaces. They are readable by both frontend and backend engineers.

```typescript
interface CreateUserRequest {
  email: string;         // MUST be valid email, max 255 chars
  password: string;      // MUST be 8-128 chars
  displayName: string;   // MUST be 1-100 chars, no HTML
  role?: "user" | "admin"; // Default: "user"
}
```

### What to Define

For each endpoint:
1. **HTTP method and path** (e.g., POST /api/users)
2. **Request body** (fields, types, constraints, defaults)
3. **Success response** (status code, body shape)
4. **Error responses** (each error code with its status and body)
5. **Headers** (Authorization, Content-Type, custom headers)

### Error Response Convention

```typescript
interface ApiError {
  error: string;         // Machine-readable code: "INVALID_CREDENTIALS"
  message: string;       // Human-readable: "The email or password is incorrect."
  details?: Record<string, string>;  // Field-level errors for validation
}
```

Always include:
- 400 for validation errors
- 401 for authentication failures
- 403 for authorization failures
- 404 for not found
- 409 for conflicts
- 429 for rate limiting
- 500 for unexpected errors (keep it generic — do not leak internals)

---

## Section 8: Data Models

### Table Format

```markdown
### User
| Field | Type | Constraints |
|-------|------|-------------|
| id | UUID | PK, auto-generated, immutable |
| email | varchar(255) | Unique, not null, valid email |
| passwordHash | varchar(60) | Not null, bcrypt, never in API responses |
| displayName | varchar(100) | Not null |
| role | enum('user','admin') | Default: 'user' |
| createdAt | timestamp | UTC, immutable, auto-set |
| updatedAt | timestamp | UTC, auto-updated |
| deletedAt | timestamp | Null unless soft-deleted |
```

### Rules

1. **Every entity in requirements MUST have a data model.** If FR-1 mentions "users", there must be a User model.
2. **Constraints MUST match requirements.** If FR-2 says passwords >= 8 chars, the model must note that.
3. **Include indexes.** If NFR-P1 says < 500ms queries, note which fields need indexes.
4. **Specify soft vs. hard delete.** State it explicitly.

---

## Section 9: Out of Scope

### Why This Section Matters

Out of Scope prevents scope creep during implementation. When someone says "while you're in there, could you also..." — point them to this section.

### Format

```markdown
- OS-1: Multi-factor authentication — Planned for Q3 (SPEC-045).
- OS-2: Social login beyond Google/GitHub — Insufficient user demand (< 2% requests).
- OS-3: Admin impersonation — Security review pending. Separate spec required.
- OS-4: Password strength meter UI — Nice-to-have, deferred to design sprint 12.
```

### Rules

1. **Every feature discussed and rejected MUST be listed.** This creates a paper trail.
2. **Include the reason.** "Not now" is not a reason. "Insufficient demand (< 2% of requests)" is.
3. **Link to future specs** when the exclusion is a deferral, not a rejection.

---

## Feature-Type Templates

### CRUD Feature

Focus on: all 4 operations, validation rules, authorization, pagination for list endpoints.

```markdown
- FR-1: Users MUST be able to create a [resource] with [required fields].
- FR-2: Users MUST be able to read a [resource] by ID.
- FR-3: Users MUST be able to list [resources] with pagination (default: 20/page).
- FR-4: Users MUST be able to update [mutable fields] of their own [resources].
- FR-5: Users MUST be able to delete their own [resources] (soft delete).
- FR-6: Users MUST NOT be able to modify or delete other users' [resources].
```

### Integration Feature

Focus on: external API contract, retry/fallback behavior, data mapping, error propagation.

```markdown
- FR-1: The system MUST call [external API] to [purpose].
- FR-2: The system MUST retry failed calls up to 3 times with exponential backoff.
- FR-3: The system MUST map [external field] to [internal field].
- FR-4: The system MUST NOT expose external API errors directly to users.
- EC-1: External API returns 5xx → Log error, return cached data if < 1h old, else 503.
- EC-2: External API response schema changes → Log warning, reject unmappable fields.
```

### Migration Feature

Focus on: backward compatibility, rollback plan, data integrity, zero-downtime deployment.

```markdown
- FR-1: The migration MUST transform [old schema] to [new schema].
- FR-2: The migration MUST be reversible (rollback script required).
- FR-3: The migration MUST NOT cause downtime exceeding 30 seconds.
- FR-4: The migration MUST validate data integrity post-run (row count, checksum).
- EC-1: Migration fails mid-way → Automatic rollback, alert ops team.
- EC-2: New schema has stricter constraints → Log invalid rows, quarantine for manual review.
```

---

## Checklist: Is This Spec Ready for Review?

- [ ] Every section is filled (or marked N/A with reason)
- [ ] All requirements use FR-N, NFR-N numbering
- [ ] RFC 2119 keywords are UPPERCASE
- [ ] Every AC references at least one requirement
- [ ] Every AC uses Given/When/Then
- [ ] Edge cases cover each external dependency failure
- [ ] API contracts define success AND error responses
- [ ] Data models include all entities from requirements
- [ ] Out of Scope lists items discussed and rejected
- [ ] No placeholder text remains
- [ ] Context includes evidence (metrics, tickets, research)
- [ ] Status is "In Review" (not still "Draft")

---

## Full Example: Password Reset

A complete spec demonstrating all sections, followed by extracted test stubs.

### The Spec

```markdown
# Spec: Password Reset Flow

**Author:** Engineering Team
**Date:** 2026-03-25
**Status:** Approved

## Context

Users who forget their passwords currently have no self-service recovery option.
Support receives ~200 password reset requests per week, costing approximately
8 hours of support time. This feature eliminates that burden entirely.

## Functional Requirements

- FR-1: The system MUST allow users to request a password reset via email.
- FR-2: The system MUST send a reset link that expires after 1 hour.
- FR-3: The system MUST invalidate all previous reset links when a new one is requested.
- FR-4: The system MUST enforce minimum password length of 8 characters on reset.
- FR-5: The system MUST NOT reveal whether an email exists in the system.
- FR-6: The system SHOULD log all reset attempts for audit purposes.

## Acceptance Criteria

### AC-1: Request reset (FR-1, FR-5)
Given a user on the password reset page
When they enter any email address and submit
Then they see "If an account exists, a reset link has been sent"
And the response is identical whether the email exists or not

### AC-2: Valid reset link (FR-2)
Given a user who received a reset email 30 minutes ago
When they click the reset link
Then they see the password reset form

### AC-3: Expired reset link (FR-2)
Given a user who received a reset email 2 hours ago
When they click the reset link
Then they see "This link has expired. Please request a new one."

### AC-4: Previous links invalidated (FR-3)
Given a user who requested two reset emails
When they click the link from the first email
Then they see "This link is no longer valid."

## Edge Cases

- EC-1: User submits reset for non-existent email → Same success message (FR-5).
- EC-2: User clicks reset link twice → Second click shows "already used" if password was changed.
- EC-3: Email delivery fails → Log error, do not retry automatically.
- EC-4: User requests reset while already logged in → Allow it, do not force logout.

## Out of Scope

- OS-1: Security questions as alternative reset method.
- OS-2: SMS-based password reset.
- OS-3: Admin-initiated password reset (separate spec).
```

### Extracted Test Cases

Generated by `test_extractor.py --framework pytest`:

```python
class TestPasswordReset:
    def test_ac1_request_reset_existing_email(self):
        """AC-1: Request reset with existing email shows generic message."""
        # Given a user on the password reset page
        # When they enter a registered email and submit
        # Then they see "If an account exists, a reset link has been sent"
        raise NotImplementedError("Implement this test")

    def test_ac1_request_reset_nonexistent_email(self):
        """AC-1: Request reset with unknown email shows same generic message."""
        # Given a user on the password reset page
        # When they enter an unregistered email and submit
        # Then they see identical response to existing email case
        raise NotImplementedError("Implement this test")

    def test_ac2_valid_reset_link(self):
        """AC-2: Reset link works within expiry window."""
        raise NotImplementedError("Implement this test")

    def test_ac3_expired_reset_link(self):
        """AC-3: Reset link rejected after 1 hour."""
        raise NotImplementedError("Implement this test")

    def test_ac4_previous_links_invalidated(self):
        """AC-4: Old reset links stop working when new one is requested."""
        raise NotImplementedError("Implement this test")

    def test_ec1_nonexistent_email_same_response(self):
        """EC-1: Non-existent email produces identical response."""
        raise NotImplementedError("Implement this test")

    def test_ec2_reset_link_used_twice(self):
        """EC-2: Already-used reset link shows appropriate message."""
        raise NotImplementedError("Implement this test")
```
