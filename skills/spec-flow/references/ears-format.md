# EARS Requirements Format

EARS (Easy Approach to Requirements Syntax) is a structured template system for writing clear, unambiguous requirements.

## Why EARS?

Traditional requirements often suffer from:

- Ambiguity ("the system should be fast")
- Incompleteness (missing edge cases)
- Untestability (no clear pass/fail criteria)

EARS provides templates that force precision and completeness.

## The Five EARS Patterns

### 1. Ubiquitous Requirements

**Template**: `The <system> shall <action>.`

**Use When**: The requirement is always true, regardless of state or event.

**Examples**:

```
✅ The system shall encrypt all passwords using bcrypt with cost factor 12.
✅ The API shall return JSON responses with Content-Type: application/json.
✅ The database shall maintain referential integrity.

❌ The system should be secure. (too vague)
❌ The system shall be fast. (not measurable)
```

**Characteristics**:
- Always active
- No triggering event
- No precondition

### 2. Event-Driven Requirements

**Template**: `When <trigger>, the <system> shall <action>.`

**Use When**: The requirement responds to a specific event or trigger.

**Examples**:

```
✅ When the user submits the login form, the system shall validate credentials within 200ms.
✅ When a payment fails, the system shall retry up to 3 times with exponential backoff.
✅ When file upload exceeds 10MB, the system shall reject with error code FILE_TOO_LARGE.

❌ When the user clicks submit, validate the form. (missing system subject)
❌ When needed, the system shall scale. (vague trigger)
```

**Characteristics**:
- Triggered by specific event
- Clear cause-effect relationship
- Event should be observable

### 3. State-Driven Requirements

**Template**: `While <state>, the <system> shall <action>.`

**Use When**: The requirement is active only during a specific state.

**Examples**:

```
✅ While the user is authenticated, the system shall include auth token in API headers.
✅ While maintenance mode is active, the system shall return 503 for all requests.
✅ While the cart contains items, the system shall display the checkout button.

❌ While running, the system shall work correctly. (tautology)
❌ While active, send data. (vague state, missing system)
```

**Characteristics**:
- Active during a condition
- Continuous behavior
- State should be verifiable

### 4. Unwanted Behavior (Negative Requirements)

**Template**: `If <condition>, then the <system> shall NOT <action>.`

**Use When**: Specifying what the system must prevent.

**Examples**:

```
✅ If the session has expired, then the system shall NOT process the request.
✅ If the user lacks admin role, then the system shall NOT display admin controls.
✅ If the rate limit is exceeded, then the system shall NOT process additional requests.

❌ The system shall not crash. (too broad)
❌ If something goes wrong, handle it. (vague)
```

**Characteristics**:
- Prevents undesired behavior
- Explicit condition
- Security/safety critical

### 5. Optional Features

**Template**: `Where <feature/option>, the <system> shall <action>.`

**Use When**: The requirement depends on configuration or feature flags.

**Examples**:

```
✅ Where dark mode is enabled, the system shall use the dark color palette.
✅ Where two-factor authentication is configured, the system shall require OTP.
✅ Where the enterprise plan is active, the system shall enable SSO integration.

❌ Optionally support dark mode. (missing specific behavior)
❌ Where needed, do extra stuff. (vague)
```

**Characteristics**:
- Configuration-dependent
- Clear feature flag or option
- Behavior when enabled AND when disabled

## Writing Good Requirements

### Do's

1. **Be Specific**: Include exact values, thresholds, timeouts
2. **Be Measurable**: Define how to verify the requirement
3. **One Action Per Requirement**: Don't combine multiple behaviors
4. **Use Active Voice**: "The system shall" not "It should be"
5. **Reference Standards**: Link to external specs when applicable

### Don'ts

1. **Avoid Ambiguous Words**:
   - ❌ fast, quick, responsive → ✅ within 200ms
   - ❌ user-friendly, intuitive → ✅ require no more than 3 clicks
   - ❌ secure → ✅ encrypt with AES-256
   - ❌ reliable → ✅ 99.9% uptime

2. **Avoid Compound Requirements**:
   - ❌ "The system shall validate input AND store in database"
   - ✅ Split into FR-001 (validate) and FR-002 (store)

3. **Avoid Implementation Details**:
   - ❌ "Using React, display the form"
   - ✅ "The system shall display a form with fields: name, email, password"

## Requirement Numbering

### Functional Requirements

```
FR-001: Core feature 1
FR-002: Core feature 2
...
FR-010: Secondary feature 1
FR-011: Secondary feature 2
...
FR-100: Edge case handling
```

### Non-Functional Requirements

```
NFR-001: Performance requirement 1
NFR-010: Security requirement 1
NFR-020: Reliability requirement 1
NFR-030: Scalability requirement 1
```

## Traceability

Every requirement should be traceable to:

1. **Source**: Why does this requirement exist?
2. **Acceptance Criteria**: How do we verify it?
3. **Test Case**: What test validates it?
4. **Implementation**: Which code implements it?

### Example Traceability Matrix

| Req ID | Description | AC | Test | Code |
|--------|-------------|-----|------|------|
| FR-001 | Login validation | AC-001 | TC-001 | `auth/login.ts` |
| FR-002 | Session management | AC-002 | TC-002 | `auth/session.ts` |
| NFR-001 | Response time | AC-010 | TC-010 | N/A (infra) |

## Acceptance Criteria Format

Use Given-When-Then format:

```
AC-001: Login Validation
Given a user with valid credentials
When they submit the login form
Then the system returns a valid session token within 200ms
```

## Common Mistakes and Fixes

| Mistake | Example | Fix |
|---------|---------|-----|
| Vague | "Handle errors gracefully" | "When API returns 500, display error message and retry button" |
| Compound | "Validate and save data" | Split into two requirements |
| Implementation | "Use PostgreSQL" | "Store data persistently with ACID guarantees" |
| Untestable | "Be user-friendly" | "Complete checkout in ≤3 steps" |
| Missing subject | "Should validate input" | "The system shall validate input" |

## Templates Quick Reference

```
UBIQUITOUS:    The <system> shall <action>.
EVENT-DRIVEN:  When <trigger>, the <system> shall <action>.
STATE-DRIVEN:  While <state>, the <system> shall <action>.
UNWANTED:      If <condition>, then the <system> shall NOT <action>.
OPTIONAL:      Where <feature>, the <system> shall <action>.
```
