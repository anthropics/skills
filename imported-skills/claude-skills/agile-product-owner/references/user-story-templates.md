# User Story Templates

Standard templates, acceptance criteria patterns, and INVEST validation for user stories.

---

## Table of Contents

- [Story Templates](#story-templates)
- [Acceptance Criteria Patterns](#acceptance-criteria-patterns)
- [INVEST Criteria](#invest-criteria)
- [Story Point Estimation](#story-point-estimation)
- [Common Antipatterns](#common-antipatterns)

---

## Story Templates

### Standard User Story Format

```
As a [persona],
I want to [action/capability],
So that [benefit/value].
```

### Template by Story Type

**Feature Story:**
```
As a [persona],
I want to [perform action]
So that [I achieve benefit].

Example:
As a marketing manager,
I want to export campaign reports to PDF
So that I can share results with stakeholders who don't have system access.
```

**Improvement Story:**
```
As a [persona],
I need [capability/improvement]
To [achieve goal more effectively].

Example:
As a sales rep,
I need faster search results
To find customer records without interrupting calls.
```

**Bug Fix Story:**
```
As a [persona],
I expect [correct behavior]
When [specific condition].

Example:
As a user,
I expect my session to remain active
When navigating between dashboard tabs.
```

**Integration Story:**
```
As a [persona],
I want to [integrate/connect with system]
So that [workflow improvement].

Example:
As an admin,
I want to sync user data with our LDAP server
So that employees are automatically provisioned.
```

**Enabler Story (Technical):**
```
As a developer,
I need to [technical requirement]
To enable [user-facing capability].

Example:
As a developer,
I need to implement caching layer
To enable sub-second dashboard load times.
```

### Persona Library

| Persona | Typical Needs | Context |
|---------|--------------|---------|
| End User | Efficiency, simplicity, reliability | Daily core feature usage |
| Administrator | Control, visibility, security | System management |
| Power User | Automation, customization, shortcuts | Expert workflows |
| New User | Guidance, learning, safety | Onboarding experience |
| Manager | Reporting, oversight, delegation | Team coordination |
| External User | Access, security, documentation | Customer/partner usage |

---

## Acceptance Criteria Patterns

### Given-When-Then (Gherkin)

Preferred format for testable acceptance criteria:

```
Given [precondition/context],
When [action/trigger],
Then [expected outcome].
```

**Examples:**

```
Given the user is logged in with valid credentials,
When they click the "Export" button,
Then a PDF download starts within 2 seconds.

Given the user has entered invalid email format,
When they submit the registration form,
Then an inline error message displays "Please enter a valid email address."

Given the daily sync job has not run in 24 hours,
When the scheduler triggers at midnight,
Then all pending records are synchronized and logged.
```

### Should/Must/Can Patterns

**Should (Expected Behavior):**
```
Should [behavior] when [condition].

Example:
Should display loading spinner when API call exceeds 500ms.
```

**Must (Hard Requirement):**
```
Must [requirement] to [achieve outcome].

Example:
Must encrypt all data at rest to meet compliance requirements.
```

**Can (Capability):**
```
Can [capability] without [negative outcome].

Example:
Can undo last action without losing other changes.
```

### Acceptance Criteria Checklist

Each story should have acceptance criteria covering:

| Category | Example Criterion |
|----------|-------------------|
| Happy Path | Given valid input, When submitted, Then success message displayed |
| Validation | Should reject input when required field is empty |
| Error Handling | Must show user-friendly message when API fails |
| Performance | Should complete operation within 2 seconds |
| Accessibility | Must be navigable via keyboard only |
| Security | Should not expose sensitive data in URL parameters |

### Minimum Acceptance Criteria Count

| Story Size (Points) | Minimum AC Count |
|--------------------|------------------|
| 1-2 | 3-4 |
| 3-5 | 4-6 |
| 8 | 5-8 |
| 13+ | Split the story |

---

## INVEST Criteria

### INVEST Validation Checklist

| Criterion | Question | Pass If... |
|-----------|----------|------------|
| **I**ndependent | Can this story be developed without depending on another story? | No blocking dependencies on uncommitted work |
| **N**egotiable | Is the implementation approach flexible? | Multiple ways to deliver the value |
| **V**aluable | Does this deliver value to users or business? | Clear benefit statement in "so that" |
| **E**stimable | Can the team estimate this story? | Understood well enough to size |
| **S**mall | Can this be completed in one sprint? | ≤8 story points typically |
| **T**estable | Can we verify this story is done? | Clear, measurable acceptance criteria |

### INVEST Failure Patterns

| Criterion | Red Flag | Fix |
|-----------|----------|-----|
| Independent | "After story X is done..." | Combine stories or resequence |
| Negotiable | Specific implementation in story | Focus on outcome, not solution |
| Valuable | No "so that" clause | Add benefit statement |
| Estimable | Team says "no idea" | Spike first, then story |
| Small | >8 points | Split into smaller stories |
| Testable | "System should be better" | Add measurable criteria |

### Story Splitting Techniques

When stories are too large (>8 points), split using:

| Technique | Example |
|-----------|---------|
| By workflow step | "Create order" → "Add items" + "Apply discount" + "Submit order" |
| By persona | "User dashboard" → "Admin dashboard" + "Member dashboard" |
| By data type | "Import data" → "Import CSV" + "Import Excel" |
| By operation | "Manage users" → "Add user" + "Edit user" + "Delete user" |
| By platform | "Mobile support" → "iOS support" + "Android support" |
| Happy path first | "Full feature" → "Basic feature" + "Error handling" + "Edge cases" |

---

## Story Point Estimation

### Fibonacci Scale Reference

| Points | Complexity | Example |
|--------|------------|---------|
| 1 | Trivial | Fix typo, change label |
| 2 | Simple | Add field, simple validation |
| 3 | Small | New form, basic CRUD operation |
| 5 | Medium | Feature with multiple components |
| 8 | Large | Complex feature, multiple integrations |
| 13 | Very Large | Consider splitting |
| 21+ | Epic | Must split |

### Estimation Factors

| Factor | Low Complexity | High Complexity |
|--------|---------------|-----------------|
| Unknowns | Well understood | Many unknowns |
| Dependencies | None | Multiple systems |
| Testing | Simple unit tests | Complex integration tests |
| Data | Simple structure | Complex transformations |
| UI | Minor changes | New components |

### Velocity Calculation

```
Velocity = Total points completed / Number of sprints

Example:
Sprint 1: 28 points
Sprint 2: 32 points
Sprint 3: 30 points
Average Velocity: (28 + 32 + 30) / 3 = 30 points/sprint

Sprint Capacity Planning:
- Committed: 80-90% of velocity (24-27 points)
- Stretch goals: 10-20% additional (3-6 points)
```

---

## Common Antipatterns

### Story Antipatterns

| Antipattern | Example | Fix |
|-------------|---------|-----|
| Solution story | "Implement React component" | "Display user profile information" |
| Compound story | "Create, edit, and delete users" | Split into three stories |
| Missing persona | "The system will..." | "As an admin, I want to..." |
| No benefit | "I want to see a button" | Add "so that [benefit]" |
| Too vague | "Improve performance" | "Reduce page load to <2 seconds" |
| Technical jargon | "Implement Redis caching" | "Enable instant search results" |

### Acceptance Criteria Antipatterns

| Antipattern | Example | Fix |
|-------------|---------|-----|
| Too vague | "Works correctly" | Specific Given-When-Then |
| Implementation details | "Use PostgreSQL query" | Focus on outcome |
| Missing unhappy path | Only success scenario | Add error cases |
| Untestable | "User is happy" | Measurable behavior |
| Too many | 15+ criteria | Split the story |

### Sprint Planning Antipatterns

| Antipattern | Impact | Fix |
|-------------|--------|-----|
| 100% capacity | No buffer for unknowns | Plan 80-85% |
| All large stories | Risk of incomplete sprint | Mix sizes |
| No dependencies mapped | Blocked work | Identify dependencies upfront |
| Stretch = overflow | Hiding overcommitment | Stretch should be optional |
