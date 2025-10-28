---
name: Agile Artifact Creation
description: Create Epics, Features, and User Stories following Agile format with testable acceptance criteria
version: 1.0
---

# Agile Artifact Creation

## Overview
Create Epics, Features, and User Stories following Agile format with testable acceptance criteria.

## Standard Format
ALL artifacts use this structure:

```
As a [persona],
I want [capability],
So that [benefit].
```

## Templates

### Epic
```
Epic: [Title]

As a [persona],
I want [outcome],
So that [value].

Success Metrics:
- [Metric 1]
- [Metric 2]

Acceptance Criteria:
- [ ] [Criterion 1]
- [ ] [Criterion 2]
- [ ] [Criterion 3]
```

### Feature
```
Feature: [Title]

As a [persona],
I want [capability],
So that [benefit].

Dependencies:
- [Dependency]

Acceptance Criteria:
- [ ] [Criterion 1]
- [ ] [Criterion 2]
- [ ] [Criterion 3]
- [ ] [Criterion 4]
- [ ] [Criterion 5]
```

### User Story
```
User Story: [Title]

As a [persona],
I want [action],
So that [outcome].

Acceptance Criteria:
Given [context],
When [action],
Then [result].

Additional Criteria:
- [ ] [Criterion 1]
- [ ] [Criterion 2]
- [ ] [Criterion 3]

Story Points: [#]
Priority: [High/Medium/Low]
```

## Common Personas
- Constituent (benefit recipient)
- Caseworker (government employee)
- System Administrator
- Solution Architect
- Developer
- Data Analyst
- Compliance Officer

## Acceptance Criteria Rules

Requirements:
- Testable and verifiable
- Specific with numbers/percentages
- No vague terms (fast, good, easy)
- Measurable outcomes

Format for User Stories:
```
Given [initial state],
When [action],
Then [result].
```

Format for Features/Epics:
```
- [ ] [Specific criterion with metrics]
```

## Examples

### Epic Example
```
Epic: Self-Service Portal

As a constituent,
I want a self-service portal,
So that I can apply without visiting an office.

Success Metrics:
- 70% applications via self-service
- 85% satisfaction rating

Acceptance Criteria:
- [ ] Users can authenticate securely
- [ ] Users can submit applications
- [ ] 99.9% uptime
- [ ] WCAG 2.1 AA compliant
```

### Feature Example
```
Feature: Document Upload

As a constituent,
I want to upload documents,
So that I can verify eligibility online.

Dependencies:
- Cloud Storage configured
- AI API enabled

Acceptance Criteria:
- [ ] Upload PDF/JPG/PNG up to 10MB
- [ ] Encrypted storage
- [ ] AI extracts data 90%+ accuracy
- [ ] Confirmation within 3 seconds
- [ ] Mobile responsive
```

### User Story Example
```
User Story: Upload Pay Stub

As a SNAP applicant,
I want to upload pay stubs,
So that I can prove income eligibility.

Acceptance Criteria:
Given I'm on the upload page,
When I upload a valid PDF,
Then I see confirmation within 3 seconds.

Additional Criteria:
- [ ] 10MB size limit with error
- [ ] Progress bar shows percentage
- [ ] Extracted data displays in 30 seconds
- [ ] Can flag for manual review

Story Points: 5
Priority: High
```

## Quality Checklist
- [ ] Uses "As a/I want/So that" format
- [ ] Persona is specific
- [ ] Criteria are testable
- [ ] Includes numbers/metrics
- [ ] No vague language

## Strong Criteria Examples
✅ Page loads under 2 seconds for 95% of requests
✅ UI passes WCAG 2.1 AA standards
✅ Data encrypted with AES-256
✅ API uses OAuth 2.0

❌ System should be fast
❌ UI should look good
❌ Data should be secure
