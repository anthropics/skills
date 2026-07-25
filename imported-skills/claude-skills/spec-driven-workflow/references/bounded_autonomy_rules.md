# Bounded Autonomy Rules

Decision framework for when an agent (human or AI) should stop and ask vs. continue working autonomously during spec-driven development.

---

## The Core Principle

**Autonomy is earned by clarity.** The clearer the spec, the more autonomy the implementer has. The more ambiguous the spec, the more the implementer must stop and ask.

This is not about trust. It is about risk. A clear spec means low risk of building the wrong thing. An ambiguous spec means high risk.

---

## Decision Matrix

| Signal | Action | Rationale |
|--------|--------|-----------|
| Spec is Approved, requirement is clear, tests exist | **Continue** | Low risk. Build it. |
| Requirement is clear but no test exists yet | **Continue** (write the test first) | You can infer the test from the requirement. |
| Requirement uses SHOULD/MAY keywords | **Continue** with your best judgment | These are intentionally flexible. Document your choice. |
| Requirement is ambiguous (multiple valid interpretations) | **STOP** if ambiguity > 30% of the task | Ask the spec author to clarify. |
| Implementation requires changing an API contract | **STOP** always | Breaking changes need explicit approval. |
| Implementation requires a new database migration | **STOP** if it changes existing columns/tables | New tables are lower risk than schema changes. |
| Security-related change (auth, crypto, PII) | **STOP** always | Security changes need review regardless of spec clarity. |
| Performance-critical path with no benchmark data | **STOP** | You cannot prove NFR compliance without measurement. |
| Bug found in existing code unrelated to spec | **STOP** — file a separate issue | Do not fix unrelated bugs in a spec-scoped implementation. |
| Spec says "N/A" for a section you think needs content | **STOP** | The author may have a reason, or they may have missed it. |

---

## Ambiguity Scoring

When you encounter ambiguity, quantify it before deciding to stop or continue.

### How to Score Ambiguity

For each requirement you are implementing, ask:

1. **Can I write a test for this right now?** (No = +20% ambiguity)
2. **Are there multiple valid interpretations?** (Yes = +20% ambiguity)
3. **Does the spec contradict itself?** (Yes = +30% ambiguity)
4. **Am I making assumptions about user behavior?** (Yes = +15% ambiguity)
5. **Does this depend on an undocumented external system?** (Yes = +15% ambiguity)

### Threshold

| Ambiguity Score | Action |
|-----------------|--------|
| 0-15% | Continue. Minor ambiguity is normal. Document your interpretation. |
| 16-30% | Continue with caution. Add a comment explaining your interpretation. Flag in PR. |
| 31-50% | STOP. Ask the spec author one specific question. Do not continue until answered. |
| 51%+ | STOP. The spec is incomplete. Request a revision before proceeding. |

### Example

**Requirement:** "FR-7: The system MUST notify the user when their order ships."

Questions:
1. Can I write a test? Partially — I know WHAT to test but not HOW (email? push? in-app?). +20%
2. Multiple interpretations? Yes — notification channel is unclear. +20%
3. Contradicts itself? No. +0%
4. Assuming user behavior? Yes — I am assuming they want email. +15%
5. Undocumented external system? Maybe — depends on notification service. +15%

**Total: 70%.** STOP. The spec needs to specify the notification channel.

---

## Scope Creep Detection

### What Is Scope Creep?

Scope creep is implementing functionality not described in the spec. It includes:

- Adding features the spec does not mention
- "Improving" behavior beyond what acceptance criteria require
- Handling edge cases the spec explicitly excluded
- Refactoring unrelated code "while you're in there"
- Building infrastructure for future features

### Detection Patterns

| Pattern | Example | Risk |
|---------|---------|------|
| "While I'm here..." | Refactoring a utility function unrelated to the spec | Medium — unreviewed changes |
| "This would be easy to add..." | Adding a search filter the spec does not mention | High — untested, unspecified |
| "Users will probably want..." | Building a feature based on assumption | High — may conflict with future specs |
| "This is obviously needed..." | Adding logging, metrics, or caching not in NFRs | Medium — may be overkill or wrong approach |
| "The spec forgot to mention..." | Building something the spec excluded | Critical — may be deliberately excluded |

### Response Protocol

When you detect scope creep in your own work:

1. **Stop immediately.** Do not commit the extra code.
2. **Check Out of Scope.** Is this item explicitly excluded?
3. **If excluded:** Delete the code. The spec author had a reason.
4. **If not mentioned:** File a note for the spec author. Ask if it should be added.
5. **If approved:** Update the spec FIRST, then implement.

---

## Breaking Change Identification

### What Counts as a Breaking Change?

A breaking change is any modification that could cause existing clients, tests, or integrations to fail.

| Category | Breaking | Not Breaking |
|----------|----------|--------------|
| API endpoint removed | Yes | - |
| API endpoint added | - | No |
| Required field added to request | Yes | - |
| Optional field added to request | - | No |
| Field removed from response | Yes | - |
| Field added to response | - | No (usually) |
| Status code changed | Yes | - |
| Error code string changed | Yes | - |
| Database column removed | Yes | - |
| Database column added (nullable) | - | No |
| Database column added (not null, no default) | Yes | - |
| Enum value removed | Yes | - |
| Enum value added | - | No (usually) |
| Behavior change for existing input | Yes | - |

### Breaking Change Protocol

1. **Identify** the breaking change before implementing it.
2. **Escalate** immediately — do not implement without approval.
3. **Propose** a migration path (versioned API, feature flag, deprecation period).
4. **Document** the breaking change in the spec's changelog.

---

## Security Implication Checklist

Any change touching the following areas MUST be escalated, even if the spec seems clear.

### Always Escalate

- [ ] Authentication logic (login, logout, token generation)
- [ ] Authorization logic (role checks, permission gates)
- [ ] Encryption/hashing (algorithm choice, key management)
- [ ] PII handling (storage, transmission, logging)
- [ ] Input validation bypass (new endpoints, parameter changes)
- [ ] Rate limiting changes (thresholds, scope)
- [ ] CORS or CSP policy changes
- [ ] File upload handling
- [ ] SQL/NoSQL query construction (injection risk)
- [ ] Deserialization of user input
- [ ] Redirect URLs from user input (open redirect risk)
- [ ] Secrets in code, config, or logs

### Security Escalation Template

```markdown
## Security Escalation: [Title]

**Affected area:** [authentication/authorization/encryption/PII/etc.]
**Spec reference:** [FR-N or NFR-SN]
**Risk:** [What could go wrong if implemented incorrectly]
**Current protection:** [What exists today]
**Proposed change:** [What the spec requires]
**My concern:** [Specific security question]
**Recommendation:** [Proposed approach with security rationale]
```

---

## Escalation Templates

### Template 1: Ambiguous Requirement

```markdown
## Escalation: Ambiguous Requirement

**Blocked on:** FR-7 ("notify the user when their order ships")
**Ambiguity score:** 70%
**Question:** What notification channel should be used?
**Options considered:**
  A. Email only — Pros: simple, reliable. Cons: not real-time.
  B. Email + in-app notification — Pros: covers both async and real-time. Cons: more implementation effort.
  C. Configurable per user — Pros: maximum flexibility. Cons: requires preference UI (not in spec).
**My recommendation:** B (email + in-app). Covers most use cases without requiring new UI.
**Impact of waiting:** Cannot implement FR-7 until resolved. No other work blocked.
```

### Template 2: Missing Edge Case

```markdown
## Escalation: Missing Edge Case

**Related to:** FR-3 (password reset link expires after 1 hour)
**Scenario:** User clicks a reset link, but their account was deleted between requesting and clicking.
**Not in spec:** Edge cases section does not cover this.
**Options considered:**
  A. Show generic "link invalid" error — Pros: secure (no info leak). Cons: confusing for deleted user.
  B. Show "account not found" error — Pros: clear. Cons: confirms account deletion to link holder.
**My recommendation:** A. Security over clarity — do not reveal account existence.
**Impact of waiting:** Can implement other ACs; this is blocking only AC-2 completion.
```

### Template 3: Potential Breaking Change

```markdown
## Escalation: Potential Breaking Change

**Spec requires:** Adding required field "role" to POST /api/users request (FR-6)
**Current behavior:** POST /api/users accepts {email, password, displayName}
**Breaking:** Yes — existing clients will get 400 errors (missing required field)
**Options considered:**
  A. Make "role" required as spec says — Pros: matches spec. Cons: breaks mobile app v2.1.
  B. Make "role" optional with default "user" — Pros: backward compatible. Cons: deviates from spec.
  C. Version the API (v2) — Pros: clean separation. Cons: maintenance burden.
**My recommendation:** B. Default to "user" for backward compatibility. Update spec to reflect MAY instead of MUST.
**Impact of waiting:** Frontend team is building against the new contract. Need answer within 2 days.
```

### Template 4: Scope Creep Proposal

```markdown
## Escalation: Potential Addition to Spec

**Context:** While implementing FR-2 (password validation), I noticed the spec does not mention password strength feedback.
**Not in spec:** No requirement for showing strength indicators.
**Checked Out of Scope:** Not listed there either.
**Proposal:** Add FR-7: "The system SHOULD display password strength feedback during registration."
**Effort:** ~2 hours additional implementation.
**Question:** Should this be added to current spec, filed as a separate spec, or skipped?
**Impact of waiting:** FR-2 implementation is not blocked. This is an enhancement question only.
```

---

## Quick Reference Card

```
CONTINUE if:
  - Spec is approved
  - Requirement uses MUST and is unambiguous
  - Tests can be written directly from the AC
  - Changes are additive and non-breaking
  - You are refactoring internals only (no behavior change)

STOP if:
  - Ambiguity > 30%
  - Any breaking change
  - Any security-related change
  - Spec says N/A but you think it shouldn't
  - You are about to build something not in the spec
  - You cannot write a test for the requirement
  - External dependency is undocumented
```

---

## Anti-Patterns in Autonomy

### 1. "I'll Ask Later"
Continuing past an ambiguity checkpoint because asking feels slow. The rework from building the wrong thing is always slower.

### 2. "It's Obviously Needed"
Assuming a missing feature was accidentally omitted. It may have been deliberately excluded. Check Out of Scope first.

### 3. "The Spec Is Wrong"
Implementing what you think the spec SHOULD say instead of what it DOES say. If the spec is wrong, escalate. Do not silently "fix" it.

### 4. "Just This Once"
Bypassing the escalation protocol for a "small" change. Small changes compound. The protocol exists because humans are bad at judging risk in the moment.

### 5. "I Already Built It"
Presenting completed work that was never in the spec and hoping it gets accepted. This creates review pressure and wastes everyone's time if rejected. Ask BEFORE building.
