# Prior Authorization Decision Rubric

This file defines the decision rules for generating recommendations (APPROVE/PENDING/DENY).

**Before making any decision, always read this file first to understand the current policy.**

---

## Default Policy: Lenient Mode

**Goal:** Request additional information instead of denying. Only approve when clearly supported.

### Decision Rules

| What to Check | If Problem Found | Action | Why |
|--------------|------------------|--------|-----|
| Provider NPI not verified | Yes | **PENDING** | Request provider credentialing documentation |
| CPT/HCPCS codes invalid | Yes | **PENDING** | Request code clarification or corrected submission |
| ICD-10 codes invalid | Yes | **PENDING** | Request diagnosis code clarification |
| Coverage policy not found | Yes | **PENDING** or continue | May need manual policy research |
| Required criteria **NOT_MET** | Yes | **PENDING** | Request additional clinical documentation |
| Required criteria **INSUFFICIENT** | Yes | **PENDING** | Request specific missing documentation |
| All required criteria **MET** | Yes | **APPROVE** | Clinical evidence supports medical necessity |
| Unclear/uncertain | Yes | **PENDING** | Default safe choice when can't determine |

---

## How to Apply These Rules

**Follow this order:**

1. **Check provider verification**
   - If provider not verified → **PENDING** (request credentialing docs)

2. **Check code validation**
   - If any CPT/HCPCS codes invalid → **PENDING** (request corrected codes)
   - If any ICD-10 codes invalid → **PENDING** (request corrected codes)

3. **Evaluate medical necessity criteria**
   - If all required criteria MET → **APPROVE**
   - If any required criteria NOT_MET or INSUFFICIENT → **PENDING** (request more clinical documentation)
   - If unclear → **PENDING** (safe default)

**That's it!** Simple lenient approach.

---

## Customizing This Rubric

### To Enable DENY (Strict Mode)

If your organization wants to automatically deny certain requests instead of pending:

**Change the Action column in the table above:**
- Provider NPI not verified → Change **PENDING** to **DENY**
- Invalid codes → Change **PENDING** to **DENY**
- Required criteria NOT_MET → Change **PENDING** to **DENY**

**Then update Step 3 in "How to Apply These Rules":**
```
If provider not verified → DENY
If any codes invalid → DENY
If required criteria NOT_MET → DENY (only use PENDING for INSUFFICIENT)
```

---

## Override Rules

Users can override recommendations in Subskill 2:
- PENDING → APPROVE: Allowed (if sufficient docs received)
- PENDING → DENY: Allowed (with clinical justification)
- APPROVE → DENY: Allowed (requires justification)
- APPROVE → PENDING: Allowed (requires justification)

