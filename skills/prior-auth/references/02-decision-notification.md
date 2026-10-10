# Subskill 2: Decision & Notification

## Purpose

Generate final authorization decision with complete documentation including authorization numbers (if approved), denial rationale (if denied), or specific documentation requests (if pended), plus provider notification letter.

## Prerequisites

**Required Files:**
- `waypoints/assessment.json` - Consolidated assessment from Subskill 1

**Required Tools:**
- None (document generation only)

## What This Subskill Does

1. Loads assessment and recommendation from Subskill 1
2. Generates authorization decision based on recommendation
3. Creates decision-specific content (auth number, denial reasons, or pend requests)
4. Generates provider notification letter
5. Documents complete audit trail
6. Creates final decision package

---

## Execution Flow

### Step 1: Load Assessment

Read assessment file:

```python
import json
from datetime import datetime, timedelta

with open('waypoints/assessment.json', 'r') as f:
    assessment = json.load(f)
```

**Verify Prerequisites:**
- [ ] Assessment file exists
- [ ] Has recommendation field
- [ ] Clinical data available

**If missing:**

Display error: "Assessment not found - Please complete Subskill 1 first."
Exit subskill.

Display Subskill 2 start with request details: Request ID, member name, service description, and Subskill 1 recommendation.

---

### Step 2: Confirm or Override Recommendation

Display assessment summary with:
- Recommendation (APPROVE/DENY/PEND)
- Confidence percentage
- Policy ID and title
- Criteria met count
- Documentation gaps count
- Rationale

Ask: "Accept this recommendation as the final decision? (Yes/No/Override)"

- **Yes:** Proceed with recommendation
- **No:** Exit, return to menu
- **Override:** Change recommendation

**If Override:**

Ask user to select new decision (APPROVE/DENY/PEND) and provide override reason.

Document override:
```python
override_info = {
    "override_applied": True,
    "original_recommendation": "[original]",
    "final_decision": "[new]",
    "override_reason": "[reason]",
    "override_date": datetime.now().isoformat()
}
```

---

### Step 3: Generate Decision-Specific Content

**Read template reference:** See [notification-letter-templates.md](notification-letter-templates.md) for available placeholders and template instructions.

**Check for Template Files:**

Before generating letters, check if custom templates exist in the `prior-auth-review-skill/assets/` folder.

- If a template file is found for the decision type, read and use it as the base template
- If no template found, generate a nicely formatted pdf using the placeholders defined in the template reference

Based on final decision, generate appropriate content in visually appealing pdf format, following the template if available.

**REQUIRED: Disclaimer Header**

All notification letters MUST include the following disclaimer at the top of the document (before any other content):

```
⚠️ AI-ASSISTED DRAFT - REVIEW REQUIRED
Coverage policies reflect Medicare LCDs/NCDs only. If this review is for a
commercial or Medicare Advantage plan, payer-specific policies were not applied.
All decisions require human clinical review before finalization.
```

This disclaimer must appear prominently at the header/top of every notification letter generated.

---

### Step 4: Create Decision Waypoint

**File:** `waypoints/decision.json`

```json
{
  "request_id": "...",
  "decision_date": "ISO datetime",

  "decision": {
    "outcome": "APPROVED/DENIED/PENDING",
    "auth_number": "PA-YYYYMMDD-XXXXX" or null,
    "valid_from": "YYYY-MM-DD" or null,
    "valid_through": "YYYY-MM-DD" or null,
    "limitations": [...] or null,
    "override_applied": true/false
  },

  "rationale": {
    "summary": "...",
    "supporting_facts": ["...", "..."],
    "policy_basis": "..."
  },

  "audit": {
    "reviewed_by": "AI-Assisted Review",
    "review_date": "...",
    "turnaround_hours": float,
    "confidence": "HIGH/MEDIUM/LOW",
    "auto_approved": true/false
  },

  "notification": {
    "letter_file": "outputs/notification_letter.txt",
    "sent_date": "..."
  }
}
```

**Write file.**

---

### Step 5: Display Final Summary

Display concise completion summary with:

**Subskill completion status**

**Request Details:**
- Request ID, member name/DOB, service description

**Decision outcome** (varies by outcome):

*If APPROVED:*
- Authorization approved status
- Authorization number, valid dates
- Approved services, any limitations
- Brief rationale

*If DENIED:*
- Authorization denied status
- Specific denial reasons with policy references
- Appeal rights information

*If PENDING:*
- Pending status
- Response deadline
- Required documentation list

**Files Generated:**
- waypoints/decision.json
- outputs/notification_letter.txt or .pdf

**Review Metrics:**
- Turnaround time, review type, confidence level

Ask user: "Would you like to: 1) View decision letter, 2) Start new PA review, 3) Exit"

Handle user choice appropriately.

---

## Output Files

**Created:**
- `waypoints/decision.json` - Final decision record
- `outputs/notification_letter.txt` or `.pdf` - Provider notification

---

## Error Handling

### Missing Assessment

Display error: "Assessment file not found - Subskill 1 must be completed first. Return to main menu."

### File Write Error

Display error: "Cannot write decision files - Error: [message]"

Suggest checking:
- Output directories exist
- Write permissions
- Disk space

Ask if user wants to retry.

---

## Quality Checks

Before completing Subskill 2:

- [ ] Final decision determined
- [ ] Auth number generated (if approved)
- [ ] Denial reasons documented (if denied)
- [ ] Documentation requests specific (if pended)
- [ ] Provider letter generated
- [ ] Decision file created
- [ ] All files written successfully

---

## Notes for Claude

### Implementation Hints

1. **Professional letter quality:** These go to providers and members
2. **Unique auth numbers:** Use proper format for claims processing
3. **Legally required appeal rights:** Always include in denials
4. **Specific denial reasons:** Cite exact criteria not met with policy references
5. **Actionable pend requests:** Specify exact documents, dates, details needed
6. **Complete audit trail:** Document everything for defensibility

### Common Mistakes to Avoid

- ❌ Don't use fake/improper authorization number formats
- ❌ Don't approve without auth number and validity dates
- ❌ Don't write vague denial reasons ("not medically necessary")
- ❌ Don't forget appeal rights in denials
- ❌ Don't skip documenting decision rationale
- ✅ DO be specific, clear, and complete
- ✅ DO include policy references
- ✅ DO document confidence and quality metrics
