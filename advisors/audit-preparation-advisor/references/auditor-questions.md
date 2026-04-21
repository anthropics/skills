# Questions to Ask Security Auditors

## Initial Scoping Call

### About Their Experience
1. "Have you audited protocols similar to ours? Can you share examples?"
2. "Who specifically will be working on our audit? Can we see their backgrounds?"
3. "What's your methodology? Manual review, tools, formal verification?"
4. "What tools do you use as part of your process?"
5. "Can you share a sample audit report?"

### About the Engagement
6. "What's your current availability? When could you start?"
7. "How long do you estimate for our codebase size?"
8. "What do you need from us to provide an accurate quote?"
9. "Do you offer re-review of fixes? Is that included?"
10. "What's your communication process during the audit?"

### About Pricing
11. "What's the total cost? Any potential additional charges?"
12. "What's included vs. extra? (Re-review, formal verification, etc.)"
13. "Payment terms? Milestone-based or upfront?"
14. "Do you offer any guarantees or remediation if issues are found post-launch?"

## Before Signing

### Clarify Scope
- "Please confirm which contracts/files are in scope"
- "Are external dependencies in scope or out of scope?"
- "What about deployment scripts and configurations?"
- "Integration risks with external protocols - in scope?"

### Clarify Deliverables
- "What will the final report include?"
- "Will you provide severity ratings and CVSS scores?"
- "Do you provide remediation recommendations?"
- "Can we publish the report publicly?"
- "What's the turnaround for the final report after fixes?"

### Clarify Process
- "How will you communicate findings - ongoing or at the end?"
- "Can we have a mid-point check-in?"
- "What if you discover a critical issue early?"
- "What's your availability for questions during the audit?"

## Red Flag Responses

**Be cautious if they say:**
- "We guarantee your code will be bug-free after audit"
- "We don't need to see the code for a quote"
- "We can start tomorrow" (suggests low demand)
- "All our auditors are equally skilled"
- "We can't share sample reports"
- "The price is the price, no scoping needed"

**Good signs:**
- They ask detailed questions about your protocol
- They're honest about limitations of audits
- They have clear methodology they can explain
- They've found real bugs in similar protocols
- They're willing to share references
- They're upfront about timeline constraints

## After Receiving Report

### Clarifying Findings
- "Can you walk us through finding X in more detail?"
- "Is this exploitable in practice or theoretical?"
- "What's the worst-case impact of this issue?"
- "Do you have suggested remediation approaches?"
- "If we can't fix X, what mitigations would help?"

### About Remediation Review
- "Which findings do you want to re-review?"
- "What's the turnaround time for fix verification?"
- "If we introduce new code in fixes, will you review that?"
- "Can we get written confirmation that fixes are adequate?"

## Comparing Multiple Auditors

Create a comparison matrix:

| Criteria | Auditor A | Auditor B | Auditor C |
|----------|-----------|-----------|-----------|
| Relevant experience | | | |
| Team quality | | | |
| Methodology | | | |
| Price | | | |
| Timeline | | | |
| Communication | | | |
| References | | | |
| Sample reports | | | |
| Gut feeling | | | |

Weight criteria by importance to your project. Don't choose solely on price - a cheap audit that misses critical bugs is worthless.
