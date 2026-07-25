# Engineering Output Format Specifications

Four specialized output format specifications for software engineering deliverables. Each includes the complete XML specification for use in Claude prompts, section-level length guidance, and calibration notes.

## Table of Contents

- [RFC (Request for Comments)](#rfc-request-for-comments)
- [ADR (Architecture Decision Record)](#adr-architecture-decision-record)
- [Runbook](#runbook)
- [Code Review Feedback](#code-review-feedback)

---

## RFC (Request for Comments)

**Use when:** Proposing a significant technical change for team deliberation. Distinct from a Technical Design Document (which specifies a decided-upon design) in that an RFC is a proposal — it presents alternatives, makes a recommendation, and invites discussion. The audience has the power to reject or modify the proposal. Use when the decision has not been made yet and needs input from multiple stakeholders.

```xml
<output_format>
Structure as an RFC:

Title: A clear, descriptive title for the proposal — not a question, but a concise statement of what is being proposed.

Status: [Draft | In Review | Accepted | Rejected | Superseded]

Summary: (1 paragraph) What is being proposed and why. A reader who reads only this paragraph should understand the core proposal and its motivation.

Motivation: (2-3 paragraphs) The problem this proposal solves. What is the current pain, what are its consequences, and why does it need to be addressed now? Include concrete evidence — incident counts, developer hours wasted, customer impact — not just abstract arguments.

Proposed Design: (3-5 paragraphs) The recommended solution in sufficient detail for reviewers to evaluate it. Cover the key design decisions, the data model or interface changes, and how the system behaves during the transition. Use diagrams or pseudocode where they add clarity.

Alternatives Considered: (1-2 paragraphs each, for 2-3 alternatives) Other approaches that were evaluated and why they were not recommended. Each alternative should be described fairly enough that a reader could advocate for it — if an alternative is dismissed without genuine consideration, reviewers will question the analysis.

Migration and Rollout: (1-2 paragraphs) How the change is deployed, how existing behavior is preserved during transition, and what the rollback plan is if problems emerge.

Drawbacks and Open Questions: (1-2 paragraphs) Honest assessment of the proposal's costs, risks, or unresolved design questions. Reviewers trust RFCs that acknowledge their own weaknesses.

Total length: 1200-2000 words. The RFC must be substantive enough to enable a decision but concise enough that reviewers will actually read it. Optimize for clarity over completeness — link to supporting documents for deep technical detail rather than including everything inline.
</output_format>
```

**Calibration notes:**

Claude may produce RFCs where the Alternatives Considered section is a straw-man exercise — alternatives described only to be dismissed with obvious flaws. If the alternatives do not feel genuinely competitive with the recommended approach, add: "Each alternative must be presented as a legitimate option that a reasonable engineer could prefer. If no alternatives are genuinely competitive, state that explicitly and explain why — do not fabricate weak alternatives to make the recommendation look stronger."

Watch for the Motivation section being too abstract. If it reads as "the current approach has limitations" rather than citing specific incidents, metrics, or developer pain, add: "Quantify the motivation. How many incidents, how much developer time, what customer impact? If you do not have exact numbers, estimate and label the estimate."

---

## ADR (Architecture Decision Record)

**Use when:** Recording a specific architectural decision — what was decided, why, and what consequences follow. Distinct from an RFC (which proposes and invites discussion) in that an ADR documents a decision that has been made. Covers a single decision point, typically in a few hundred words. Use when you need a compact, referenceable record of why a particular technical choice was made.

```xml
<output_format>
Structure as an architecture decision record:

Title: ADR-[number]: [Decision statement as an active sentence, e.g., "Use PostgreSQL for the primary data store"]

Status: [Proposed | Accepted | Deprecated | Superseded by ADR-N]

Context: (1-2 paragraphs) The situation that motivated this decision. What forces are at play — technical constraints, team capabilities, business requirements, deadlines? What problem needs to be solved, and what makes it a decision worth recording?

Decision: (1 paragraph) The decision itself, stated directly. What will we do? Be precise — "use PostgreSQL" is clearer than "use a relational database."

Consequences: (2-3 paragraphs) What follows from this decision — both positive and negative. What becomes easier? What becomes harder or impossible? What new constraints does this create for future decisions? What risks are we accepting? Be honest about the costs — an ADR that lists only benefits is not useful as a decision record.

Total length: 300-600 words. ADRs are intentionally concise. If the decision requires more than 600 words to explain, it may need an RFC instead, or the decision may actually be multiple decisions that should be recorded separately.
</output_format>
```

**Calibration notes:**

Claude may over-expand ADRs into mini design documents, losing the format's core value as a concise, scannable decision record. If the output exceeds 600 words, add: "This is an ADR, not a design document. Capture the decision and its reasoning in the minimum words necessary. If you find yourself explaining implementation details, the scope has expanded beyond a single decision."

Watch for the Consequences section being one-sided — listing only benefits without costs. Every architectural decision involves tradeoffs; an ADR that does not acknowledge the costs of the chosen path is incomplete.

---

## Runbook

**Use when:** You need an operational playbook for responding to a specific incident type, performing a maintenance procedure, or executing a complex operational task. Designed to be followed under stress — during an incident at 3 AM by an on-call engineer who may not be deeply familiar with the system. Every instruction must be unambiguous, every command must be copy-pasteable, and every decision point must have clear criteria.

```xml
<output_format>
Structure as an operational runbook:

Title: [Specific scenario, e.g., "Responding to Database Replication Lag > 30s"]

Severity / Priority: The urgency level and expected response time for this scenario.

Symptoms: (brief list) How this issue manifests — what alerts fire, what the user-facing impact looks like, what monitoring dashboards show. An on-call engineer reading these symptoms should be able to confirm within 60 seconds whether this runbook applies.

Prerequisites: What access, tools, or permissions the responder needs before starting. List specific systems, credentials, or VPN requirements.

Diagnostic Steps: (numbered, sequential) How to confirm the root cause and assess severity. Each step should include the exact command or query to run, what the output means, and what to do based on the result. Use explicit decision forks: "If X, proceed to step N. If Y, skip to step M."

Remediation Steps: (numbered, sequential) How to fix the issue. Same standards as diagnostic steps — exact commands, expected output, explicit decision points. Include verification checks after each major action: "After running this command, verify that [metric] has returned to [normal range] within [timeframe]."

Rollback: What to do if the remediation makes things worse. Specific steps to undo changes, not just "revert."

Escalation: When and how to escalate. What conditions indicate that this runbook is insufficient, and who to contact. Include specific contact channels, not just team names.

Total length: 500-1500 words depending on procedure complexity. Every command should be copy-pasteable. Every decision point should have clear criteria. No ambiguous instructions — "check the logs" is insufficient; "run `kubectl logs -n production deployment/api-server --tail=100 | grep ERROR`" is actionable.
</output_format>
```

**Calibration notes:**

Claude may produce runbooks that are technically complete but assume too much system familiarity — using shorthand for system names, referencing dashboards without URLs, or assuming the reader knows which cluster to connect to. If the output assumes insider knowledge, add: "Write for an on-call engineer who joined the team two months ago. Include the full path to every dashboard, the exact cluster and namespace for every command, and explain any system-specific terminology on first use."

Watch for runbooks that lack clear escalation criteria. The most dangerous outcome of a runbook is an engineer following it for an hour when they should have escalated after ten minutes. If the escalation section is vague, add: "Define a specific time-box for each phase. If diagnostic steps have not identified the cause within [N] minutes, escalate immediately."

---

## Code Review Feedback

**Use when:** You need structured feedback on a codebase, pull request, design implementation, or technical proposal. Specifically formatted as review feedback — prioritized findings with actionable recommendations, written for the author of the code. Use when the deliverable is the review itself.

```xml
<output_format>
Structure as code review feedback:

Summary: (2-3 sentences) Overall assessment — is this ready to merge, does it need changes, or does it need a fundamentally different approach? State the verdict upfront.

Critical Issues: (numbered) Issues that must be resolved before merge. Each entry includes: what the issue is, where it occurs (file and function or line reference), why it matters (what breaks or what risk it introduces), and the recommended fix. These are correctness, security, or data integrity problems.

Important Improvements: (numbered) Issues that should be resolved but are not blocking. Same format as critical issues. These are maintainability, performance, or clarity problems that will cause pain later if not addressed now.

Suggestions: (numbered, brief) Optional improvements — alternative approaches, readability enhancements, or patterns the author might consider. These are professional-judgment items, not requirements.

What Works Well: (1-2 sentences, optional) If specific aspects of the code are notably well-done — clean abstraction, thorough error handling, good test coverage — acknowledge them briefly. This is not mandatory and should not be forced.

Total length: Scale to the size and complexity of the code under review. A small PR might need 200 words; a major feature branch might need 800. Do not pad the review to fill space — if there are only two findings, present two findings.
</output_format>
```

**Calibration notes:**

Claude may produce code review feedback that is uniformly positive — praising the code without identifying substantive issues. This is Claude's agreeableness tendency applied to code review, and it undermines the format's purpose. If the output lacks critical or important findings on code that clearly has issues, add: "This review must identify at least the most significant improvement opportunity in the code. A review with no actionable findings is not useful — if the code is genuinely excellent, explain specifically what makes it so rather than offering generic praise."

Watch for Claude inventing line numbers or file references when reviewing code it can see but cannot precisely locate within. If specific references are unreliable, add: "Reference findings by function name and description of the code section, not by line number, unless you can verify the line numbers exactly."
