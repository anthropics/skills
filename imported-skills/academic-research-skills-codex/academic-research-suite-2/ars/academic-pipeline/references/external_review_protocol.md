# External Review Protocol (Added in v2.5)

**Scenario**: The user submitted to a journal and received feedback from real human reviewers, bringing those comments into the pipeline.

**Trigger**: User says "I received reviewer comments," "reviewer comments," "revise and resubmit," etc.

## Differences from Internal Review

| Aspect | Internal Review (Stage 3 simulation) | External Review (real journal) |
|--------|-------------------------------------|-------------------------------|
| Source of review comments | Pipeline's AI reviewers | Journal's human reviewers |
| Comment format | Structured (Revision Roadmap) | Unstructured (free text, PDF, email) |
| Comment quality | Consistent, predictable | Variable quality, may be vague or contradictory |
| Revision strategy | Can accept wholesale | Need to judge which to accept/reject/negotiate |
| Acceptance criteria | AI re-review suffices | Ultimately decided by human reviewers |

## Step 1: Intake and Structuring

```
1. Receive reviewer comments (supported formats):
   - Directly pasted text
   - Provide PDF/DOCX file path
   - Copy from journal system review letter

2. Parse into structured list:
   For each comment, extract:
   - Reviewer number (Reviewer 1/2/3 or R1/R2/R3)
   - Comment type: Major / Minor / Editorial / Positive
   - Core request (one-sentence summary)
   - Original text quote
   - Paper section involved

3. Produce External Review Summary:
   +----------------------------------------+
   | External Review Summary                |
   +----------------------------------------+
   | Journal: [journal name]                |
   | Decision: [R&R / Major / Minor]        |
   | Reviewers: [N]                         |
   | Total comments: [N]                    |
   |   Major: [n]  Minor: [n]  Editorial: [n]|
   +----------------------------------------+

4. Confirm parsing results with user:
   "I organized the reviewer comments into [N] items. Here is the summary — please confirm nothing was missed or misinterpreted."
```

## Step 2: Strategic Revision Coaching (External Revision Coaching)

Unlike the Socratic coaching for internal review, external review coaching focuses more on **strategic judgment**:

```
For each Major comment, guide the user to think through:

1. Understanding layer
   "What is this reviewer's core concern? Is it about methodology, theory, or presentation?"

2. Judgment layer
   "Do you agree with this criticism?"
   - Agree -> "How do you plan to revise?"
   - Partially agree -> "Which parts do you agree with and which not? What is your basis for disagreement?"
   - Disagree -> "What is your rebuttal argument? Can you support it with literature or data?"

3. Strategy layer
   "How will you phrase this in the response letter?"
   - Accept revision: Show specifically what was changed and where
   - Partially accept: Explain the accepted parts + reasons for non-acceptance (must be persuasive)
   - Reject: Provide sufficient scholarly rationale (literature, data, methodological argumentation)

4. Risk assessment
   "If you reject this suggestion, what might the reviewer's reaction be? Is it worth the risk?"
```

**Key principles**:
- **Do not default to "accept all"**: Real reviewer comments are not always correct — some may be based on misunderstanding or school-of-thought bias
- **Encourage user to inject context**: "What school of thought do you think this reviewer might come from? What context might they not be aware of?"
- **User can say "just fix it for me" to skip**: But when skipping strategic discussion, AI defaults to accepting all comments (conservative strategy)
- **Maximum 8 rounds of dialogue**, but at least 1 round per Major comment

## Step 3: Revision and Response to Reviewers

```
Produce two documents:

1. Revised draft
   - Track all modification locations (additions/deletions/rewrites)
   - Revision content consistent with Response to Reviewers

2. Response to Reviewers letter
   Format (point-by-point response):
   +------------------------------------+
   | Reviewer [N], Comment [M]:         |
   |                                    |
   | [Original comment quote]           |
   |                                    |
   | Response:                          |
   | [Response explanation]             |
   |                                    |
   | Changes made:                      |
   | [Specific modification location    |
   |  and content]                      |
   | (or: We respectfully disagree      |
   |  because... [rationale])           |
   +------------------------------------+
```

## Step 4: Self-Verification (Completeness Check)

```
Stage 3' behavior adjustments in external review mode:

1. Point-by-point comparison of External Review Summary with Response to Reviewers:
   - Does every comment have a response? (completeness)
   - Is each response consistent with actual changes? (consistency)
   - Were the places claimed as "modified" actually changed? (truthfulness)

2. New citation verification:
   - New references added during revision enter Stage 4.5 integrity verification

3. Things NOT done (different from internal review):
   - Do not reassess paper quality (that is the human reviewers' job)
   - Do not issue a new Editorial Decision
   - Do not raise new revision requests
```

## Honest Capability Boundaries

1. **AI verification does not equal human reviewer satisfaction**: Stage 3' can confirm revisions are "complete and consistent," but cannot predict whether human reviewers will accept your responses. Reviewers may have unstated expectations, school-of-thought preferences, or methodological insistence
2. **Unstructured comments may not parse perfectly**: Some reviewers write vaguely (e.g., "the methodology needs more work"), and AI will do its best to parse but may miss implied intentions. After parsing, **user confirmation is mandatory**
3. **AI cannot make scholarly judgments for you**: "Should I accept Reviewer 2's suggestion?" is your decision. AI can provide an analytical framework, but final judgment rests with the researcher
4. **Cross-cultural review convention differences**: Response conventions differ across journals/academic circles (some require extreme deference, others accept direct rebuttal). AI defaults to neutral academic tone; the user can request adjustments
