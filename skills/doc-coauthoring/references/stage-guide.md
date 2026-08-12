# Doc Co-Authoring - Stage-by-Stage Guide

## Overview of the Three Stages

The doc co-authoring workflow breaks document creation into three phases:

1. **Stage 1: Context Gathering** — Build shared understanding
2. **Stage 2: Refinement & Structure** — Build document section-by-section
3. **Stage 3: Reader Testing** — Validate the doc works for readers

Each stage has a clear goal and exit condition. Move through them sequentially—don't skip stages, as each builds on the previous one.

---

## Stage 1: Context Gathering

### Goal
Close the gap between what you know and what Claude knows, so Claude can guide you effectively in later stages.

### Duration
15-30 minutes (flexible—more complex docs need more time)

### The Process

**Step 1: Answer Meta-Questions**
1. What type of document? (technical spec, decision doc, proposal, PRD, RFC, etc.)
2. Who's the primary audience? (internal team, external partners, regulators, etc.)
3. What's the desired impact? (inform a decision, document architecture, convince investors, etc.)
4. Is there a template or format requirement?
5. Any other constraints? (word count, deadline, style guide, etc.)

**Answer in shorthand.** You don't need to write essays—bullet points, single sentences, or "see attached" all work.

**Step 2: Info Dump**
Share everything you can about the topic:
- Background and context
- Related discussions or decisions made elsewhere
- Why you're choosing this approach (and why you rejected alternatives)
- Organizational context (who cares about this? what's at stake?)
- Timeline or deadline pressures
- Technical architecture or dependencies
- Known stakeholder concerns or objections

**Don't organize it.** Stream-of-consciousness is fine—Claude will organize as you go.

**Step 3: Clarifying Questions**
Claude will ask 5-10 questions to fill gaps. You can:
- Answer directly
- Link to a channel or document ("see #design-thread")
- Point to another conversation ("I talked about this in Slack on Tuesday")
- Just keep info-dumping if you have more context

**Step 4: Exit Condition**
You're done when:
- Claude understands the core decision/proposal
- Edge cases and trade-offs have been explored
- Claude asks clarifying questions about specific details, not basic facts

### Common Mistakes

| Mistake | Why it's a problem | Fix |
|---------|---|---|
| Leaving out context ("just write something") | Claude guesses wrong about audience, purpose, or constraints | Spend time in Context Gathering—it's not wasted |
| Sharing too much unrelated info | Noise confuses the later workflow | Stick to info directly related to the document |
| Skipping this stage ("I know what I want") | You might, but Claude doesn't—later stages get confused | Even 10 minutes of context gathering helps |
| Not being honest about constraints | Later stages optimize for the wrong thing | If it's a 2-page summary, say so up front |

### Tips

- **Be specific about audience.** "Internal team" is vague; "engineering leads who need to plan hiring" is actionable.
- **Name the problem.** What are you trying to solve or decide?
- **Mention constraints early.** Deadlines, word limits, required sections all matter.
- **Share dissenting opinions.** If someone on your team disagrees, say so—it helps Claude anticipate objections.

---

## Stage 2: Refinement & Structure

### Goal
Build the document section-by-section through brainstorming, curation, and iterative refinement.

### Duration
30 minutes – 2 hours (depends on document length and complexity)

### The Process

**Step 1: Agree on Structure**
Claude suggests 3-5 sections appropriate for your document type. Review and adjust:
- Which sections do you need?
- Should any be combined or split?
- Is there a standard order?

**Example structures:**

**Technical Spec:**
1. Overview & Goals
2. Architecture/Design
3. Data Model
4. API/Interface
5. Failure Modes & Mitigations
6. Timeline & Dependencies

**Decision Document:**
1. Context
2. Options Considered
3. Decision & Rationale
4. Expected Outcomes
5. Next Steps

**Proposal:**
1. Executive Summary
2. Problem Statement
3. Proposed Solution
4. Benefits & Trade-offs
5. Implementation Plan
6. Budget & Timeline

**Step 2: Build Each Section**
For each section, Claude will:

1. **Ask clarifying questions** — What should this section include?
2. **Brainstorm options** — 5-20 possible points to include
3. **Get your input** — Which to keep, remove, or combine?
4. **Check for gaps** — Is anything important missing?
5. **Draft** — Write the actual section text
6. **Iterate** — You give feedback; Claude refines

**Step 3: Iterative Refinement**
After each section is drafted, you review and indicate what to change:

✅ Good feedback: "Remove the X bullet - already covered by Y" or "Make the third paragraph more concise"
❌ Vague feedback: "Looks good" or "Fix it" (Claude can't learn from this)

**Feedback format:** Be specific about what to change and why. This helps Claude learn your style for the next sections.

**Step 4: Quality Check**
After 3 iterations with no major changes, Claude will ask: "Is there anything here that could be removed without losing important information?"

This helps tighten the doc and remove filler.

### Common Patterns

**Pattern: "I don't know what should go here"**
- Claude will ask clarifying questions
- Answer with what you do know; Claude will guide you
- Sometimes this reveals you need to research or talk to someone

**Pattern: "The section is boring/generic/weak"**
- Add specific examples or data points
- Include the decision or reasoning that makes it unique
- Remove abstract statements; make it concrete

**Pattern: "It's too long"**
- Remove supporting details (move to appendix)
- Combine similar points
- Cut anything that could be understood from context

### Tips

- **Start with the hardest section.** If you do the core proposal/decision first, other sections get easier.
- **Write for your audience.** A spec for engineers includes different details than a spec for executives.
- **Use examples.** Abstract descriptions are forgettable; examples stick.
- **Anticipate objections.** If someone might ask "but what about X?", address it proactively.

### Section Ordering

**Recommended order to draft:**
1. Start with the section that has the most unknowns (usually the core proposal/decision)
2. Then do supporting sections (architecture, implementation plan)
3. Leave summaries/conclusions for last (you'll know better what to summarize once the rest is done)

---

## Stage 3: Reader Testing

### Goal
Validate that the document actually works for readers—catches blind spots before it's shared.

### What Gets Tested

Claude will test these questions:
1. **Does a reader understand the main point?** (without context you have)
2. **Are technical terms defined or assumed?**
3. **Are there internal contradictions?**
4. **Would a reader need to ask clarifying questions?**
5. **Does it achieve the intended impact?**

### How It Works

**If you have Agent access** (Claude Code environments):
Claude runs the tests automatically by asking a "fresh" Claude to read the doc and answer questions.

**If testing manually** (claude.ai web, most cases):
1. Open a fresh Claude conversation (no context from this one)
2. Paste or link the document
3. Ask it the questions Claude generates
4. Report back what Reader Claude said

### Common Issues Found in Testing

| Issue | What it means | How to fix |
|---|---|---|
| Reader can't identify the main point | Doc buries the lead or mixes too many ideas | Move your core message earlier; one main idea per section |
| Reader asks "what about X?" | You assumed knowledge or skipped a step | Add the missing context or step explicitly |
| Reader interprets it differently than intended | Language is ambiguous | Rephrase for clarity; add an example |
| Reader agrees but doesn't feel convinced | Logic is sound but lacks evidence | Add data, concrete examples, or expert opinions |
| Reader doesn't know who should do what | Responsibilities unclear | Clarify owners and next steps explicitly |

### Exit Condition

You're done when:
- Reader Claude answers your key questions correctly
- No new ambiguities or contradictions surface
- The doc achieves its intended purpose (informs, convinces, documents, etc.)

### Tips

- **Test with real reader profiles if possible.** If the audience is "engineering leads," have Claude test as one.
- **Don't over-test.** Once Reader Claude gets the main points and doesn't find new gaps, you're ready.
- **Trust your instinct.** If Reader Claude's feedback doesn't resonate, you can ignore it—you're the author.
- **Leave time for testing.** Don't skip this because you're rushed; this is when actual problems surface.

---

## Choosing Between Structured Workflow vs. Freeform

### Use the structured workflow (all 3 stages) when:
- The document is important or high-stakes
- You're writing for unfamiliar audiences
- You don't yet know exactly what the doc should say
- You want Claude to catch blind spots
- It's a complex topic with many sections

### Use freeform (just write with Claude, no workflow) when:
- You know exactly what you want to say
- It's a quick document (1-2 pages)
- You're just asking Claude to help you refine something you've already drafted
- You prefer to iterate without structure

**You can switch mid-stream.** Start freeform and realize you need structure? Ask Claude to help you organize into stages. Committed to a stage and want to break out? Tell Claude—it's your document.

---

## Troubleshooting

| Problem | Solution |
|---|---|
| Stuck in Context Gathering | Set a time limit (20 min max) and move to Refinement |
| Can't agree on a structure | Try the suggested structure first; you can always restructure later |
| Sections feel repetitive | Combine them or move details to appendix |
| Feedback isn't specific enough | Claude asks what to change—be concrete ("unclear" → "the middle paragraph doesn't explain why") |
| Worried about Reader Testing revealing problems | That's the point—better to find them now than when it's published |
| Testing takes too long | Focus on 1-2 key questions, not every possible edge case |

---

## Time Estimate by Document Type

- **1-2 page summary:** 30-45 minutes total
- **Technical spec (5-10 pages):** 1-2 hours
- **Decision document:** 45 minutes – 1 hour
- **Proposal (10+ pages):** 2-3 hours
- **RFC/Design doc (long, complex):** 3+ hours

Add time if:
- You need to gather info/do research
- Stakeholders disagree on approach
- The topic is very new to you

---

## Quick Reference Checklist

### Before Starting
- [ ] What type of doc? (spec, proposal, decision, etc.)
- [ ] Who reads it? (be specific about audience)
- [ ] What decision/action should it drive?
- [ ] Any templates or required sections?

### During Stage 1: Context Gathering
- [ ] Answered 5 meta-questions
- [ ] Shared relevant context and background
- [ ] Addressed Claude's clarifying questions
- [ ] Both you and Claude understand the core idea

### During Stage 2: Refinement & Structure
- [ ] Agreed on section structure
- [ ] Each section drafted and refined
- [ ] Feedback was specific ("remove X because Y")
- [ ] No major sections are missing

### Before Stage 3: Reader Testing
- [ ] Entire doc drafted and refined
- [ ] Read through once yourself—anything obviously wrong?
- [ ] Ready to test with "fresh reader" perspective

### After Reader Testing
- [ ] Reader Claude answered key questions correctly
- [ ] No major contradictions or gaps found
- [ ] You trust the doc achieves its purpose
- [ ] Do a final read-through yourself

---

## Related Skills & Resources

- **Chief-of-staff:** Use for business decisions and planning
- **Business-opportunity-finder:** Use for market research sections
- **Doc-coauthoring:** This skill (structured workflow)
- **TESTING_EXAMPLES.md:** In repository root, has doc examples
