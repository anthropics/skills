---
name: handoff-protocols
description: Manages work transitions between team members or agents by creating structured handoff documents, summarizing project status, documenting key decisions, blockers, and open questions, and generating onboarding briefs. Use when someone needs to hand off, hand over, or transition a project; pass work to another person or agent; brief a colleague taking over; prepare a shift change summary; or onboard someone mid-task. Produces ready-to-use handoff documents covering current status, next steps, known issues, technical context, and communication templates for both planned and unplanned transfers.
version: 1.0.0
triggers:
  - handoff
  - pass to
  - transfer work
  - take over
  - continue from
  - pick up where
tags:
  - collaboration
  - handoff
  - communication
  - context
difficulty: beginner
estimatedTime: 10
relatedSkills:
  - collaboration/structured-review
  - collaboration/parallel-investigation
---

# Handoff Protocols

You are executing a work handoff between team members or agents.

## Handoff Types

| Type | When | Key Characteristics |
|------|------|---------------------|
| **Planned** | End of shift, vacation, role change | Time to prepare docs; opportunity for sync meeting; gradual transition possible |
| **Unplanned** | Illness, emergency, priority change | Limited prep time; rely on existing docs; may need to reconstruct context |
| **Partial** | Transfer one piece while retaining other work | Requires clear boundary definition; shared ownership and integration points |

## Handoff Document

### Essential Sections

```markdown
# Handoff: [Task/Project Name]

## Quick Summary
[One paragraph: What is this and current state]

## Current Status
- [ ] Phase: [Design/Implementation/Testing/etc]
- [ ] Progress: [X% complete / Y of Z tasks done]
- [ ] Blockers: [Current blockers, if any]
- [ ] Next Action: [Very next thing to do]

## Context

### What We're Building
[Brief description of the goal/feature]

### Why
[Business/technical justification]

### Key Decisions Made
| Decision | Options Considered | Choice | Rationale |
|----------|-------------------|--------|-----------|
| [D1] | A, B, C | B | [Why B was chosen] |

### Open Questions
- [Question 1]
- [Question 2]

## Technical Details

### Architecture/Design
[Relevant diagrams or links]

### Key Files
- `path/to/file1.ts` - [Purpose]
- `path/to/file2.ts` - [Purpose]

### Dependencies
- [Dependency 1]: [How it's used]
- [Dependency 2]: [How it's used]

## Current State of Code

### What's Complete
- [x] [Completed item 1]
- [x] [Completed item 2]

### In Progress
- [ ] [In progress item] - [Current state]

### Not Started
- [ ] [Pending item 1]
- [ ] [Pending item 2]

## Known Issues

### Active Issues
- [Issue 1]: [Description and current understanding]

### Workarounds in Place
- [Workaround 1]: [Why it exists, how to remove it]

## How to Continue

### Immediate Next Steps
1. [Step 1]
2. [Step 2]
3. [Step 3]

### Things to Watch Out For
- [Gotcha 1]
- [Gotcha 2]

### Who to Contact
- [Name/Team] for [Topic]
- [Name/Team] for [Topic]

## Resources
- [Link to design doc]
- [Link to requirements]
- [Link to related PRs]
```

## Handoff Meeting Checklist

If doing a live handoff:

**Before Meeting:**
- [ ] Prepare handoff document
- [ ] Ensure code is in clean state
- [ ] List questions you anticipate

**During Meeting:**
1. Walk through handoff document
2. Show current state of code
3. Demo any working functionality
4. Explain key decisions and trade-offs
5. Highlight risks and unknowns
6. Answer questions
7. Verify recipient understands

**After Meeting:**
- [ ] Share access to all resources
- [ ] Offer availability for follow-up questions
- [ ] Confirm handoff complete

## Code State Preparation

Before handing off, ensure:

```bash
# Clean working directory
git status  # Should be clean

# Latest changes committed
git log -1  # Recent meaningful commit

# Branch is up to date
git pull origin main

# Tests pass
npm test    # All green

# Build works
npm run build  # No errors
```

Leave the code in a state where:
- It compiles/runs
- Tests pass
- No work-in-progress changes uncommitted
- Clear commit messages explain recent changes

## Communication Templates

### Async Handoff Message

```
Hi [Name],

I'm handing off [Task/Project] to you. Here's what you need to know:

**Status:** [Current state in one sentence]

**What I've Done:**
- [Accomplishment 1]
- [Accomplishment 2]

**Next Steps:**
1. [Immediate next action]
2. [Following action]

**Watch Out For:**
- [Important gotcha]

**Resources:**
- Handoff doc: [link]
- Code: [branch name]
- Related PR: [link]

Let me know if you have questions!
```

### Requesting Additional Context

```
Hi [Name],

I'm picking up [Task] from your handoff. A few clarifications:

1. [Specific question 1]
2. [Specific question 2]

Also, I noticed [observation]. Was that intentional?

Thanks!
```

## Handoff Anti-Patterns

Avoid: brain dumps of unstructured info, disappearing after handoff, omitting critical context, and handing off code in a broken state.

## Receiving a Handoff

When you receive work:

1. **Read documentation** before asking questions
2. **Acknowledge receipt** to confirm handoff
3. **Identify gaps** in your understanding
4. **Ask focused questions** about specific unclear points
5. **Verify you can build/run** the current state
6. **Document** any additional context you discover

## Handoff Quality Checklist

For the giver:
- [ ] Documentation is complete and current
- [ ] Code is in clean, working state
- [ ] All access/permissions transferred
- [ ] Key contacts introduced
- [ ] Questions answered or noted
- [ ] Availability for follow-up communicated

For the receiver:
- [ ] Documentation reviewed
- [ ] Can build and run the code
- [ ] Understand current state
- [ ] Know next steps
- [ ] Know who to contact
- [ ] No blocking questions

## Integration with Other Skills

- **structured-review**: Get review before handoff if work is complete
- **parallel-investigation**: Handoff individual threads
- **planning/task-decomposition**: Reference task breakdown in handoff
