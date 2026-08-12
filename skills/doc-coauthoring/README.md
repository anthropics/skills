# Doc Co-Authoring

A structured workflow for writing documentation, proposals, technical specifications, and other complex documents with Claude's guidance.

## Quick Start

**Use this skill when:**
- Writing documentation, technical specs, or design documents
- Creating proposals, RFCs, or decision documents
- You want help organizing complex information
- You're unsure what the document should say or how to structure it
- You want Claude to help catch gaps and unclear sections before sharing

## The Three-Stage Workflow

This skill guides you through three phases:

1. **Context Gathering** (15-30 min): Share everything Claude needs to know
2. **Refinement & Structure** (30-120 min): Build the document section-by-section
3. **Reader Testing** (15-30 min): Validate the document works for readers

**For a quick overview of each stage**, see `references/stage-guide.md`.

**For the full workflow and examples**, read `SKILL.md`.

## What This Skill Does

### Context Gathering
- Asks clarifying questions about document type, audience, and goals
- Helps you organize information you might have scattered in your head
- Ensures Claude understands your constraints and context before drafting

### Refinement & Structure
- Suggests appropriate section structures based on document type
- Brainstorms content for each section (5-20 options per section)
- Helps you refine sections through iterative feedback
- Ensures nothing important is missing

### Reader Testing
- Tests the document with a "fresh reader" perspective
- Identifies gaps, ambiguities, or weak arguments
- Validates that the document achieves its intended purpose
- Catches issues before you share it publicly

## When to Use This Skill

### Ideal Use Cases
- Technical specifications (architecture docs, API specs, design docs)
- Decision documents (RFC, ADR, analysis)
- Proposals (business proposals, project proposals, funding pitches)
- Planning documents (project plans, strategy documents, roadmaps)
- Reports and analyses (research reports, findings, case studies)

### Less Ideal (Use Freeform Instead)
- Quick 1-2 page documents you know exactly what to say
- Documents where you just need Claude to polish/refine existing text
- When you prefer to iterate without structure

## Key Features

- **Structured guidance**: Three clear stages with exit conditions
- **Collaborative iteration**: You control the direction; Claude suggests options
- **Quality validation**: Reader testing catches blind spots early
- **Flexible pacing**: Adapt the workflow to your document complexity
- **Audience-aware**: Tailors structure and content to your specific readers

## Common Document Types & Structures

### Technical Specification
1. Overview & Goals
2. Architecture/Design
3. Data Model
4. API/Interface
5. Failure Modes & Mitigations
6. Timeline & Dependencies

### Decision Document (RFC/ADR)
1. Context
2. Options Considered
3. Decision & Rationale
4. Expected Outcomes
5. Next Steps

### Proposal
1. Executive Summary
2. Problem Statement
3. Proposed Solution
4. Benefits & Trade-offs
5. Implementation Plan
6. Budget & Timeline

### Design Document
1. Overview
2. Problem Statement
3. Proposed Solution
4. Architecture
5. Alternative Approaches
6. Risks & Mitigations

## Workflow Timing

| Document Type | Total Time | Context | Refinement | Testing |
|---|---|---|---|---|
| 1-2 page summary | 30-45 min | 10 min | 15 min | 10 min |
| Technical spec (5-10 pages) | 1-2 hours | 20 min | 60 min | 15 min |
| Decision document | 45-60 min | 15 min | 25 min | 15 min |
| Proposal (10+ pages) | 2-3 hours | 30 min | 90 min | 30 min |
| Complex RFC/design | 3+ hours | 30+ min | 120+ min | 30+ min |

## How to Get Started

### Option 1: Structured Workflow
"I want to write a technical spec for [topic]. Let's use your full workflow."

Claude will:
1. Ask meta-questions (type, audience, goal)
2. Guide you through information gathering
3. Suggest structure
4. Build section-by-section with your input
5. Test with a fresh reader

### Option 2: Freeform
"Let's write a spec together. I'll describe what I want, and you help me organize it."

Claude will:
- Collaborate iteratively without strict structure
- More flexible, faster for simple docs
- Still catches issues, just less systematically

### Option 3: Refinement Only
"I have a draft spec. Help me improve it."

Claude will:
- Read what you have
- Suggest improvements
- Iterate on specific sections
- Skip Context Gathering and Structure phases

## Quick Reference

| Stage | Duration | Goal | Exit Condition |
|---|---|---|---|
| Context Gathering | 15-30 min | Shared understanding | Claude understands core idea and constraints |
| Refinement | 30-120 min | Complete draft | All sections written and refined |
| Testing | 15-30 min | Validation | Reader Claude gets main points and finds no gaps |

## For Better Results

### Before Starting
- [ ] Know your audience (be specific)
- [ ] Have a rough idea of scope
- [ ] Gather any existing materials or context
- [ ] Consider your deadline

### During Context Gathering
- [ ] Be thorough—context gathering is not wasted time
- [ ] Share dissenting opinions or constraints
- [ ] Mention edge cases or special requirements
- [ ] Don't over-organize; Claude will organize

### During Refinement
- [ ] Give specific feedback ("remove X because Y", not just "better")
- [ ] Start with hard sections (core ideas) before easy ones
- [ ] Use examples to clarify complex ideas
- [ ] Anticipate reader objections

### During Testing
- [ ] Let Claude test objectively (don't coach the reader)
- [ ] Fix real issues Claude surfaces; ignore subjective preferences
- [ ] Do a final read-through yourself

## Common Pitfalls & Fixes

| Pitfall | Why it's a problem | Fix |
|---------|---|---|
| Skipping context gathering | Claude guesses wrong about audience/purpose | Invest 15-20 min in this phase |
| Vague audience ("just write something") | Doc optimizes for wrong readers | Be specific about who and why |
| Feedback like "sounds good" | Claude can't learn from it | Say what to change and why |
| Too many sections | Document becomes hard to follow | Combine related sections; move details to appendix |
| Skipping reader testing | Problems found after it's shared | Always test with fresh reader perspective |

## Related Skills

- **chief-of-staff**: Use for business planning and decision-making
- **skill-creator**: Use to document how to create skills
- **business-opportunity-finder**: Use for market/opportunity analysis sections
- **internal-comms**: Use for internal communication documents

## Troubleshooting

| Problem | Solution |
|---|---|
| Stuck in context gathering | Set a 20-minute timer and move to refinement |
| Can't agree on structure | Use Claude's suggestion first; restructure later if needed |
| Sections feel repetitive | Combine them or move details to appendix |
| Testing reveals major gaps | That's the point—fix them before sharing |
| Taking longer than expected | Complex docs take time; prioritize most important sections |

## Resources

- **Stage guide**: `references/stage-guide.md` — detailed walkthrough of each stage
- **Full workflow**: `SKILL.md` — complete instructions and edge cases
- **Examples**: TESTING_EXAMPLES.md (repository root) — real document examples
- **CLAUDE.md**: Repository guide with broader context

## For Contributors

This skill works best when:
- You provide honest feedback on what wasn't clear
- You test it with real documents and use cases
- You report issues with the workflow or guidance

---

**Last Updated**: August 2026  
**License**: Apache 2.0  
**Repository**: anthropics/skills

**Suggested Next Steps:**
1. Read `references/stage-guide.md` for stage details
2. Start with Context Gathering to share your document needs
3. Move through Refinement stage-by-stage
4. Use Reader Testing to validate before sharing
