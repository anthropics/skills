# Diagnostic Question Bank

Use these questions when the user's submission is incomplete — they have pasted Custom Instructions but not described their knowledge files, or they have described symptoms but not provided the Project materials. Select the most relevant questions rather than asking all of them; tailor to what information is missing.

## Architecture Discovery

Ask these when you need to understand the Project's structure before auditing:

- How many knowledge files does this Project have, and what does each one contain?
- What are the main task types users perform in this Project?
- Who uses this Project — what is their expertise level?
- What output formats does the Project produce?
- What is the Project's scope — what is explicitly outside it?

## Memory Discovery

Ask these when you need to understand the Project's Memory configuration:

- Has the Project's Memory been configured with manual edits, or is it using only auto-populated memories?
- What orientation facts does Claude need in every conversation — current project phase, key constraints, user role, active decisions?
- Is there a build_context.md or similar institutional memory file in the Project's knowledge files?
- Has the Memory been reviewed since the Project's last significant change?

## Symptom Discovery

Ask these when the user reports problems but has not provided enough detail to diagnose:

- What specific output problem are you seeing? (Generic output, wrong format, shallow analysis, inconsistent quality, wrong tone, excessive length, etc.)
- Is the problem consistent or intermittent across conversations?
- Does the problem affect all task types or only specific ones?
- When did the problem start — was the Project working better before?
- Can you provide an example of a conversation where the output was not what you expected?

## Context Discovery

Ask these when you need background to evaluate whether the Project's architecture fits its purpose:

- What domain does this Project operate in?
- How often is the Project used — daily, weekly, occasionally?
- Has the Project been modified since initial setup?
- Are there any specific Claude behavioral tendencies you have noticed? (Over-agreeing, hedging, verbosity, list overuse, fabricated precision, over-exploration, tool overtriggering, LaTeX defaulting)

## Usage Guidance

Do not ask all questions at once. Select the 2–4 most relevant questions based on what the user has already provided. If they have pasted Custom Instructions but not described knowledge files, focus on Architecture Discovery. If they have described symptoms without providing materials, focus on Symptom Discovery first, then ask for the Project materials.

Frame questions as helping you produce a more accurate audit, not as a gatekeeping step. If the user provides enough material for at least a partial audit, begin the audit and note which dimensions could not be fully evaluated due to missing information.
