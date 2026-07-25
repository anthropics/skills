# Handoff Prompt — Mandatory Checklist for the Agent

This is the discipline that turns a free-hand summary into a faithful handoff. Walk every item before writing the doc. **No exceptions.**

The goal of the checklist is one thing only: prevent the model from free-handing a rosy summary that drops the actual blockers.

## Step 1 — Walk the conversation explicitly

For **each topic** discussed in the conversation, classify it as exactly one of:

1. **Include in State of play** — work that's done, in flight, or blocked. Reference the artifact (PR, branch, commit, file path).
2. **Log as an Open decision** — a question the next agent must answer before continuing.
3. **Drop with reason** — out of scope for the handoff. Note it inline as a comment if the decision to drop is non-obvious.

If a topic spans multiple classifications, split it. Do not merge.

> **Anti-pattern:** writing the State section by skimming the conversation top to bottom. That misses dropped threads and blocked items that came up mid-conversation.

## Step 2 — Verify each State item against an artifact

For every bullet in **State of play**, name the artifact that proves it:

- "Implemented X" → name the commit hash or PR number.
- "Tested Y" → name the test file or CI run.
- "Documented Z" → name the doc path.
- "Blocked on W" → name the issue, comment, or external party.

If you cannot name an artifact, the item is either not yet done, or it's an Open decision. Reclassify.

> **Anti-pattern:** "Implemented the new endpoint." — vague, unverifiable, and the next agent has no idea where to look.

## Step 3 — Surface every Open decision

A handoff that hides decisions makes the next session repeat work. For each decision:

- State the question in one sentence.
- List the options already considered (even if rejected).
- State which option you lean toward and why — or "no lean yet."
- Name the constraint that forces the decision (deadline, budget, dependency).

> **Anti-pattern:** "TODO: figure out caching." — gives the next agent no starting point.

## Step 4 — Pick 3-5 skills, no more

For **Skills to use**:

- Hard cap at 5.
- Each entry: skill name + one-line *why this session needs it*.
- If you find yourself listing more than 5, you haven't picked. Choose.
- If you find yourself listing fewer than 3, ask: is something obvious missing? (Often a review skill or a verifier.)

> **Anti-pattern:** listing every skill that might be tangentially useful. The reader stops reading after item 8.

## Step 5 — Artifacts as paths and URLs only

For **Artifacts**:

- Branches, PRs, issues, file paths, doc URLs.
- One line each.
- Never paste content. If the next agent needs to see the diff, they open the branch.

> **Anti-pattern:** pasting the PRD because "what if they can't access it?" If they can't access it, the link is the bug — fix that, don't duplicate.

## Step 6 — Run the redaction linter before saving

Before save, the linter scans for secrets and PII. In strict mode it blocks save until findings are resolved. Use the inline marker `<!-- handoff:allow secret -->` to whitelist a specific match if it's a false positive.

Patterns it cannot catch (do these by eye):

- Internal hostnames and IPs that aren't shaped like obvious secrets.
- Names of customers, partners, or unrelated third parties.
- Free-form leakage in narrative ("Last week Ann from FinCo asked us to…").

## Step 7 — Compare against Matt's no-duplication rule

Final pass before save:

- Does any section paste content that exists elsewhere? Replace with a link.
- Does any section narrate the conversation linearly? Compress to State + Decisions.
- Does any bullet say "the user did X"? Rewrite as the artifact (commit, message, decision).

## What "done" looks like

A handoff is done when:

1. Every State bullet has an artifact reference.
2. Every Open decision has a one-sentence question + at least one option.
3. Skills to use has between 3 and 5 entries.
4. Artifacts has only paths/URLs.
5. Redaction linter exits clean (or all findings are whitelisted with reason).
6. A fresh agent could pick up the work without reading the original conversation.

Test the last item by asking yourself: *if I close the conversation right now and a stranger opens this doc, do they know the next 30 minutes of work?* If no, go back to Step 1.
