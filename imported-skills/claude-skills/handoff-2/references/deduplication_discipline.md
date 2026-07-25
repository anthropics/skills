# Deduplication Discipline

Matt's core rule, made operational:

> Do not duplicate content already captured in other artifacts (PRDs, plans, ADRs, issues, commits, diffs). Reference them by path or URL instead.

This document turns that rule into a list of concrete *do-this-not-that* pairs the agent applies before saving.

## Why this matters

A handoff that duplicates artifacts goes stale the moment the artifact updates. A handoff that references artifacts stays correct as long as the references resolve. The reader follows links to canonical sources; they don't trust the handoff to be the source of truth.

A second reason: duplication grows the file, which grows the next session's context window, which costs tokens and attention. Every paragraph that isn't a link is a paragraph the next agent has to read.

## The do-this-not-that pairs

### 1. The diff

| Don't | Do |
|---|---|
| Paste the diff into the handoff. | Reference the branch (`feature/foo`) or PR (`#123`). |
| List every file you touched. | "Touched 14 files across `src/auth/` and `tests/auth/` — see PR for full list." |
| Quote a 40-line code block to "preserve context." | Link to the file path + line range: `src/auth/login.ts:42-87`. |

### 2. The PRD

| Don't | Do |
|---|---|
| Retype the PRD as bullet points. | Link to the PRD path. |
| Summarise the PRD because "the next agent might not have access." | If they don't have access, the access is the bug — fix that. |
| Paraphrase the user stories. | Reference them by ID. |

### 3. The commit message

| Don't | Do |
|---|---|
| "I committed a fix for the redaction edge case." | "Fixed redaction edge case — `a1b2c3d`." |
| Narrate the commits in order. | "5 commits on `feature/foo`. See `git log feature/foo`." |

### 4. The issue / ticket

| Don't | Do |
|---|---|
| Restate the bug from the issue body. | "See issue #456." |
| Copy the acceptance criteria. | "Acceptance criteria in #456." |
| Quote the latest comment. | "Latest comment from @teammate at issue #456." |

### 5. The conversation itself

| Don't | Do |
|---|---|
| Recap the conversation chronologically. | Compress to State of play + Open decisions. |
| List every question the user asked. | Surface only the questions that became decisions. |
| Include the back-and-forth that led to a conclusion. | Just the conclusion. |

### 6. Suggested skills

| Don't | Do |
|---|---|
| List 20 skills "in case any are useful." | Pick 3-5 and say *why each*. |
| Recommend a skill without explaining the link to the goal. | "code-review — to review the PR before opening it." |
| Re-explain what each skill does. | The next agent reads the SKILL.md if needed. |

### 7. Artifacts

| Don't | Do |
|---|---|
| Embed the full PR description. | Link to the PR. |
| Quote the relevant lines from an ADR. | Link to the ADR path + section. |
| Paste a CI log to show what failed. | Link to the failing CI run + one-line summary ("type-check failed at L42 of `foo.ts`"). |

## What survives the rule

Some content must live inline in the handoff because it doesn't exist anywhere else:

- **Open decisions and your lean** — these are *new* information the conversation produced. Inline them.
- **State of play prose** — the synthesis itself. The artifacts exist; the synthesis is the handoff.
- **Forcing constraints** — "Deadline: EOD." These often live only in the conversation.
- **Sub-text and known-unknowns** — "Reviewer hates verbose tests, so keep new tests short." This shapes the work and isn't in any artifact.

If you're unsure, ask: *does removing this and replacing with a link lose any information?* If no, replace it. If yes, keep the inline content.

## Anti-pattern: defensive duplication

Defensive duplication looks like: *"I'll paste the diff inline too, just in case the link breaks."*

Resist. If links can break, that's a separate problem — fix the link, don't duplicate. Defensive duplication causes the second failure mode this rule is designed to prevent: a handoff that contradicts the artifact it duplicates.

## Sources

- Matt Pocock, *Handoff skill* (MIT) — the original rule.
- Karpathy, *Software 3.0 talk* (2025) — context engineering: every duplicated paragraph is a future contradiction.
- Cory Doctorow, *Writing for the machine that reads* (essay) — references over copies, durably.
- Google SRE Workbook — postmortem hygiene: link to evidence, do not paraphrase it.
- Atlassian, *Confluence handoff template guide* — the same discipline at organizational scale.
- Edward Tufte, *Beautiful Evidence* — the principle of *information density*: one source of truth per fact.
