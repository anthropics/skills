---
name: prompt-fieldtest
description: Field-test an instruction document (a rule file, CLAUDE.md, an agent, another skill) by having a team of agents build against it blind, audit what it caused, and destroy the evidence. Use when asked to review, stress-test, validate or improve a prompt/rule/convention file in practice rather than by reading it.
disable-model-invocation: true
---

# Prompt field test

Target document: **$ARGUMENTS** (if empty, ask which file — do not guess).

## Baseline, captured before anything is built

!`git status --porcelain --untracked-files=all`

!`git stash list`

## What this is

Reading an instruction document tells you whether it's *agreeable*. Making someone
follow it blind tells you whether it's *followable*, and what it actually produces.
This skill does the second thing: a fresh agent builds a throwaway feature guided only
by the document, a second agent audits what the document caused, a third erases it.

The deliverable is a report about the **document**. The code is a probe, never a
product — it gets deleted in phase 4 regardless of how good it is.

Findings only count if they trace to a specific line of the document and a specific
line of what the builder produced. A criticism you could have written without running
the test is a criticism you should have written without running the test — cut it.

## The team

Three subagents do the work. Their standing instructions live in their own files; what
you supply at invocation time is the run-specific payload.

| Phase | Agent | Why it's shaped that way |
| --- | --- | --- |
| 1 | `prompt-fieldtest-feature-builder` | Its **prose** never mentions probes, audits or reviews. It reads its own system prompt, so any such mention in that file would un-blind it permanently. The name is the one leak we accept for discoverability — it can infer the family it belongs to, so the blinding rests entirely on the file's wording and on the Phase 1 invariants below, never on the name. |
| 2 | `prompt-fieldtest-auditor` | No `Bash`, no edit tools — read-only is enforced by the tool list rather than merely asserted in prose. |
| 4 | `prompt-fieldtest-cleanup` | Needs a real shell, so its prohibitions can only live in prose. `tools:` cannot scope `Bash`; treat that file's forbidden-command list as the only control that exists. |

## Phase 0 — read the target, then design the probe

Read the target document yourself, fully, plus whatever it points at (token modules,
configs, referenced paths). You need this to judge the reports later; you cannot
outsource it.

Then design a build spec. This is the part that determines whether the whole exercise
is worth anything, so spend real effort here:

- **Cover the clause surface.** Walk the document's clauses and choose a feature that
  forces most of them to fire. Note in advance which clauses your spec will *not*
  exercise — those stay untested, and the report must say so rather than implying
  full coverage.
- **Include at least one clause that requires the builder to *extend* something**, not
  just consume it — a token that doesn't exist yet, a missing helper, a new module.
  Clauses about consuming an existing system almost always pass; clauses about growing
  it are where documents turn out to be silent.
- **Include at least one thing the document is plainly silent on**, chosen deliberately.
  What the builder invents to fill a gap is the highest-value output of this exercise,
  and silences never surface if the spec only asks for what the document covers.
- **Include any documented technical caveat** (a compiler version workaround, a
  framework gotcha) so you can verify empirically whether it's still true.
- **Write the spec as a product brief, in product language.** "Rows stack on mobile and
  go horizontal from tablet up." Never in the document's own vocabulary — if you name
  the clauses, you're testing the builder's reading comprehension of your prompt
  instead of the document's clarity.

## Phase 1 — build

Invoke the **`prompt-fieldtest-feature-builder`** agent. It already knows how to work: follow the
conventions at the path it's given, never edit them, make its own calls instead of
asking, prove the checks pass, and report its file list plus an honest account of every
guess. Don't restate any of that.

What you supply is the payload — and two invariants that live here, in your prompt,
because the agent must never learn them:

- **Never tell it this is a document review.** An agent that knows it's being graded on
  compliance over-performs on compliance, and you lose every signal about what the
  document fails to say. Its own file is written to read as a genuine feature agent for
  exactly this reason; don't undo that by mentioning the field test, the audit, or the
  fact that the code will be deleted. It thinks it is shipping a feature.
- **Never paste the document into its prompt.** Pass the path and say the conventions
  are mandatory. Pasting turns a test of "is this findable and readable in place" into a
  test of "can an agent follow instructions in its context," which you already know the
  answer to.

So the invocation carries exactly three things: the product brief from phase 0, the path
to the conventions document, and the paths it may touch.

## Phase 2 — audit

Invoke **`prompt-fieldtest-auditor`** — but **only after the build lands**, and
**without the builder's self-report**. Two blind passes that converge on the same
finding is the strongest evidence this method produces; showing the auditor the
builder's report destroys that independence and you can never get it back.

Its mandate, taxonomy, and output shape are all in its file. The invocation carries:

- the path to the target document,
- the list of files the builder produced — **paths only**, stripped of the builder's
  commentary about them.

Withhold your phase 0 coverage notes as well. The auditor reports never-exercised
clauses independently; comparing its list against yours afterwards is a free check on
both.

## Phase 3 — verify the reports yourself

Both agents will state things with total confidence that are wrong. Do not relay any
load-bearing claim you have not checked. In practice the cheap checks are:

- **Empirically test documented technical claims.** Write a minimal probe in the
  scratchpad, run the real toolchain against it, delete it. A caveat that reproduces is
  validated and should be defended; one that doesn't is dead weight to cut.
- **Check claims about tooling against the resolved config**, not against what the
  agent assumed — `npx eslint --print-config <file>`, the actual formatter config, the
  installed versions. "This would trip lint" is frequently false.
- **Check comparisons against the right comparand.** An agent will call something
  inconsistent with a sibling file while the file it was actually modelled on does the
  same thing.
- **Check the document's own scope.** If it has path-matching frontmatter, work out
  which files it governs and which it doesn't. Clauses that legislate files the
  document never attaches to are a real structural defect and neither agent is
  positioned to notice it.

The auditor has no shell by design, so every empirical claim in its report is inference.
Treat it that way.

Say in your report which claims you discarded and why. It's the difference between
relaying three agents and having reviewed them.

## Phase 4 — cleanup

Before you invoke anything, record the target document's hashes yourself so you can
prove it survived:

```bash
shasum -a 256 <target>          # worktree content
git rev-parse :<target>         # staged blob, if staged
```

Then invoke **`prompt-fieldtest-cleanup`**. Its file carries the prohibitions and the
verification checklist; it will refuse to act on a vague instruction, and it's right to.
The invocation must therefore enumerate:

- exactly what to remove — directories the build created, and each new file,
- exactly which tracked files to revert,
- the pre-existing modified and staged state from the baseline above that it must not
  touch — **especially the target document itself, which is usually mid-edit**,
- the baseline `git status` output, so it can verify against a fixed target rather than
  its own idea of clean.

Re-check both hashes afterwards. Verify the cleanup independently rather than trusting
its report — your own `git status` is worth more than its summary.

## Phase 5 — report

Lead with how the document actually performed in absolute terms: a document that
produced compiling, passing, near-compliant work is a good document, and burying that
under a defect list misrepresents it.

Then, in order:

- **Findings that matter**, ranked by damage, each with the classification, the evidence
  from both sides, and the concrete replacement wording. Mark which ones both agents
  found independently — that convergence is your confidence signal.
- **What's working and should be left alone**, with the evidence that it paid off.
- **The pattern.** Several findings are usually one hole seen from different angles;
  naming it is more useful than the list. Look especially at whether the clauses that
  worked are the ones that explain *why* — bare assertions tend to get over-applied by
  careful readers and ignored by everyone else.
- **What went untested**, from your phase 0 notes.

Offer to apply the fixes, split into mechanical edits you'll just make and genuine
policy decisions that are the user's call. Don't edit the target document as part of
this skill — field-testing it and rewriting it are separate jobs, and the user may
disagree with half the findings.

## Hard rules

- **Strictly sequential.** Build → audit → cleanup. Each phase needs the previous one's
  output; running them concurrently produces an auditor reviewing a half-written tree.
- **No agent may edit the target document.** The auditor can't (no edit tools), the
  cleanup agent is told to protect it, and the builder is told the path is off limits —
  say so in the builder's prompt every time regardless, since it's the one with a full
  toolset.
- **Never leak the exercise to the builder.** If you find yourself explaining why the
  brief looks arbitrary, stop: that explanation is the leak.
- **Agents routinely go idle without delivering their report**, because plain text
  output doesn't reach you. When one does, message it and ask for the report explicitly.
  Never write, guess, or summarise a report that hasn't arrived.
- **The probe always dies.** If the user wants to keep it, that's a new request — this
  skill's contract is that the repo ends where it started.
