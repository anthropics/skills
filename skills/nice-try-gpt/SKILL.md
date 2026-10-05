---
name: nice-try-gpt
description: Analyzes authorized CTF challenges by reproducing intended solves, identifying cheap LLM shortcuts, applying minimal human-friendly transformations, and verifying results end-to-end. Appropriate when reviewing or adapting CTFs to reduce pattern-matching shortcuts without materially increasing human difficulty.
license: GPL-3.0-only
metadata:
  author: aleff-github
  version: "0.2.0"
---

# NiceTryGPT

Less pattern matching. More actual hacking.

Use this skill only for CTFs, training labs, and systems the user is authorized to test.

## Core contract

The goal is not to make the challenge harder in general. The goal is to reduce one cheap LLM shortcut while keeping the challenge fair and recognizable to a human player.

Preserve these invariants:

1. Same intended vulnerability class.
2. Same learning objective.
3. Same prerequisite knowledge.
4. Same flag or success semantics.
5. Roughly the same human difficulty band.

Default to **one** resistance change. Use a second only when the first is insufficient and the Human Cost Gate still passes.

It is valid to make no change.

Use these final statuses exactly:

- `BASELINE FAILED`
- `NO CHANGE NEEDED`
- `TRANSFORMED PASS`
- `TRANSFORMED FAILED`

## 1. Understand

Read only what is needed to understand and run the challenge:

- player-facing description;
- entry point;
- relevant source/configuration;
- run or build instructions;
- flag format or equivalent success condition;
- intended learning objective.

Before editing, record:

- vulnerability class;
- intended solve path;
- expected player knowledge;
- approximate difficulty band;
- clean-start procedure.

Do not modify files yet.

## 2. Baseline solve

Start from a clean state and solve the original challenge end-to-end through the player-facing surface.

A valid baseline must obtain the runtime flag or equivalent success condition through the intended vulnerability.

Do **not** count any of these as a solve:

- reading the flag directly from source;
- reading fixture or environment values directly;
- inspecting container internals only to extract the answer;
- assuming the documented solve works without reproducing it.

If the baseline cannot be reproduced, stop with `BASELINE FAILED`. Do not transform an unverified challenge.

## 3. Identify the cheapest shortcut

Ask:

> What lets an LLM jump from observation to solution without enough interaction or hypothesis testing?

Choose one primary shortcut, supported by evidence from the baseline. Examples:

- a parameter or endpoint practically names the vulnerability;
- the next obvious numeric ID is the target;
- a textbook payload works immediately with no discovery;
- all solve-relevant facts appear in one static response;
- an error message reveals the intended path;
- a static value removes the need to observe runtime behavior.

Do not invent a problem just to justify a transformation.

## 4. Pick the smallest resistance move

Choose zero, one, or at most two lightweight moves:

- **Pattern break** — remove an overly explicit cue without hiding the vulnerability.
- **Runtime discovery** — move one solve-relevant fact into normal runtime behavior.
- **Context split** — require connecting two nearby pieces of ordinary application behavior.
- **State dependency** — let a small amount of ordinary state matter.
- **Semantic decoy** — add one plausible but cheaply falsifiable attack surface.

Read `references/resistance-patterns.md` only when selection guidance is useful.

Do not stack patterns by default.

## 5. Human Cost Gate

Reject a proposal unless all of these remain true:

- same vulnerability class;
- same learning objective;
- same prerequisite knowledge;
- no new exploit primitive required;
- no brute force;
- no CAPTCHA or human-verification gimmick;
- no huge context, token flooding, or pointless encoding;
- no obscure external trivia;
- no artificial multi-stage chain;
- normally no more than 1–3 additional meaningful player actions;
- expected solve difficulty stays in the same band.

A meaningful action is an interaction that materially advances or rejects a hypothesis, such as one request, command, or inspection step.

For semantic decoys:

- default to zero;
- if useful, add only one semantic decoy;
- make it dismissible in 1–2 normal interactions;
- never use fake flags, destructive traps, or punishment.

If a useful resistance change fails this gate, keep the original challenge and report `NO CHANGE NEEDED`.

## 6. Modify

Implement the smallest diff that satisfies the chosen strategy.

Preserve normal application behavior. Avoid cosmetic rewrites that do not change the shortcut.

Runtime randomization is acceptable only when:

- the player can discover the randomized value through normal interaction;
- it never requires guessing or brute force;
- it does not make the challenge flaky.

Do not hide the flag behind randomness or instability.

## 7. Verify end-to-end

Restart or rebuild from a clean state.

Verify all applicable checks:

1. application starts normally;
2. legitimate player-facing functionality still works;
3. the intended vulnerability still exists;
4. the original cheap shortcut is actually reduced or removed;
5. the transformed solve works end-to-end;
6. the runtime flag is obtained through the vulnerability;
7. the flag is not leaked by unrelated surfaces;
8. any decoy has a normal path that works and an obvious exploit probe that fails safely.

If verification fails, simplify or revert the transformation. End with `TRANSFORMED FAILED` if a valid transformed challenge cannot be restored.

## 8. Fresh-solver check

When a genuinely isolated context, subagent, or separate model is available, give it only the player-facing challenge information and ask it to solve the transformed challenge.

Do not reveal:

- the baseline solution;
- the shortcut analysis;
- the transformation plan.

If no independent solver is available, mark the result `NOT TESTED`.

Never claim that self-review proves LLM resistance.

## 9. Report

Create or update `nicetrygpt-report.md` in the challenge root.

Keep it short and include:

- final status;
- baseline result;
- vulnerability class;
- shortcut identified;
- transformation used, or `NO CHANGE NEEDED`;
- human-cost estimate in additional meaningful actions;
- original difficulty band;
- post-change difficulty band;
- post-change E2E result;
- fresh-solver result or `NOT TESTED`;
- files changed.

## Success rule

A transformation succeeds only when the learning objective is preserved, the challenge still works end-to-end, and the identified shortcut is reduced without materially worsening the human experience.

If those goals conflict, favor the human player.
