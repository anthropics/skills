---
name: "cross-eval"
description: "/cs:cross-eval <memo> — Multi-model consensus on a board memo or strategy brief. Claude + Codex + Gemini cross-review with graceful degradation. Use when a high-stakes memo needs an independent sanity check before the boardroom — e.g. a bet-the-company pivot or fundraise terms."
---

# /cs:cross-eval — Multi-Model Consensus

**Command:** `/cs:cross-eval <memo-or-brief>`

Runs the same memo through multiple model providers and reconciles divergences. Use for **high-stakes, irreversible decisions** where single-model bias is too costly: M&A, major fundraises, layoffs, strategic pivots, regulatory commitments.

Adapted from gstack's `/codex` cross-review pattern, generalized to **business memos** instead of code PRs.

## When to Run

- Before signing a term sheet
- Before announcing a layoff
- Before committing to a regulated market
- Before any decision where reversing costs > 6 months of company time
- When the boardroom vote was split or had a CRITICAL dissent

## Models Used (graceful degradation)

The command tries to invoke each available model in order:

1. **Claude** (primary, always available) — the boardroom's native voice
2. **Codex / OpenAI** (if `OPENAI_API_KEY` or `codex` CLI available)
3. **Gemini** (if `GEMINI_API_KEY` or `gemini` CLI available)

If only Claude is available, the command runs **Claude-only with adversarial mode** — same model, different prompt seeds — and clearly labels the output as single-model.

## Workflow

1. Read the memo / brief
2. Probe environment for available model CLIs / API keys
3. For each available model:
   - Send the memo with this prompt prefix:
     > "You are an independent C-suite reviewer. The following is a board memo from another company's boardroom. Identify the top 3 concerns, the top 3 supports, and your vote (APPROVE / REJECT / DEFER). Do not deferentially agree — assume the memo's reasoning is flawed until proven otherwise."
4. Collect three independent reviews
5. Reconcile: where do they agree? Where do they diverge?
6. Surface the divergences as questions for the founder

## Output Format

Saved to `~/.claude/cross-eval/YYYY-MM-DD-<slug>.md`:

```markdown
# Cross-Eval: <memo title>
**Date:** YYYY-MM-DD
**Memo reviewed:** <link>
**Models invoked:** Claude / Codex / Gemini (or noted fallbacks)

## Vote Tally
| Model | Vote | Confidence |
|---|---|---|
| Claude | APPROVE | High |
| Codex | DEFER | Med |
| Gemini | APPROVE | Low |

## Consensus Concerns (≥2 models flagged)
1. <concern> — flagged by Claude + Codex
2. <concern> — flagged by all 3

## Divergent Concerns (1 model flagged)
- <Codex only:> <concern> — worth a second look
- <Gemini only:> <concern> — likely noise, but check

## Consensus Supports (≥2 models endorsed)
1. <support>
2. <support>

## Recommendation
- 🟢 GO if 2+ models APPROVE and no CRITICAL concerns from any model
- 🟡 PAUSE if any model is DEFER or any concern is CRITICAL
- 🔴 STOP if 2+ models REJECT

## Open Questions for Founder
1. <question raised by divergence>
2. <question raised by divergence>
```

## Why This Matters

Single-model recommendations have systematic biases. Claude trends helpful and may under-weight risk. Codex (OpenAI) trends more cautious on emerging-market and regulatory topics. Gemini trends more cautious on technical scale claims. Disagreement is signal, not noise.

This is the **safety net before irreversibility** — not a replacement for outside counsel or a real board.

## Graceful Degradation

If only Claude is available:

```markdown
**Models available:** Claude only
**Mode:** ADVERSARIAL — running 3 independent Claude passes with different system prompts:
  1. Standard reviewer
  2. Devil's advocate (must find 3 critical concerns)
  3. Steelman (must find 3 strongest reasons to approve)

This is weaker than true multi-model. Treat the result as suggestive, not conclusive.
```

## Routing

- `/cs:decide` — if consensus is GO
- `/cs:freeze` — if consensus is PAUSE
- `/cs:boardroom` (re-run) — if consensus is STOP

## Related

- Skills: [`board-meeting`](../../../skills/board-meeting/SKILL.md), [`executive-mentor`](../../../executive-mentor/)
- Inspiration: gstack's `/codex` cross-review pattern (adapted to business memos)

---

**Version:** 1.0.0
