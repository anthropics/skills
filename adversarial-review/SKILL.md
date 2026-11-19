---
name: adversarial-review
description: Run the adversarial PR review loop with Codex-first spend and inline line-item PR comments. Use whenever you open or push a PR, say a PR is ready, hand work to a traffic cop, need a code review, or fall through reviewers after Codex/agy quota failures. Prefer this skill over remembering review order from AGENTS.md prose.
version: 2.2.0
author: Bernier LLC
---

# Adversarial review

Durable form of `~/.claude/references/pr-review-loop.md`. Agents forget prose; install this skill per repo so the loop is loadable and enforceable alongside `review-gate`.

## Spend posture (Matt, 2026-11-07)

| Role | Model | Notes |
|------|--------|------|
| Coding | Claude Opus → Cursor Auto | Not this skill |
| Traffic cops | Codex mid (`gpt-6-astra`) | See `traffic-cop.md` |
| **Adversarial review (this skill)** | **Codex high first** | Burn OpenAI review budget here |
| Fallthrough | Antigravity (`agy`) → Claude Sonnet last | Record which ran |

## When to run

After opening a PR or pushing commits to one. Never declare "ready" in the same breath as the push. Run reviewers and CI **in parallel**.

## Reviewer order (fall through only when unavailable)

1. **Codex first**
   - **GitHub:** Codex reviews the PR's first head on open. **Never post a comment that mentions the Codex bot** (the at-sign followed by `codex`, e.g. asking it to review): each one starts a review on Matt's Codex quota (Program Cop, 2026-11-19). Every later head gets a fallback review (below) and the `Fallback review:` attestation line in `## Review` (see PR body). Only Matt's explicit ask overrides; then the command carries a `# codex-review-ok: <reason>` shell comment (colon optional), which `pr-merge-flow`'s guard requires.
   - **T3 parallel local:** `delegate_task` with `modelSelection` `{ "instanceId": "codex", "model": "gpt-6.1-sol" }` against the PR diff.
   - Unavailable: quota exhausted, not started within ~15 min of first request, or absent from the repo.
   - **After Codex completes:** if required check `Review Gate` is still red (parallel open/synchronize often failed before the review landed), re-fire the trusted `pull_request_target` workflow with a no-op label toggle (e.g. add then remove `review:refresh`) or a trivial PR body edit — do not wait on review-event Actions (those are intentionally disabled for security).
2. **Antigravity (`agy`) headless** — outside Claude tokens. Inline the diff in the prompt; `--sandbox --dangerously-skip-permissions --model gemini-3.8-flash-high`. See `pr-review-loop.md` for the verified command shape.
3. **Claude Sonnet / `superpowers:requesting-code-review`** — last resort only.

Standing consent: switch providers on unavailability without asking Matt again. No new subscriptions or weaker merge gates.

## Inline comments (required)

Every P0/P1 finding must become a **GitHub review thread on the relevant line**, not only a summary comment.

- Prefer `gh api graphql` / `POST /repos/{owner}/{repo}/pulls/{n}/comments` with `commit_id`, `path`, `line` (or `subject_type` + multi-line fields as appropriate).
- Summary sticky comment is fine **in addition** for the round overview; it does not replace line threads.
- P2: one-line each; fix ≤10 lines in touched files or Tracker row + PR reply with Notion link.

Every review brief opens with the redundancy question: *does this reimplement something the framework, a dependency, or this repo already provides?*

## Severity and convergence

- **P0/P1:** fix at root before merge.
- **P2:** ≤10-line fix in touched files, else Tracker + closing reply.
- **Nit:** answer or ignore; never a new round.
- Done when a round has **no new P0/P1**.
- One push per round. Cap: third P0/P1 in the same area → simplify or plan, tell Matt.

## PR body

Maintain a `## Review` section naming which reviewer ran and the round count. When the GitHub Codex bot (`chatgpt-codex-connector`) did not review the current head, add this explicit attestation only after the review that did run completes, including a local Codex high review (replace the example SHA with the head actually reviewed):

```text
## Review

Fallback review: claude-sonnet on 89cda0610123456789abcdef0123456789abcdef — verdict: clean
```

The exact format is `Fallback review: <reviewer> on <sha> — verdict: <verdict>` on one plain-text line. Allowed reviewers: `codex` (local Codex, e.g. T3 Codex high), `agy`, `antigravity`, `superpowers`, `claude-sonnet`. Allowed verdicts: `clean`, `findings fixed`. The SHA must be the full 40-hex current head OID (`gh pr view <n> --json headRefOid`); a prefix does not count. Lines containing `pending`, `running` or `TODO` are rejected, as are keyword-only prose, URLs and generated footers. After every push, rerun review before updating the attestation; never just copy the new SHA. See [review-gate](../review-gate/SKILL.md) for enforcement.

## Plan / spec PRs

One local adversarial pass **before** the first Codex review (exhaust pipeline/state/schema/auth/deploy/frontend/cross-plan classes). Then Codex.

## After the loop

In T3: hand the PR to `Traffic Cop · <repo>` (`traffic-cop.md`). Do not self-merge around a missing cop.

Install **`review-gate`** in the same repos so merge/CI enforcement matches this loop (conversation resolution + trusted `Review Gate` check).

## Related

- Full detail / CLI examples: `~/.claude/references/pr-review-loop.md`
- Merge discipline: skill `pr-merge-flow`
- Server + hook enforcement: skill `review-gate`
- Credit failover for stuck threads: `~/.claude/references/credit-failover.md`

<!-- feedback-loop:begin -->
## Feedback

If the `feedback-loop` skill is installed, use it to improve this skill over time:

- When this skill's own instructions cause rework, a wrong default, a missed case or a needless
  pause, log it as it happens: subject `skill:adversarial-review`, with the phase or section at fault and the
  concrete fix to these instructions.
- When the project's own process causes friction during this skill's work (for example a flaky
  or slow CI job, a test that missed a regression, a plan that was wrong about the code), log it
  as subject `process:<project>` with `--area <ci|test|plan|review|deploy|dev>`.
- At the end of a run, check `skill:adversarial-review`; if a review is due, make the feedback-loop offer.

If `feedback-loop` is not installed, ignore this section.
<!-- feedback-loop:end -->
