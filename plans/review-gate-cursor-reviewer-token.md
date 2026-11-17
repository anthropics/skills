# Review Gate: add a `cursor` reviewer token

Status: planned, ready to start. PR #105 (review-gate 3.2.8) has merged (d876413), so the attestation grammar this plan extends is the one on main. Build on 3.2.8 or later, never on a pre-3.2.8 checker.

## Why

The reviewer fallback chain is now **Codex → agy → Cursor → Claude**, with no spend (Matt, 2026-11-16: "we have a fallback for a reason - fallback from Codex, to agy, to cursor, then to claude. If we are out everywhere, we have to wait till something has credits.").

The Review Gate's fallback attestation accepts only `codex|agy|antigravity|superpowers|claude-sonnet`. A real Cursor pass therefore cannot be attested. Today it would have to be mislabelled as another reviewer, which makes the attestation false, or skipped, which sends the PR straight to Claude (spend) before Cursor has been tried.

## Root cause

The reviewer token list is a hard-coded alternation in several places and was written before Cursor joined the chain. Nothing derives the list from one source, so adding a reviewer means finding every copy.

## Affected surfaces (grep before editing; this list is a starting point)

- `review-gate/scripts/check-review-gate.py`: the `Fallback review: (…) on <sha>` attestation regex and the failure message that lists the tokens.
- `scripts/check-review-gate.py`: the repo mirror of the checker (a repo-copy drift test must cover it).
- `review-gate/SKILL.md`: the attestation grammar and reviewer-chain documentation.
- `adversarial-review/SKILL.md`: the fallback order and the attestation line it tells reviewers to post.
- `review-gate/tests/test_check_review_gate.py`: add accept and reject cases for `cursor`, including near-miss tokens (`cursor-agent`, `Cursor`, `cursors`).
- The installer (`install-workflow`) and the vendored copies it writes into target repos, plus `review-gate.yml` if it embeds the token list.
- `~/.claude/references/pr-review-loop.md` and `credit-failover.md` (outside this repo; update the chain text so prose and grammar agree).

## Correct fix

1. Define the allowed reviewer tokens once in the checker (a single tuple) and build the regex and the error message from it, so the next reviewer is a one-line change.
2. Add `cursor` to the tuple.
3. Tests: a `cursor` attestation passes; every other token still passes; unknown tokens fail; the error message lists exactly the tuple. Include a test that the docs' token list equals the checker's tuple (behaviour over byte comparison).
4. Update both SKILL.md files and the installer output, then re-vendor into repos that carry the gate.
5. Migration: repos on the old grammar keep working (the new token only widens the allow-list), so no bootstrap commit is needed beyond the normal skill update.

## Out of scope

- Verifying that an attestation matches a real review. The Sonnet pass on #105 flagged self-attestation as a P1 (documented trust model); that is its own plan.
- Changing the chain order or adding spend.

## Priority

Medium. It blocks nothing today (Cursor Auto is out of credits until 12/6) but must land before Cursor is used as a fallback.
