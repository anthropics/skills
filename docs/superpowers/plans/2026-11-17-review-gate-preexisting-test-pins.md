# Plan: pin review-gate's untested fail-closed paths

## Origin

These came from a Sonnet mutation-coverage pass on bernierllc/claude-skills#105 at head 9c51e35. The survivors are on lines that are identical to main, so #105 did not introduce them.

They are rated P1 because the gate would pass when it should fail if any of them regressed. Today the code behaves correctly; no test pins that behaviour.

Tracker: https://app.notion.com/p/review-gate-P2-findings-from-105-Sonnet-pass-a-on-1a2cfc3-41b4efecc95a810594cdf6650b33155f

## Status

Gaps 1 and 2 were pinned in #105 (merged as d876413): the empty-head loop over `("", None)` in review-gate/tests/test_check_review_gate.py (around line 349) asserts both Codex checks return False. Gap 3 and the P2 survivors are not started. Proposed priority: P1.

## Gaps

1. Done in #105: `codex_done_on_head` returns False when `headRefOid` is empty. Its `if not head` guard is redundant with the commit check below it, so the test pins the behaviour, not that line (re-check on 9af68ae).
2. Done in #105: `codex_clean_comment_on_head` has the same no-head guard; a mutant flipping it is killed.
3. `run_gh` adds `--hostname <host>` for Enterprise repos. If that argument is dropped, the gate reads the default host's PR with the same number.

## Correct fix (tests only)

1. Point a fake `gh` on PATH that records its argv. Call `run_gh([...], hostname="ghe.example.com")`. Assert that `--hostname ghe.example.com` comes before the endpoint. Then call without a hostname and assert there is no `--hostname`.
2. Re-run the mutant (the `--hostname` argument dropped) and show that the suite now fails.

Also add the P2 survivors from the same pass, each as a one-line assert. Extend the subprocess `_run` harness in test_check_review_gate.py for the argv and env cases, and call `parse_repo_with_host` directly for the repo-normalisation cases:

- `CODEX_STATE` with `re.S` (a multi-line Codex state marker)
- usage errors exit 2
- a second positional PR number is rejected
- `PR_NUMBER` env fallback
- `.git` is stripped
- `www.github.com` is normalized

## Out of scope

Server-side merge enforcement is covered by 2026-11-17-api-merge-guard.md.

Not added: CRLF in `closes()`. It is already tested (CRLF, lone CR and `\r\nmore` cases), and the surviving mutant (dropping the CRLF replace) is equivalent.
