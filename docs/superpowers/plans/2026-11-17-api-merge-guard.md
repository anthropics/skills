# review-gate: enforce merges server-side (API merges skip the client guard)

- **Origin:** claude-skills PR #105, Sonnet adversarial pass (a) on 1a2cfc3, finding P1-1. Deferred from #105 by Program Cop ruling as a scope deferral with a plan, not a not-a-finding.
- **Tracker:** https://app.notion.com/p/review-gate-enforce-merges-server-side-so-API-GraphQL-git-push-merges-cannot-skip-the-gate-plan-fr-41b4efecc95a8188b633c084b161109c
- **Status:** proposed. **Priority proposal:** P1 (High). Until it lands, the gate is advisory for any agent that merges by a route other than `gh pr merge`.

## Root cause

`review-gate/scripts/merge-guard.py` is a PreToolUse hook that reads the shell command text and blocks only commands it recognises as `gh … pr … merge` (`MERGE_RE`, `is_gh_pr_merge`). A merge is a server-side state change with many client spellings, and a text matcher can only enumerate the ones it knows. Every other spelling reaches GitHub with no gate check at all. The `Review Gate` status check itself is computed correctly; nothing on the server *requires* it before a merge.

## Affected surfaces

1. `gh api -X PUT repos/{o}/{r}/pulls/{n}/merge` (REST merge endpoint).
2. `gh api graphql` with the `mergePullRequest` (or `enablePullRequestAutoMerge`) mutation.
3. `curl` / any HTTP client against the same REST or GraphQL endpoints.
4. `git push origin <branch>:main` / `:staging` (direct push to the protected branch; also `git merge` + push).
5. git aliases, shell functions, `make` targets and repo scripts that wrap any of the above (the hook sees `git ship` or `./scripts/release.sh`, not the merge).
6. The GitHub web UI and other tools without the hook (outside every client guard by definition).

## Correct fix

Enforce on the server, where every surface above converges:

1. A repository ruleset on `main` and `staging` per gated repo: require the `Review Gate` status check (pinned to the GitHub Actions app as its source, so an API-POSTed check from another integration does not satisfy it), require conversation resolution, require a pull request (blocks direct push), and an empty or audited bypass list (no admin bypass by default, which also closes `--admin`).
2. `install-workflow.py` (or a sibling `install-ruleset.py`) applies and verifies the ruleset idempotently, so a repo cannot be "installed" without it; `review-gate` tests cover the ruleset JSON it sends.
3. A check that fails loudly when a gated repo lacks the ruleset (detector run in the workflow, or a scheduled audit), so drift is visible.
4. Keep `merge-guard.py` as fast local feedback only; document that it is not the enforcement boundary.

The ruleset change is shared, prod-visible repository state: it needs Matt's authorization before it is applied to any repo ("No ruleset change currently authorized" stands until then).

## Out of scope

Binding the fallback attestation to a reviewer identity (plan PR #113).
