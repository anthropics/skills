Run a committee code review comparing the current branch against a base branch using the reviewer-committee skill.

$ARGUMENTS should be a branch name (e.g. `main`, `develop`). If no branch is provided, ask the user which branch to compare against.

Invoke the `reviewer-committee` skill. Use mode `base` with the provided branch as the param. Run the committee review script and write COMMITTEE_REVIEW.md to the current working directory, then present a brief synthesis of consensus findings.
