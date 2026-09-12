Run a committee code review on a specific git commit using the reviewer-committee skill.

$ARGUMENTS should be a commit SHA (full or short). If no SHA is provided, show recent commits with `git log --oneline -10` and ask the user which commit to review.

Invoke the `reviewer-committee` skill. Use mode `commit` with the provided SHA as the param. Run the committee review script and write COMMITTEE_REVIEW.md to the current working directory, then present a brief synthesis of consensus findings.
