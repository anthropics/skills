# Trigger evaluation regression tests

From `skills/skill-creator`, run:

```sh
python -m unittest discover -s scripts/tests -v
```

The suite uses the Python standard library, requires no Claude credentials,
and makes no model calls. It covers artifact isolation, field-scoped trigger
matching, later tool calls, failed batches, custom configuration directories,
and preservation of completed optimization iterations.

On Windows, one test launches a real `.cmd` shim with a Python child to verify
that timeout cleanup terminates the child as well as the wrapper. Run it in an
environment that permits `taskkill /T`; a sandbox that denies process-tree
termination cannot validate this behavior. That test is skipped on other OSes.

Evaluation errors, timeouts, and streams ending without a terminal result are
invalid measurements. `run_eval` raises instead of assigning a zero trigger
rate. `run_loop` propagates an initial failure and preserves completed
iterations if a later evaluation fails. Successful result JSON is unchanged.

These tests do not establish routing accuracy for a particular Claude Code
version. That requires a separate positive/negative live evaluation with the
CLI version and model recorded.
