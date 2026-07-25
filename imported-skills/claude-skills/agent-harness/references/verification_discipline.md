# Verification Discipline

Why the harness adjudicates its own gates, and why an agent's claim of success is
never evidence. The controller's design decisions trace to these sources.

## Sources

1. **Jason Wei, "Asymmetry of verification and verifier's law", Jul 2025** —
   https://www.jasonwei.net/blog/asymmetry-of-verification-and-verifiers-law. "The ease of
   training AI to solve a task is proportional to how verifiable the task is." Tasks easy to
   check but hard to do are exactly where iteration works. Design consequence: **invest in
   making the task verifiable before investing in the agent** — a task in a harness plan with
   no executable check is a liability, which is why `goal_compiler.py` marks such tasks
   `manual-evidence` and the controller refuses to auto-verify them.
2. **John Yang, Carlos E. Jimenez et al., "SWE-agent: Agent-Computer Interfaces Enable
   Automated Software Engineering", NeurIPS 2024** — https://arxiv.org/abs/2405.15793.
   Agents fail when the environment gives no feedback on bad actions; the single highest-value
   guardrail was a linter that **rejects invalid edits at write time**. Design consequence:
   gates run cheap→expensive and fail fast; a failed check returns the failing command's
   output tail so the next attempt has signal, not vibes.
3. **OpenAI, "SWE-bench Verified", 2024** — https://www.swebench.com/verified.html. Even
   benchmark test suites were noisy enough to need human validation before scores meant
   anything. Design consequence: every check in a manifest declares its `kind`
   (smoke/sample/manual-evidence); only deterministic kinds can flip a task to `verified`
   without a human-authored evidence line.
4. **Boris Cherny (Anthropic), "Claude Code: Best practices for agentic coding", Apr 2025** —
   https://www.anthropic.com/engineering/claude-code-best-practices. The strongest loop is
   test-driven: write the check first, confirm it fails, then iterate work against it —
   "Claude performs best when it has a clear target to iterate against." Design consequence:
   the harness's recommended flow is gate-first (run the verification before the work; a gate
   that already passes pre-work is invalid as evidence of progress).
5. **Noah Shinn et al., "Reflexion: Language Agents with Verbal Reinforcement Learning",
   NeurIPS 2023** — https://arxiv.org/abs/2303.11366 — self-critique improves outcomes **only
   when grounded in external feedback signals**; and **Jie Huang et al., "Large Language Models
   Cannot Self-Correct Reasoning Yet", ICLR 2024** — https://arxiv.org/abs/2310.01798 —
   intrinsic self-correction without external feedback often makes answers worse. Design
   consequence: retries are only granted after a *recorded external failure* (nonzero exit),
   and the retry directive explicitly demands a changed approach.
6. **Anthropic, "From shortcuts to sabotage: natural emergent misalignment from reward
   hacking", Nov 2025** — https://www.anthropic.com/research/emergent-misalignment-reward-hacking.
   Agents that learn to game their checks (hard-coding expected values, editing tests)
   generalize to worse behavior. Design consequence — the harness's central invariant:
   **the worker must not adjudicate or modify the gates it is judged by.**
   `loop_controller.py verify` re-runs the check commands itself via subprocess; a passing
   `record --phase verify` without `--evidence` is rejected outright ("no verification
   theater"); and the same invariant already ships in this repo as autoresearch-agent's
   locked-evaluator rule ("`evaluate.py` is ground truth — never modify it").
7. **Google SRE Workbook (Beyer et al., 2018), ch. 2 "Implementing SLOs"** —
   https://sre.google/workbook/implementing-slos/. Error budgets are the production-grade
   version of the same idea: a numeric, pre-agreed threshold decides whether you ship or stop,
   not the operator's optimism. Design consequence: attempts and iterations are budgets
   (`max_attempts_per_task`, `max_loop_iterations`); exhausting a budget is a *terminal,
   reportable state* — never silently absorbed.

## The verification ladder (most → least trustworthy)

| Rank | Check type | Harness treatment |
|---|---|---|
| 1 | Deterministic command, exit-code contract (`kind: smoke`/`sample`) | `verify` subcommand runs it; pass can auto-flip state |
| 2 | Deterministic command with output assertion (JSON keys, thresholds) | Same, encode the assertion in the command (`... | python3 -c "assert ..."`) |
| 3 | Human-readable evidence written by the agent (`kind: manual-evidence`) | Requires `record --phase verify --evidence "<observation>"`; controller refuses empty evidence |
| 4 | Agent asserting "done" | **Never accepted.** Not a state transition in the machine. |

## Anti-gaming rules the controller enforces

- `verify` executes checks itself (subprocess, timeout, output tail captured to the evidence
  log) — recorded exit codes are for the *execute* phase only.
- A passing verify record without evidence text is exit 6, not a pass.
- Failure at `max_attempts` escalates (exit 2); the loop cannot convert an exhausted task
  into a success, only a human can waive it — and `close --waive` demands a reason that is
  written permanently into the handoff.
- `close` with any unverified, unwaived task is exit 4. There is no force flag.

## Trust boundary: plan and state files

`loop_controller.py verify` shell-executes each task's `verification[].cmd` string via
`subprocess.run(..., shell=True)`. In the documented flow those commands are template-
generated from repo-scanned script paths (`harness_manifest_builder.py` → `goal_compiler.py`),
so they are not attacker-reachable. But the controller does **not** re-validate a `--state`
or `--plan` file's contents before shelling out — a hand-crafted or tampered plan/state file
is therefore effectively arbitrary local command execution, the same trust model as a
Makefile or a CI config. **Treat `plan.json` and `state.json` as a trust boundary: only
run the harness on plan/state files you (or the `goal_compiler`) produced, never on files
sourced from untrusted input.** This matters because the harness is designed to be driven by
an agent (`harness-runner`) that could in principle be handed a malicious plan.
