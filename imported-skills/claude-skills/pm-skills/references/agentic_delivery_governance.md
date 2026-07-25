# Agentic Delivery Governance

The accountability layer behind `delivery_loop_gate.py`. When agents execute delivery
work, the failure mode is not bad output — it is **unowned output**: work no human is
accountable for, verified by nobody, closed by the optimism of the thing that did it.
The 2025–2026 vendors converged on the same governance shape; this file encodes it.

## The delegation model (why G1/G2 exist)

- **Linear's shipped design**: issues can be delegated to agents, but the **human stays
  primary assignee; the agent is a contributor**. Delegation transfers execution, never
  accountability. → Gate G1: every task names a human owner.
- **Atlassian Rovo (GA 2026)**: agents are assignable and @mentionable inside Jira, but
  "every action remains logged and auditable", and multi-step plans pause for human
  oversight at decision points. → Gate G2: agent-executed tasks name a human reviewer;
  hard rule: no un-reviewed `transitionJiraIssue` to Done, no permission changes inside a
  loop.

## Verification discipline (why G3/G4 exist)

- **Machine-checkable definition of done**: the reliable loop shape is plan → act →
  verify with a deterministic verifier → reflect. A criterion without a command or a
  threshold ("looks good", "improved") cannot gate anything. → G3: acceptance = a `cmd`,
  or a criterion containing a measurable number.
- **Never trust self-report**: the agent that did the work does not adjudicate the work.
  Evidence precedes status: `done` without recorded evidence is rejected (G4) — the same
  invariant as agent-harness's "a verify pass without --evidence is exit 6" and
  autoresearch-agent's locked evaluator ("never modify the gate you are judged by").

## Terminal-state honesty (why G5/G6 exist)

From the loop-library contract: loops end in a **named terminal state** — success, clean
no-op, blocked, approval-required, exhausted, stagnated. Two corollaries the gate
enforces:

- Close is refused while any task is neither done nor waived (G5); waivers are human
  decisions with recorded rationale.
- An exhausted budget (attempts or iterations) is an **escalation**, never a success
  report (G6). Budgets are first-class: max attempts per task, max loop iterations, and
  the stop fires mechanically, not when the agent feels finished.

## Design principles for PM loops

1. **Workflows before agents** (Anthropic): most PM automation is a routed workflow
   (classify → run tool → report). Reach for the autonomous loop only when the task needs
   fresh feedback each cycle — flow snapshots, retro follow-through, RAID hygiene.
2. **Evaluator-optimizer needs clear criteria**: the generator/critic loop pays off
   exactly when acceptance is machine-checkable — which is why the gate forces G3 before
   any loop starts.
3. **Context from structured interfaces, not prompt-stuffing**: the agent's Jira context
   comes through the MCP (Teamwork-Graph-style structured access), snapshotted to a file
   the loop can re-read — every iteration is executable by a fresh session.
4. **Agent-readiness is a data-hygiene property**: agents amplify the Jira they are given
   (DORA 2025's amplifier finding). Field completeness, acceptance criteria in
   descriptions, and honest statuses are prerequisites, not nice-to-haves.

## Sources

1. Linear, "Agents in Linear" / Linear for Agents — https://linear.app/agents and
   https://linear.app/docs/agents-in-linear
2. Atlassian Rovo — https://www.atlassian.com/software/rovo and Rovo agents docs
   https://support.atlassian.com/rovo/docs/agents/
3. Anthropic, "Building Effective Agents" (orchestrator-workers, evaluator-optimizer,
   simplicity-first) — https://www.anthropic.com/research/building-effective-agents
4. Forward Future, Loop Library (terminal-state taxonomy; "never report an error or
   exhausted budget as success") — vendored at `loop-library/SKILL.md`
5. DORA, *State of DevOps 2025* (AI as amplifier) — https://dora.dev/dora-report-2025/
6. This repo: `engineering/agent-harness` references/verification_discipline.md
   (reward-hacking failure mode; locked evaluators)
7. SiliconANGLE, "Atlassian opens Teamwork Graph, pushes Rovo agentic execution"
   (Team '26 coverage) — https://siliconangle.com/2026/05/06/
