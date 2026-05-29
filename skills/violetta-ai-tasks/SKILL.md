---
name: violetta-ai-tasks
description: Formulates and verifies work items using the VIOLETTA standard for AI-native tasks (Verifiable, Integrated, Observable, Living, Executable, Transferable, Trainable, Aware). Use for admin panels, BPM, B2B portals, internal tools (CRM, billing, approvals, integrations), agent task specs, ticket or Notion review, or when the user mentions VIOLETTA, AI-native tasks, or agent-ready work.
license: MIT
---

# VIOLETTA — AI-native task standard

**Mnemonic:** every task must be verifiable, integrated, observable, living, executable, transferable, trainable, and aware — **V I O L E T T A**.

**Methodology:** [Medium (EN)](https://medium.com/@antonkochenevskiy_23318/after-crud-we-need-violetta-a-new-standard-for-tasks-in-the-age-of-ai-agents-7b9570b8f9f8) · [vc.ru (RU)](https://vc.ru/ai/2858702-standart-violetta-dlya-zadach-v-epokhu-ai-agentov)

## Where this skill shines

Anywhere tasks go beyond simple CRUD:

- **Admin panels / back-office** — permissions, entities, bulk operations, audit → **Observable**, **Verifiable**
- **Business processes & approvals** — multi-step chains, escalations, context shifts → **Living**, **Transferable**
- **B2B portals & client dashboards** — integrations, SLA, contract context → **Integrated**, **Aware**
- **Internal systems** (CRM, billing, support, data pipelines) — handoffs between people and agents, incident learning → **Transferable**, **Trainable**, **Executable**

A task for an agent is a **living, autonomous unit of work**, not a static ticket. Without the properties below it is closer to a **note** than an AI-native task.

## Eight properties

| Letter | Property | Meaning |
|--------|----------|---------|
| **V** | Verifiable | Measurable success criterion; can be checked programmatically or via checklist |
| **I** | Integrated | Connected to the ecosystem. Straight-through processing (STP): the task runs end-to-end without manual steps. Data sources, APIs, tools, result format, and downstream actions are stated explicitly — the agent does not search for information, the task brings it |
| **O** | Observable | Real-time status + full decision history (audit trail) |
| **L** | Living | Updates when context changes, or the context is explicitly marked as stable |
| **E** | Executable | Agent can execute without clarifications; HITL only at declared points |
| **T** | Transferable | Handoff to another agent/person without losing history or artifacts |
| **T** | Trainable | After failure the cause and lesson are recorded; next run is smarter |
| **A** | Aware | The "why", constraints, prior attempts, and decisions live inside the task |

**Living** and **Trainable** fundamentally rely on AI capabilities by design.

## Checklist (V-I-O-L-E-T-T-A)

- [ ] **V** — Is it clear when to stop and what counts as success?
- [ ] **I** — Are systems, data, tools, and result format specified?
- [ ] **O** — Is progress visible, with a trail of actions and decisions?
- [ ] **L** — How does the task update when context changes (or is context explicitly stable)?
- [ ] **E** — Can it execute right now automatically (with declared HITL points)?
- [ ] **T** Transferable — Can another executor pick it up without a briefing?
- [ ] **T** Trainable — Is there something to record after failure?
- [ ] **A** — Will the agent understand without a series of clarifying questions?

**≥ 3 "no" answers** → refine the formulation or label it as a spike/note, not a production task for an agent.

## How the agent should respond (required structure)

1. **Formulation / review** — table or list: one line per VIOLETTA letter — "covered / gap".
2. **Reviewing someone else's task** — list gaps by property + suggest concrete fixes (criteria, links, artifacts).
3. **Decomposition** — each sub-task must be at least **E + V**; keep shared context in the parent's **A**.

## Task template (copy-paste)

```markdown
## Task (VIOLETTA)
**Aware — why / context:**
**Verifiable — definition of done:**
**Integrated — data, systems, format:**
**Observable — how progress and history are tracked:**
**Executable — trigger; HITL only if:**
**Living — what to do when priorities/data change:**
**Transferable — what to hand off to the next executor:**
**Trainable — what to record after failure:**
```

## Trigger phrases

- "Check this task against VIOLETTA"
- "Formulate a VIOLETTA-compliant ticket"
- "Review this ticket for agent readiness"
- "Is this task AI-native?"
- "Break down this goal using VIOLETTA"

## Examples: weak vs strong

- **Weak:** "Improve onboarding."
- **Stronger:** "Raise registration → first-action conversion from 23% to 35% in 30 days; funnel in analytics X; do not touch the payment flow."

- **Weak:** "Prepare the quarterly report."
- **Stronger:** "Pull metrics from [BI/table], use template Y, send to Z by [date]; if access is missing → record in task and stop (HITL)."

More examples (admin panels, B2B, pipelines): [examples.md](https://github.com/kochenevsky/violetta-ai-task-skill/blob/main/examples.md).

## Anti-patterns

- A single abstract verb with no criterion ("improve", "optimize", "fix").
- A link to "the docs" without path, version, or section.
- "Do it like the competitor" without an artifact or comparison metric.
- No scope boundary (what is **not** part of the task).

## Limitations

- VIOLETTA is about **task formulation quality**; it does not replace security reviews, access controls, or risk approvals.
- Destructive or bulk changes to production require explicit permission and scoped boundaries per repository policies.
