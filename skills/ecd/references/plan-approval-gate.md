# Plan Approval Gate

Use this reference during `ecd pre`.

## Purpose

Turn a raw user idea into an approved, frozen planning target before B-H converges the full bundle.

## Rules

- Audit the request before trusting it.
- Search local repo reality before asking the user to restate information that is already discoverable.
- Treat the user's description as low-reliability evidence: they may be unsure, contradictory, solution-biased, or unaware of their own hidden requirements.
- Do not optimize for fewer questions. Use A to aggressively gather meaning while user interaction is still allowed.
- Ask broad but concrete clarification questions across goals, non-goals, examples, anti-examples, workflows, priorities, tradeoffs, failure cases, data semantics, UI states, and acceptance expectations.
- Prefer grouped clarification passes that reveal contradictions and missing semantics over a single minimal follow-up.
- Stop asking only when the remaining unknowns are truly low-impact implementation details rather than latent product semantics.

## Approval Pack

Before entering B-H, present a short approval pack containing:

- `reframed_goal`: the product or change you now believe the user actually wants
- `retained_scope`: what will be delivered in this pass
- `excluded_scope`: what will not be delivered in this pass
- `critical_assumptions`: the assumptions that materially affect semantics
- `frozen_for_code`: the decisions `code` will treat as fixed truth

## Tiered Approval Packs `[v1.2]`

The approval pack varies by complexity tier. Present the pack that matches the tier determined by the complexity classifier.

**Every approval pack MUST begin with a classifier explanation line** `[v1.2]`:

```
[L2] 判定依据: 6文件 + 功能逻辑风险 + 需求明确
```

Format: `[Tier] 判定依据: Q1_result + Q2_result + Q3_result` where each Q result is a brief Chinese description:
- Q1: "≤3文件" / "4-10文件" / ">10文件"
- Q2: "UI样式风险" / "功能逻辑风险" / "数据/安全风险"
- Q3: "需求明确" / "部分待定" / "需求模糊→强制L3"

### Lite Approval Pack (L1)

For L1 tasks, present a compact pack before entering J-Lite:

- **Classifier line** (required, see above)
- `reframed_goal`: the change you now believe the user actually wants
- `retained_scope`: what will be delivered
- `excluded_scope`: what will NOT be delivered
- `acceptance_checks`: 3-5 concrete, verifiable checks
- `frozen_for_code`: decisions code will treat as fixed truth

**Rule:** Maximum 3 clarification questions before presenting this pack. If you need more, the task is likely L2 or L3.

### Standard Approval Pack (L2)

For L2 tasks, the Lite pack plus:

- **Classifier line** (required, see above)
- `critical_assumptions`: assumptions that materially affect semantics
- `key_non_goals`: what is explicitly out of scope
- `risk_register`: top 3 risks with mitigation notes

### Full Approval Pack (L3)

For L3 tasks:

- **Classifier line** (required, see above)
- Unchanged from v1.0 — the complete 5-field pack (reframed_goal, retained_scope, excluded_scope, critical_assumptions, frozen_for_code) with full semantic coverage. For L3, also include scenario_fragments and blocking_unknowns from Stage A full output.

## Exit Rule

Do not continue to `ecd plan` and B-H until the user has explicitly approved the approval pack.

If the user responds with changes, update the approval pack and ask for approval again.

After the user approves, do not keep turning B-H or J into a stage-by-stage interview. Converge later stages mainly in the background and return to the user only when a new high-impact ambiguity, contradiction, or blocker appears.

## Personal Project Progress Planner Heuristic

For a personal project-progress tool, make sure the approval pack freezes at least:

- what counts as a project, idea, plan item, or capture item
- whether the app is single-user only
- whether persistence is local-only or server-backed
- which time horizons matter, such as long-term, short-term, or spark ideas
- what the dashboard must show on first open
