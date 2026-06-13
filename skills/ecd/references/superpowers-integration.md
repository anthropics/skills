# Superpowers Complementary Integration `[v1.1]`

## Purpose

ECD and Superpowers solve different halves of the delivery problem. ECD excels at semantic freezing (pre/plan); Superpowers excels at engineering discipline (TDD, code review, branch management). Used together, they form a complete delivery pipeline.

## The Division of Labor

| Capability | ECD | Superpowers |
|-----------|-----|-------------|
| Semantic freezing (pre/plan) | **Primary** — Stages A-J freeze all product meaning before code touches the repo | N/A |
| TDD enforcement | Not present — verification commands specified but not TDD-gated | **Primary** — `test-driven-development` skill enforces red-green-refactor |
| Independent adversarial review | **Primary** — Subagent-based (D critique, G red-blue, H review, J compile) | Secondary — `requesting-code-review` skill (compliance-focused) |
| Branch isolation | N/A | **Primary** — `using-git-worktrees` skill |
| Execution planning | **Primary** — Frozen implementation units with contracts | **Primary** — `writing-plans` + `executing-plans` (2-5 min tasks) |
| Verification before completion | `achieve` phase (evidence-based closure) | `verification-before-completion` skill |
| Debugging | `references/diagnosis-and-observability.md` | `systematic-debugging` skill (4-phase method) |

## Recommended Workflow

### Option A: ECD Plan + Superpowers Execute

Best for medium-to-large features where both semantic fidelity and engineering quality matter.

```
1. ECD pre/plan (A through J)
   → Produce frozen bundle with 90-code-handoff.md
   → Semantic meaning is locked; no product decisions remain

2. Superpowers using-git-worktrees
   → Isolate workspace for the change

3. Superpowers test-driven-development
   → Write tests from ECD's function contracts and acceptance checks
   → See tests FAIL first

4. Executing from ECD handoff
   → Superpowers executing-plans consumes ECD's implementation units
   → ECD's code-playbook rules apply: no product meaning invention

5. Superpowers verification-before-completion
   → Verify all acceptance checks pass
   → Confirm first-open UX is not broken

6. ECD achieve
   → Evidence-based closure with archive/left_open verdict
```

### Option B: ECD Lite + Superpowers TDD

Best for small-to-medium features that need TDD but not full adversarial review.

```
1. ECD A-Lite → J-Lite (L1 or L2 tier)
   → Quick semantic freeze with compact handoff

2. Superpowers test-driven-development
   → TDD from the handoff's verification commands

3. Superpowers verification-before-completion
   → Verify before closing

4. ECD achieve-Lite
   → Quick evidence-based closure
```

### Option C: Superpowers-Only

Best for bugfixes, refactors, or tasks where the requirement is already unambiguous. Skip ECD entirely — Superpowers alone is sufficient.

## Handoff Format: ECD → Superpowers

When ECD's plan phase hands off to Superpowers' executing-plans:

| ECD Output | Maps to Superpowers Input |
|-----------|--------------------------|
| `90-code-handoff.md` → `implementation_units` | `writing-plans` task list |
| `90-code-handoff.md` → `function_contracts` | TDD test specifications |
| `90-code-handoff.md` → `verification_commands` | `verification-before-completion` checks |
| `90-code-handoff.md` → `acceptance_checks` | Final verification checklist |
| `05-constraint-ledger.md` → `frozen_constraints` | "Do not reinterpret" guardrails |

## Anti-Patterns

- ❌ **Do NOT** run ECD Full (L3) for a simple change just to "be thorough" — use ECD-Lite or Superpowers-only
- ❌ **Do NOT** skip ECD's pre for a greenfield project — Superpowers brainstorming is not equivalent to ECD's Stage A semantic excavation
- ❌ **Do NOT** use Superpowers brainstorming for semantic discovery on complex/ambiguous requirements — that is ECD's domain
- ❌ **Do NOT** use ECD as a substitute for TDD — add Superpowers' `test-driven-development` skill to the workflow
- ✅ **DO** let ECD own meaning, Superpowers own execution quality — the boundary is clean

## When to Use Each (Decision Matrix)

| Scenario | Recommendation |
|----------|---------------|
| New greenfield app, unclear requirements | ECD Full (L3) pre/plan → Superpowers execute |
| Adding auth to existing app | ECD Full (L3) pre/plan → Superpowers execute |
| New API endpoint, clear spec | ECD Standard (L2) → Superpowers TDD |
| Dark mode toggle | ECD Lite (L1) or Superpowers-only |
| Bug fix with known root cause | Superpowers-only (systematic-debugging + TDD) |
| Performance optimization ("make it fast") | ECD Full (L3) Stage A first — block until metrics exist |
| Refactoring (behavior-preserving) | Superpowers-only |
