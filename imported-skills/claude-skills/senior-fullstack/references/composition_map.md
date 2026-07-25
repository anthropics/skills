# Fullstack Engineer — Composition Map

**Principle (Karpathy #2, Simplicity First):** do not reimplement scope that the POWERFUL-tier engineering specialists already own. This skill is the *fullstack orchestrator*; the specialists are the *implementers*. Fork into them — do not duplicate them.

This map is the routing table for the `cs-fullstack-engineer` agent and the `/cs:fullstack-review` command.

## Composition routing table

| User concern | Fork into | When to fork | Path |
|---|---|---|---|
| API contract / REST + GraphQL design / breaking change risk | **api-design-reviewer** | After Q1–Q3 of the forcing-question library reveal API surface area | `../../../engineering/skills/api-design-reviewer/` |
| Database schema / migration safety / index strategy | **database-designer** + **migration-architect** | After Q4 (traffic forecast) — read/write ratio drives schema choice | `../../../engineering/skills/database-designer/`, `../../../engineering/skills/migration-architect/` |
| Bundle size, frontend perf, server response perf | **performance-profiler** | After Q7 success criteria include a latency/LCP target | `../../../engineering/skills/performance-profiler/` |
| Reliability target / SLO / error budget | **slo-architect** | After Q7 lists an uptime or p99 SLA | `../../../engineering/slo-architect/skills/slo-architect/` |
| CI/CD pipeline (multi-language fullstack) | **ci-cd-pipeline-builder** | After Q2 cadence is daily / per-PR | `../../../engineering/skills/ci-cd-pipeline-builder/` |
| Dependency vulnerability + license risk | **dependency-auditor** | Before every major release; before any production push | `../../../engineering/skills/dependency-auditor/` |
| Monorepo tooling (Turbo / Nx / pnpm workspaces) | **monorepo-navigator** | When team size ≥ 6 and the codebase houses multiple deployable surfaces | `../../../engineering/skills/monorepo-navigator/` |
| API test generation + contract tests | **api-test-suite-builder** | After API contract is stable | `../../../engineering/skills/api-test-suite-builder/` |
| Observability + golden signals + alert design | **observability-designer** | Concurrent with SLO design | `../../../engineering/skills/observability-designer/` |
| Architecture onboarding doc for a new team member | **codebase-onboarding** | When ≥ 3 engineers will touch the code in 90 days | `../../../engineering/skills/codebase-onboarding/` |
| Hardening: AuthZ/AuthN, threat model, sensitive-data handling | **senior-security** + **adversarial-reviewer** | Before public launch; before handling PII/PHI/PCI data | `../../../engineering-team/skills/senior-security/`, `../../../engineering-team/skills/adversarial-reviewer/` |
| Pre-commit code review (Karpathy 4 principles) | **cs-karpathy-reviewer** | Before EVERY commit this skill produces | `../../../engineering/karpathy-coder/` |
| Pre-flight grill on a draft architecture | **cs-grill-master** | Before locking the stack picks | `../../../engineering/grill-me/` |

## Composition rules

1. **Fork via `context: fork`** — the agent forks its own context, runs the sub-skill, returns a ≤ 200-word digest.
2. **One sub-skill at a time.** Matt Pocock's depth-first rule. Finish the API contract branch before opening the database branch.
3. **Honor sub-skill outputs as inputs.** If `database-designer` recommends a schema, the next call to `api-design-reviewer` must use that schema, not invent one.
4. **Never reimplement specialist scope.** If the user asks "what's the right index strategy?" do not answer with handcrafted advice — fork into `database-designer`.
5. **Document the chain.** Every artifact this skill produces must list the sub-skills it invoked, in order, with the digest paths.

## Anti-patterns

- ❌ Calling all sub-skills at the start "to be thorough." Burns context, produces noise.
- ❌ Skipping `cs-karpathy-reviewer` before committing. Every commit from this skill must pass the diff-noise gate.
- ❌ Implementing what `api-design-reviewer` would have caught (e.g., inconsistent REST verbs). Fork first; commit second.
- ❌ Treating this skill's recommendations as approvals. Architecture choices must be sign-off-able by a named engineer; this skill never auto-approves.

## When to escalate out of fullstack

- **Pure-engineering org-design questions** (team topologies, manager triggers) → escalate to `cs-vpe-advisor`.
- **Strategic build-vs-buy at the company level** → escalate to `cs-cto-advisor`.
- **AI/ML pipeline questions** → escalate to `senior-ml-engineer` / `senior-prompt-engineer`.
- **Data warehouse / lakehouse / dbt questions** → escalate to `senior-data-engineer`.
- **Pure security / threat model** → escalate to `cs-ciso-advisor` (strategic) or `senior-security` (tactical).

## References

- Karpathy 4 principles → `../../../engineering/karpathy-coder/skills/karpathy-coder/references/karpathy-principles.md`
- Matt Pocock grill discipline → `../../../engineering/grill-me/skills/grill-me/references/forcing_question_patterns.md`
- Path-B 11-file contract → `../../../business-operations/CLAUDE.md` (canonical statement)
