# Backend Engineer — Composition Map

**Principle (Karpathy #2, Simplicity First):** do not reimplement scope that the POWERFUL-tier specialists already own. This skill is the *backend orchestrator*; the specialists are the *implementers*.

This map is the routing table for the `cs-backend-engineer` agent and the `/cs:backend-review` command.

## Composition routing table

| User concern | Fork into | When to fork | Path |
|---|---|---|---|
| API contract / REST / GraphQL design / breaking-change risk | **api-design-reviewer** | After Q1–Q3 reveal API shape | `../../../engineering/skills/api-design-reviewer/` |
| Schema design / ERD / normalization / indexing | **database-designer** + **database-schema-designer** | After Q1 (read/write ratio) is known | `../../../engineering/skills/database-designer/`, `../../../engineering/skills/database-schema-designer/` |
| Zero-downtime schema migrations | **migration-architect** | Before any production schema change | `../../../engineering/skills/migration-architect/` |
| SLO + SLI + error-budget design | **slo-architect** | After Q7 (SLO) is set | `../../../engineering/slo-architect/skills/slo-architect/` |
| Observability / golden signals / alert design | **observability-designer** | Concurrent with SLO design | `../../../engineering/skills/observability-designer/` |
| MCP server build (tools-from-OpenAPI) | **mcp-server-builder** | When backend exposes tools to LLM agents | `../../../engineering/skills/mcp-server-builder/` |
| CI/CD pipeline for backend service | **ci-cd-pipeline-builder** | After Q2 (tenancy) and Q5 (pattern) are set | `../../../engineering/skills/ci-cd-pipeline-builder/` |
| Dependency vulnerability + license risk | **dependency-auditor** | Before every release | `../../../engineering/skills/dependency-auditor/` |
| API test suite + contract tests | **api-test-suite-builder** | After API contract is stable | `../../../engineering/skills/api-test-suite-builder/` |
| Security hardening / threat model / authZ | **senior-security** + **adversarial-reviewer** | Before public launch; before handling PII/PHI/PCI | `../../../engineering-team/skills/senior-security/`, `../../../engineering-team/skills/adversarial-reviewer/` |
| Cloud architecture (AWS / Azure / GCP) | **aws-solution-architect** / **azure-cloud-architect** / **gcp-cloud-architect** | When infrastructure choice is the bottleneck | `../../../engineering-team/skills/aws-solution-architect/` (and siblings) |
| Feature-flag investment + cleanup | **feature-flags-architect** | After Q5 (pattern) is set; before per-PR cadence | `../../../engineering/feature-flags-architect/` |
| Chaos engineering / failure-injection experiments | **chaos-engineering** | After SLO is in place + stable | `../../../engineering/chaos-engineering/` |
| Pre-commit Karpathy review | **cs-karpathy-reviewer** | Before EVERY commit | `../../../engineering/karpathy-coder/` |
| Pre-flight architecture grill | **cs-grill-master** | Before locking pattern or DB choice | `../../../engineering/grill-me/` |
| RA/QM compliance evidence (HIPAA, ISO 27001, SOC2) | **ra-qm-team** | After Q4 reveals regulated data | `../../../ra-qm-team/` |

## Composition rules

1. **Fork via `context: fork`** — the agent forks its own context, runs the sub-skill, returns a ≤ 200-word digest.
2. **One sub-skill at a time.** Matt Pocock's depth-first rule. Finish the DB branch before opening the API branch.
3. **Honor sub-skill outputs as inputs.** If `database-designer` recommends a schema, the next call to `api-design-reviewer` uses it.
4. **Never reimplement specialist scope.** If the user asks "what's my index strategy?" do not answer with handcrafted advice — fork into `database-designer`.
5. **SLO before scale.** If Q7 (SLO) is not set, don't burn cycles on caching / sharding / queue topology. Fork into `slo-architect` first.

## Anti-patterns

- ❌ Recommending Kafka before naming a second team that needs it (premature event-driven).
- ❌ Recommending microservices before Q5 (team-size justification) passes.
- ❌ Designing API contracts without forking into `api-design-reviewer` (consistency, breaking-change risk).
- ❌ Skipping `cs-karpathy-reviewer` before commit — every commit must pass the diff-noise gate.
- ❌ Auto-approving a production schema migration — every migration names the on-call + DBA approver.

## When to escalate out of backend

- **Frontend integration questions** → escalate to `cs-frontend-engineer`.
- **Org-design / capacity / hiring** → escalate to `cs-vpe-advisor` (engineering) or `cs-bizops-orchestrator` (cross-functional ops).
- **Strategic build-vs-buy at company level** → escalate to `cs-cto-advisor`.
- **AI/ML pipeline + model serving** → escalate to `senior-ml-engineer`.
- **Data warehouse / dbt / lakehouse** → escalate to `senior-data-engineer`.
- **Pure security threat model** → escalate to `cs-ciso-advisor` (strategic) or `senior-security` (tactical).

## References

- Karpathy 4 principles → `../../../engineering/karpathy-coder/skills/karpathy-coder/references/karpathy-principles.md`
- Matt Pocock grill discipline → `../../../engineering/grill-me/skills/grill-me/references/forcing_question_patterns.md`
- Path-B 11-file contract → `../../../business-operations/CLAUDE.md`
- SLO canon → `../../../engineering/slo-architect/skills/slo-architect/references/slo_principles.md`
