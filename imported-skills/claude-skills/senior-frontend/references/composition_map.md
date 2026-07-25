# Frontend Engineer — Composition Map

**Principle (Karpathy #2, Simplicity First):** do not reimplement scope that the POWERFUL-tier specialists already own. This skill is the *frontend orchestrator*; the specialists are the *implementers*.

This map is the routing table for the `cs-frontend-engineer` agent and the `/cs:frontend-review` command.

## Composition routing table

| User concern | Fork into | When to fork | Path |
|---|---|---|---|
| WCAG audit, contrast checks, screen-reader gaps | **a11y-audit** | After Q7 (WCAG target) is set | `../../../engineering-team/skills/a11y-audit/` |
| Bundle profiling, Lighthouse perf, runtime CPU/memory | **performance-profiler** | After Q2 (LCP target) is set | `../../../engineering/skills/performance-profiler/` |
| Cinematic / parallax / scroll-storytelling landing | **epic-design** | When `marketing-site` or `landing-page` profile applies | `../../../engineering-team/skills/epic-design/` |
| Pre-commit Karpathy review on changed files | **cs-karpathy-reviewer** | Before EVERY commit this skill produces | `../../../engineering/karpathy-coder/` |
| Pre-flight architecture grill | **cs-grill-master** | Before locking framework or rendering model | `../../../engineering/grill-me/` |
| Monorepo coordination (Turbo / Nx / pnpm) | **monorepo-navigator** | When frontend shares repo with backend / mobile / extension | `../../../engineering/skills/monorepo-navigator/` |
| Dependency vulnerability sweep | **dependency-auditor** | Before every major release | `../../../engineering/skills/dependency-auditor/` |
| Visual / accessibility regression in CI | **api-test-suite-builder** (extend for visual) + **playwright-pro** | After Q7 (WCAG target) is set | `../../../engineering-team/playwright-pro/` |
| Apple HIG / iOS / macOS / visionOS app review | **apple-hig-expert** | When the surface is Apple-platform-native | `../../../product-team/skills/apple-hig-expert/` |
| AEO (Answer Engine Optimization) — visibility in LLM search | **aeo** | After Q5 (SEO-dependent surface) is confirmed | `../../../marketing-skill/skills/aeo/` |
| SEO crawlability + meta + structured data | **seo-auditor** (if present) | After Q5 (SEO-dependent surface) | search `skills/` for the SEO auditor entry point |
| API contract from the consumer side | **api-design-reviewer** | When frontend defines/consumes a new API contract | `../../../engineering/skills/api-design-reviewer/` |

## Composition rules

1. **Fork via `context: fork`** — the agent forks its own context, runs the sub-skill, returns a ≤ 200-word digest.
2. **One sub-skill at a time.** Matt Pocock's depth-first rule. Finish the a11y branch before opening the perf branch.
3. **Honor sub-skill outputs as inputs.** `performance-profiler` produces a baseline; the next iteration of `senior-frontend` must respect that baseline.
4. **Never reimplement specialist scope.** If the user asks "what's my CLS?" do not hand-roll a check — fork into `performance-profiler`.
5. **Document the chain.** Every artifact lists the sub-skills invoked, in order.

## Anti-patterns

- ❌ Adding a third-party perf monitoring lib without checking it against the bundle budget from Q4.
- ❌ Implementing what `a11y-audit` would have caught (e.g., missing alt text, color contrast, focus traps).
- ❌ Skipping `cs-karpathy-reviewer` before committing — every commit must pass the diff-noise gate.
- ❌ Treating shipped UI as a final product without `playwright-pro` visual-regression baseline.

## When to escalate out of frontend

- **Brand voice / copy** → escalate to `marketing-skill/content-creator` + `cs-content-creator` agent.
- **Backend API design** → escalate to `cs-backend-engineer` + `api-design-reviewer`.
- **iOS/macOS-native UI** → escalate to `cs-apple-hig` (if present) or `product-team/skills/apple-hig-expert`.
- **Marketing-site infrastructure choice (Astro vs Next vs Hugo)** → escalate to `cs-fullstack-engineer` (marketing-site profile).

## References

- Karpathy 4 principles → `../../../engineering/karpathy-coder/skills/karpathy-coder/references/karpathy-principles.md`
- Matt Pocock grill discipline → `../../../engineering/grill-me/skills/grill-me/references/forcing_question_patterns.md`
- Path-B 11-file contract → `../../../business-operations/CLAUDE.md`
