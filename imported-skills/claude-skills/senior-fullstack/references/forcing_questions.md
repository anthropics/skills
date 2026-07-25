# Fullstack Engineer — Forcing-Question Library

**Discipline (Matt Pocock, derived from `engineering/grill-me`, MIT):** walk these one at a time. Do not skip ahead. Do not bundle. Answers must be written down. If the user cannot answer one, **that is your next investigation** — stop and surface the gap.

These seven questions are the Matt Pocock grill that gates every meaningful fullstack decision (stack pick, scale step, build-vs-buy, monolith-vs-microservices). Each has a recommended answer with canon citation and a **kill criterion** — the condition under which the plan fails the question and the work should stop until the gap is closed.

---

## Q1 — "What is your team size today, and what is the credible 12-month engineer headcount?"

**Recommended answer:** a single integer for today plus a single integer for month 12 (e.g., "4 engineers today, 9 in 12 months, hiring funded through Series A close"). Not a range. Not "growing."

**Why it's the first question:** every other architecture question collapses on this number. A team of 4 cannot operate a microservice fleet; a team of 80 cannot share a monorepo without tooling. Will Larson is explicit: *org structure is the binding constraint on architecture*, not the other way around.

**Kill criterion:** "we're starting microservices day one" with no 30+ engineer plan in 12 months — STOP. Re-plan as modular monolith. (Sam Newman's "MonolithFirst" rule, 2021.)

**Canon:** Will Larson, *An Elegant Puzzle* (2019); Sam Newman, *Building Microservices* 2e (2021); Melvin Conway, *How Do Committees Invent?* (1968).

---

## Q2 — "What is your target deployment cadence — per-PR, daily, weekly, or quarterly?"

**Recommended answer:** a specific cadence with named bottleneck (e.g., "daily; bottleneck is QA sign-off, fix that first"). The cadence forces every downstream choice: CI/CD spend, environment count, feature-flag investment, observability budget.

**Why it matters:** the *Accelerate* program's research (Forsgren/Humble/Kim, 2018) shows elite-cadence teams (per-PR or daily) outperform low-cadence teams on every business metric. But a quarterly-cadence team buying microservice infrastructure has bought the cost without the benefit.

**Kill criterion:** quarterly cadence with a microservice fleet, or weekly cadence with no feature-flag strategy → STOP. Fix the bottleneck before the architecture investment.

**Canon:** Forsgren, Humble & Kim, *Accelerate* (2018); DORA State of DevOps Reports (2014–2024).

---

## Q3 — "Customer-facing product, internal tool, or marketing site? Pick exactly one."

**Recommended answer:** one of the three, written down. "Sort of both" usually means the wrong stack is about to be chosen.

**Why it matters:** the cost shape is different for each. A marketing site on a Next.js + GraphQL + PostgreSQL stack is paying for capability it will never use. An internal tool built like a public product over-invests in a11y, perf, and theming the four-user audience does not need. A customer-facing product built like an internal tool ships a broken first impression.

**Kill criterion:** "marketing-site-but-also-the-product-someday" — STOP. Build the marketing site as static (Astro / Hugo / pure HTML). Build the product as a separate codebase. Joining them later is cheap; un-joining them is expensive.

**Canon:** Donald Reinertsen, *Principles of Product Development Flow* (2009), Principle E2 (queue length); Jeff Patton, *User Story Mapping* (2014), on product-vs-tool framing.

---

## Q4 — "What is your one-year p50 and p99 traffic forecast in RPS or daily-active users?"

**Recommended answer:** two numbers grounded in evidence — current baseline × growth multiplier with a named source ("today 12 RPS p50 / 45 RPS p99 from CloudWatch last 30 days; +3× per board commit; year-1 target 36 / 135 RPS"). Not "we want to scale."

**Why it matters:** premature scale planning is the #1 fullstack cost overrun. Backends sized for unverified hyperscale waste >50% of cloud spend (Vogels, 2016, "10 lessons"). Frontends sized for ten users with edge CDNs / SSR-on-everything are paying for performance their audience does not measure.

**Kill criterion:** p99 forecast > 100× current with no evidence basis — STOP. Build for 3× headroom; instrument the actual curve.

**Canon:** Martin Kleppmann, *Designing Data-Intensive Applications* (2017), ch. 1 on capacity planning; Werner Vogels, *10 Lessons from 10 Years of AWS* (2016).

---

## Q5 — "Are you hiring against your stack, or training your existing team into it?"

**Recommended answer:** one of "hiring against it" (with named recruiter pipeline + active reqs) or "training" (with named senior who has shipped this stack before). "Both" is usually neither.

**Why it matters:** exotic-stack picks (Elm, F#, Erlang, OCaml in 2026) ship the architecture but kill the recruiting curve. A Java-only team picking Rust because "it's safer" pays 6–12 months of velocity tax. A Next.js team picking Remix because "RSCs are confusing" pays the migration tax and the team has no senior.

**Kill criterion:** stack pick with no on-team senior AND no active reqs AND no recruiter pipeline — STOP. Pick the stack the team has shipped before.

**Canon:** Camille Fournier, *The Manager's Path* (2017), ch. 8 on hiring-velocity tax; Andy Grove, *High Output Management* (1983), on training as throughput investment.

---

## Q6 — "What is the year-one monthly cloud + SaaS budget ceiling?"

**Recommended answer:** a single dollar figure with sign-off (e.g., "$3.5K/mo through year 1, signed off by CFO"). Not "as low as possible." Not "we'll figure it out."

**Why it matters:** the default fullstack stack in 2026 (Vercel + Supabase + Sentry + LaunchDarkly + Datadog + Auth0 + Stripe + Linear) clears $4K/mo for any non-trivial product before a single customer pays. Without a ceiling, the team picks Big-Co defaults and ships before noticing the burn.

**Kill criterion:** no ceiling AND default-Vercel-and-five-add-ons stack — STOP. Either set the ceiling or accept the burn in writing (CFO sign-off in chat).

**Canon:** Tomasz Tunguz, *Cloud Cost Discipline* essays (2020–2024); Bessemer State of the Cloud (annual); Martin Casado & Sarah Wang, *The Cost of Cloud, a Trillion Dollar Paradox* (a16z, 2021).

---

## Q7 — "What does *done* look like? Name the verifiable success criteria — three measurable metrics, each with a target."

**Recommended answer:** three concrete metrics with thresholds (e.g., "p95 API latency < 200ms; first-contentful-paint < 1.8s on mobile-4G; uptime ≥ 99.9% over rolling 30 days"). Each metric must be machine-checkable, not "feels fast."

**Why it matters:** this is Karpathy Principle #4 (*Goal-Driven Execution*). Without verifiable success criteria, the implementation "looks right" and ships before anyone notices the regressions. Karpathy's 2026 critique: the LLM (and the human team) cannot loop toward a target if no target is named.

**Kill criterion:** any answer that does not contain a number — STOP. "Fast," "scalable," "robust," "production-ready," "great UX" are not success criteria.

**Canon:** Andrej Karpathy, *4 Coding Principles* (2026), Principle #4; Tom Gilb, *Competitive Engineering* (2005), on quantified-quality discipline.

---

## How to use this library in a conversation

1. **State the rule first** — tell the user you'll walk seven questions, one at a time, before recommending any stack or architecture.
2. **One question per turn.** Never bundle.
3. **Recommend the answer.** Always cite the canon source for *why* this is the right shape.
4. **Surface the kill criterion.** If the user's answer trips it, stop and surface that gap. Do not proceed.
5. **Track the answers.** Write them to a working file (e.g., `/tmp/fullstack-grill-<date>.md`) so the conversation can resume.
6. **After Q7, recommend the profile.** Match the seven answers against the profile JSON files in `../profiles/` and pick the closest fit. Surface ≥ 2 close matches with the tradeoff between them.
