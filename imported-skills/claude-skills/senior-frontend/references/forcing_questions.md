# Frontend Engineer — Forcing-Question Library

**Discipline (Matt Pocock, derived from `engineering/grill-me`, MIT):** walk these one at a time. Do not skip ahead. Do not bundle. Answers must be written down. If the user cannot answer one, **that is your next investigation** — stop and surface the gap.

These seven questions gate every meaningful frontend decision: framework pick, rendering model, bundle budget, design-system investment, a11y target. Each has a recommended answer with canon citation and a **kill criterion**.

---

## Q1 — "Primary user device + network condition: desktop-fiber, mobile-4G, low-end Android, or corporate-network?"

**Recommended answer:** one named segment with evidence (analytics breakdown, target market, deployment context). Not "all of them" — every frontend optimizes for one and tolerates the others.

**Why it's the first question:** every rendering / bundling / image-pipeline decision changes shape based on the network floor. A mobile-4G product CANNOT ship a 500KB JS bundle; a corporate-internal tool on fiber CAN. Optimizing for the wrong target is the #1 frontend cost overrun.

**Kill criterion:** "all users equally" — STOP. Pull analytics or target-market data. The frontend tax for an unknown floor is paid by every user.

**Canon:** Web Almanac (HTTP Archive, 2025) — device + network distribution; Addy Osmani, *Web Performance for the Modern Web* (2024); Tim Kadlec, *High Performance Images* (2016).

---

## Q2 — "What is your LCP target on the primary device? Pick a number in milliseconds."

**Recommended answer:** a single number (e.g., "LCP < 2.0s on mobile-4G p75"). Bonus for naming the p75 / p95 split.

**Why it matters:** Core Web Vitals are a Google ranking signal *and* a measured business metric (every 100ms of LCP improvement = ~1% conversion lift per Akamai 2017 and reaffirmed by Chrome UX Report 2024). "Fast" is not a target. The number gates the entire performance-investment conversation.

**Kill criterion:** "as fast as possible" — STOP. Pick a number. Without a target there's no way to know when to stop optimizing.

**Canon:** Chrome UX Report (CrUX) public dataset; Akamai *Online Retail Performance* (2017); Google *Web Vitals* spec (web.dev/vitals, 2020–2024).

**Related targets to set in the same turn:** INP < 200ms; CLS < 0.1. If the user has not heard of INP, walk them through the 2024 migration from FID → INP (Google, March 2024).

---

## Q3 — "Server Components (RSC), classic SPA, server-rendered (SSR), or static (SSG)? Pick and defend."

**Recommended answer:** one of the four with explicit rationale tied to Q1 (network) and Q2 (LCP). Defaults: marketing → SSG; SEO-dependent + dynamic → SSR or RSC; auth-walled app → SPA; content-heavy with personalization → RSC.

**Why it matters:** the rendering choice cascades into every other decision (data fetching, state management, hydration cost, server cost). Picking it implicitly (= "whatever the framework default is") locks in costs the team won't notice until production traffic shows up.

**Kill criterion:** "RSC because it's newest" with no LCP measurement on a comparable SSR baseline — STOP. RSC is not faster by default; it's faster *for some workloads* and slower for others. Measure.

**Canon:** Dan Abramov, *React Server Components* spec (Vercel, 2023); Ryan Florence, *Remix data-loading patterns* (2022–2024); Astro *Islands Architecture* (Eisenberg, 2021); Rich Harris, *Frameworks Without Hydration* (Svelte 5, 2024).

---

## Q4 — "What is the JS bundle budget per route in KB (gzipped)?"

**Recommended answer:** a per-route number (e.g., "< 80KB gzip for landing, < 150KB gzip for app routes, hard cap at 200KB"). Bonus: split between framework + app + third-party.

**Why it matters:** the bundle budget is the only thing that holds the team accountable. Without a number, every new feature adds 5–20KB; in 12 months the app is 800KB and Q2's LCP target is impossible. Tim Kadlec's *Performance Budgets* (2013) framing — set the ceiling, fail the build when it's crossed.

**Kill criterion:** no per-route budget set in CI — STOP. Add `bundlewatch` or `size-limit` to CI with a failing gate before shipping the next feature.

**Canon:** Tim Kadlec, *Performance Budgets* (2013); Patrick Stox, *JavaScript and SEO* (Ahrefs, 2023); Alex Russell, *The Performance Inequality Gap* (2021–2024).

---

## Q5 — "Is the surface SEO-dependent or auth-walled?"

**Recommended answer:** one of the two, written down. "Both" means split the surface — public marketing pages go static / SSR; auth-walled app goes SPA or SSR-with-no-SEO-investment.

**Why it matters:** an SEO-dependent surface MUST render content in HTML (not just JS) and MUST optimize for Core Web Vitals (ranking signal). An auth-walled surface CAN ship a heavier JS bundle (no SEO cost) and CAN defer SSR. Picking the wrong rendering for the wrong surface is a common pre-Series-A waste.

**Kill criterion:** SEO-dependent + SPA-only rendering — STOP. Switch to SSR/SSG/RSC, or accept the SEO penalty in writing (signed by marketing-lead).

**Canon:** Google *Search Quality Rater Guidelines* (2024); Patrick Stox, *JS-rendered pages and crawl budget* (Ahrefs, 2023); John Mueller (Google) on JS-rendering best practices (2020–2024 SearchOff Hours).

---

## Q6 — "Where does your design system live: Figma + tokens, ad-hoc Tailwind, or a headless UI library?"

**Recommended answer:** one of the three with a named owner. Bonus: name the token export path (e.g., `tokens.json` synced via Style Dictionary).

**Why it matters:** ad-hoc styling at team size > 3 produces a fork-bomb (5 button variants, 9 modal stylings, 17 spacing values). A design system isn't a luxury — it's the only way to keep the visual language consistent past 3 engineers. But a custom design system at team size ≤ 3 is a tar pit; use shadcn/ui + Tailwind tokens instead.

**Kill criterion:** team size ≥ 4 with no design-system source of truth — STOP. Pick: Figma + Style Dictionary, or shadcn/ui + Tailwind, or a headless library (Radix, Ark, React Aria). No fourth option.

**Canon:** Brad Frost, *Atomic Design* (2016); Nathan Curtis, *Design Systems Handbook* (InVision, 2017); Vitaly Friedman, *Design Systems by Smashing* (2020–2024); shadcn/ui project (2023–2024) on copy-paste components vs. library lock-in.

---

## Q7 — "WCAG target — AA, AAA, or best-effort? And who is the accessibility owner?"

**Recommended answer:** one of WCAG 2.2 AA (the legal default in EU/AU/CA/many US states), 2.2 AAA (rare; public-sector or accessibility-first product), or best-effort (auth-walled internal-only). PLUS a named owner.

**Why it matters:** a11y is a regulatory baseline in 2026 (European Accessibility Act enforcement began 2025; US ADA Title III litigation surged 2018–2024). "We'll fix it later" is the most expensive a11y strategy — retrofitting costs 5–10× building it in. AND without a named owner, no one is accountable.

**Kill criterion:** customer-facing surface + no named a11y owner — STOP. Assign one before scaffolding. Run `engineering-team/skills/a11y-audit` as part of CI.

**Canon:** W3C WCAG 2.2 (2023); Marcy Sutton, *Accessibility in JavaScript Applications* (2017+); Adrian Roselli's blog on a11y testing (a-roselli.com, 2015–2024); European Accessibility Act (EU 2019/882, enforced 2025).

---

## How to use this library in a conversation

1. **State the rule first** — tell the user you'll walk seven questions, one at a time, before recommending any framework or rendering model.
2. **One question per turn.** Never bundle.
3. **Recommend the answer.** Always cite the canon source for *why* this is the right shape.
4. **Surface the kill criterion.** If the user's answer trips it, stop and surface that gap. Do not proceed.
5. **Track the answers.** Write them to a working file (e.g., `/tmp/frontend-grill-<date>.md`).
6. **After Q7, recommend the profile.** Match the seven answers against the profile JSON files in `../profiles/` and pick the closest fit.
