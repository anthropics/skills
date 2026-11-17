# Example: ask is too vague, output is questions instead

A worked example of the `scope-then-build` output when the request is genuinely under-specified.

**User asked:** "Make the app faster."

---

I can scope this, but I need three answers first:

1. **Faster where?** — initial page load, in-app navigation, a specific API call, or perceived responsiveness?
2. **What's "fast enough"?** — a specific target (e.g. p95 TTI under 2s), or just "noticeably better than now"?
3. **What can change?** — code only, or are infra changes (CDN, caching layer, DB indexes) in scope?

Once those are clear I'll produce the 5-step plan.

---

**Why this is the right response:**

Producing a speculative plan ("step 1: profile the app, step 2: look for slow queries...") wastes the next 20 minutes if it turns out the user only cares about a specific perceived-lag bug on the dashboard. The questions surface the disambiguation cheaply.

The three questions are **scoped**: each one is answerable in one sentence, none requires the user to write a spec. Don't ask 8 questions — pick the three that most change the plan.
