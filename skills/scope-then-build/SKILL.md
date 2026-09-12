---
name: scope-then-build
description: Turn a vague feature ask into a concrete 5-step plan before writing any code. Use whenever the user says "build X", "add a feature", "fix something" without a clear spec — especially when the task spans more than one file, or when interpretation is ambiguous. Outputs a scope document, not code.
license: Apache-2.0
---

# Scope-then-build

Stop diving into code when the ask is ambiguous. Produce a focused 5-step plan first, get alignment, then build.

## When to use this skill

Activate this skill when **any** of the following are true:

- The user's request is one sentence and would touch more than one file
- The request includes hedging words ("maybe", "could you", "see if you can")
- Two engineers reading the same request would code two different things
- The task description doesn't name a specific file/function/line

Do **not** use this skill when:

- The user has already given a precise spec (a function signature, a failing test, a specific file:line edit)
- The task is purely conversational (explaining something, answering a question)
- The user explicitly says "just do it" or "skip the plan"

## What this skill produces

Exactly five sections, in this order, with these headings:

```
1. What we're actually building
2. Files we'll touch
3. The order of work
4. What we're explicitly NOT doing
5. First thing to build
```

Each section has a specific job. Don't merge them, don't reorder them, don't skip them.

### 1. What we're actually building

One sentence. Concrete enough that two engineers reading it would interpret it the same way. If you can't write this sentence yet because the ask is genuinely ambiguous, stop and ask the clarifying question instead of inventing detail.

Good: *"Add a per-account API rate limit (10 req/sec, sliding window) enforced at the API gateway, returning 429 with a Retry-After header on exceed."*

Bad: *"Improve rate limiting."* — too vague to plan from.

### 2. Files we'll touch

Bulleted list, each line: path + one-sentence reason. **Do not invent paths.** Use Glob/Grep tools first to confirm files actually exist; for new files, mark them as "new" so the reader can flag mis-placements.

Example:
```
- src/middleware/rate-limit.ts (new) — sliding-window limiter middleware
- src/server.ts — wire the middleware into the gateway stack
- src/types/api.ts — add RateLimitConfig type
- tests/middleware/rate-limit.test.ts (new) — unit + concurrency test
```

A 10-file list usually means the scope is too big; either decompose into multiple plans, or push back to the user.

### 3. The order of work

3-5 steps, each independently testable. The point of ordering is so that each step can land alone without leaving the codebase in a broken state.

```
Step 1: Define RateLimitConfig type and the limiter interface (no implementation).
Step 2: Implement in-memory sliding-window limiter; unit-test it in isolation.
Step 3: Wire it as middleware in server.ts; add an integration test.
Step 4: Add the Retry-After header and the 429 response shape; verify in test.
Step 5: Add CHANGELOG entry and config example to README.
```

If steps depend on each other in a non-linear way, that's a sign the design needs revision before any code is written.

### 4. What we're explicitly NOT doing

The single most important section, and the most often skipped. List the adjacent things that fall outside the scope. Naming them prevents drift later and makes review easier.

```
- Not adding per-endpoint rate limits (account-wide only)
- Not adding distributed-cache backing (single-process limiter; revisit if we scale)
- Not changing auth, billing, or any other middleware
- Not modifying the existing 429 handler in the SDK
```

When you finish coding, re-read this section: anything you accidentally touched goes into the PR description as "scope expansion (here's why)".

### 5. First thing to build

Pick the smallest piece from Step 3 that can land in a PR alone and unblock the rest. Usually this is a type/interface, a failing test, or a stub. Building the riskiest piece first surfaces the wrong-design problem before you've written the rest.

```
First PR: just the RateLimitConfig type + the limiter interface + a no-op
implementation. Lets a downstream PR pick up the middleware wiring.
```

## Hard rules

1. **Do not write code in the scoping response.** This is a planning step. The next turn can write code.
2. **Do not invent file paths.** Confirm with Glob/Grep before listing. Mark new files as `(new)`.
3. **If the ask is genuinely too vague to scope** (no clear user/output/success criterion), respond instead with the 3 specific questions you'd need answered. Then stop. Don't half-scope on guesses.
4. **Bias towards smaller scope.** If you can't fit the plan in the 5 sections without each becoming a wall of text, the task is too big — decompose first.

## Anti-patterns

- ❌ Producing a "plan" that's just a restatement of the user's ask in five sub-bullets.
- ❌ Listing 15 files. Either the scope is too big or the listing is speculative.
- ❌ Step 1 = "set up", Step 2 = "implement", Step 3 = "test". Generic phases, not concrete steps.
- ❌ Empty "NOT doing" section. There's always adjacent scope; name it.
- ❌ Producing the plan and then immediately coding it. Stop at the plan; let the user accept or modify it.

## Examples

### Example A — vague ask, well-scoped

**User:** "Can you add team invites to the dashboard?"

**Skill output:**

```markdown
1. What we're actually building
   Email-based invite flow for an Account owner to invite teammates, with role-on-invite (Admin / Member), accepted via a one-time link that lands them in the same Account on signup.

2. Files we'll touch
   - prisma/schema.prisma — add Invite model (id, email, role, account_id, expires_at, accepted_at)
   - src/lib/invites.ts (new) — create / accept / expire helpers
   - src/api/invites/route.ts (new) — POST /api/invites (create), GET /api/invites/[token] (accept)
   - src/components/InviteTeammateForm.tsx (new) — form UI
   - src/email/templates/invite.tsx (new) — invite email body
   - tests/lib/invites.test.ts (new)

3. The order of work
   Step 1: Schema + migration for Invite model. No code paths use it yet.
   Step 2: Lib helpers + tests; pure functions, no HTTP.
   Step 3: POST endpoint + email send via existing mail client.
   Step 4: Accept endpoint + signup flow integration (gate the redirect on accept).
   Step 5: Form UI + the page that lists pending invites for an Account.

4. What we're explicitly NOT doing
   - Not adding SCIM / SSO provisioning (separate effort, blocked on enterprise plan)
   - Not implementing invite revoke yet (delete from DB is the v1 escape hatch)
   - Not enforcing invite-count limits per plan (left for billing PR)
   - Not migrating existing teammates added by other means

5. First thing to build
   Step 1: the Invite model + migration. Lands cleanly with no behavioral changes,
   unblocks every other step.
```

### Example B — ask is too vague, output is questions instead

**User:** "Make the app faster."

**Skill output:**

```markdown
I can scope this, but I need three answers first:

1. Faster where — initial page load, in-app navigation, a specific API call, or perceived responsiveness?
2. What's "fast enough" — a specific target (e.g. p95 TTI under 2s), or just "noticeably better than now"?
3. What can change — code only, or are infra changes (CDN, caching layer, DB indexes) in scope?

Once those are clear I'll produce the 5-step plan.
```

## Output format expectations

- Headings exactly as shown (numbered, bold not required).
- Sections kept tight — 80-120 words per section is the sweet spot. If you need more, decompose the task into two plans.
- No code blocks of actual implementation. Type signatures or one-line pseudocode are OK to convey shape.
- Finish with: "Ready to proceed with step (5) or want to adjust scope?"

---

Skill author: [nvwalj](https://github.com/nvwalj). Apache-2.0 — modify and ship freely.
