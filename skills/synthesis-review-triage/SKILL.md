---
name: synthesis-review-triage
description: >
  PR queue prioritization methodology with weighted scoring across review gap,
  CI status, age, size, and labels. Includes author-response detection, queue
  classification, and prior-review gate for deciding full audit vs. delta-only
  vs. skip. Use when asked to: triage PRs, which PR should I review, review
  queue, prioritize reviews, PR backlog, review priority, what needs review,
  PR triage, review workload.
license: "CC0-1.0"
depends_on: []
metadata:
  author: "Emil Peñaló"
  version: "1.0.0"
  source_repo: "github.com/rajivpant/synthesis-skills"
  source_type: "public"
---

# Synthesis Review Triage

Review triage decides *which* PR to review next. It does not evaluate code — that is the job of synthesis-pr-review and synthesis-code-audit. Triage is a routing and scheduling methodology: classify the queue, score each item by urgency, and direct review effort where it has the most impact.

The most common failure in code review is not low-quality reviews — it is reviewing the wrong thing at the wrong time. A team that reviews the newest PR first while a merge-ready PR sits waiting for one more approval is wasting reviewer capacity. Triage prevents this.

---

## Where This Fits

| Skill | Scope | When to use |
|-------|-------|-------------|
| **review-triage** (this one) | PR queue prioritization | Before starting a review session — decide which PR to review next |
| **pr-review** | Delta review of a single change | Every PR, before peer approval or lead integration |
| **code-audit** | 10-dimension quality scan of a diff | During review, as systematic input alongside judgment-based evaluation |

Triage is upstream of everything in the review path. Run it before opening any PR.

---

## Queue Classification

Every open PR belongs to exactly one of three categories:

### 1. Reviewable

PRs that need your review action. This is the working queue — everything you score and prioritize comes from here.

### 2. Waiting on Author

PRs that are genuinely blocked on the author. Changes were requested or a blocker was raised, and the author has not responded. These are visible for awareness but not actionable by the reviewer.

### 3. Blocked

PRs held by external factors — labels like "blocked" or "do not merge," dependency on another PR, or infrastructure holds. Shown for awareness, not actionable.

---

## Exclusion Rules

Before scoring, remove PRs that should not be in your queue:

- **Self-authored** — you do not review your own PRs.
- **Drafts** — the author has not marked the PR ready for review.
- **Already approved by you** — your review work is done. This includes dismissed approvals that were positive in nature (contained "LGTM," "looks good," or similar signals with no blockers). A dismissed approval after a force-push does not mean the reviewer's assessment was wrong — it means the platform reset the review state.
- **Already reviewed by you with no new code commits** — you have seen this code. If the most recent commit on the PR predates your last review, there is nothing new to evaluate.

### Classifying Post-Review Commits

When a PR has new commits since your last review, classify them before deciding what to do:

- **Merge-only commits** (all new commits have 2+ parents, or messages begin with "Merge branch") — likely no code changes. Flag as "rebase/merge since your last review — verify manually." These rarely warrant a full re-review.
- **Code commits** (at least one new commit with 1 parent and a substantive message) — actual changes since your review. Flag as "new code commits since your last review — delta review needed." Boost priority.

---

## Author-Response Detection

This is the single most important classification decision in triage. Get it wrong and review-ready PRs hide in the "waiting on author" bucket.

**The insight:** A PR with changes requested + new commits pushed after the review is not blocked on the author. The author already responded. It is blocked on the *reviewer* to re-review.

**How to determine this:**

1. Find the timestamp of the most recent changes-requested review (or blocker comment).
2. Find the timestamp of the latest commit on the PR.
3. Compare:
   - **Latest commit is after the review** — the author likely addressed feedback. Move to the **Reviewable** queue with flag: "Author pushed changes after review — re-review needed." Boost priority.
   - **No new commits since the review** — genuinely **Waiting on Author**.

Apply the same logic to inline blocker comments (comments containing "blocker," "must fix before merge," "do not merge," or similar signals). If commits arrived after the blocker was posted, the author may have addressed it.

**Why this matters:** Teams that classify all "changes requested" PRs as "waiting on author" create invisible review debt. The author did their part. The reviewer is now the bottleneck but does not know it.

---

## Scoring Dimensions

Score each reviewable PR across these dimensions. The goal: maximize the impact of your review time.

### Review Gap — weight: highest

How far is the PR from its approval threshold?

| State | Urgency |
|-------|---------|
| 1 approval, CI passing, no conflicts | **Critical** — your review unblocks merge |
| 0 reviews | **High** — nobody has looked at it |
| Has review comments but 0 approvals | **High** — reviewed but not approved |
| Already meets approval threshold | **Low** — threshold met, your review is additive |

This is the most impactful dimension because it directly connects your review to an unblock event.

### CI Status — weight: medium

| Status | Effect |
|--------|--------|
| All passing | Boost — PR is actionable right now |
| Some failing | Neutral — may still be worth reviewing |
| All failing | Deprioritize — author needs to fix CI first |

### Age & Staleness — weight: medium

- Days since PR opened
- Days since last activity (commits, comments, reviews)
- Open > 7 days with no review = review debt — boost priority
- Updated in last 24h = actively being worked on — slight boost

Review debt compounds. A PR that has waited a week is more urgent than one opened an hour ago, all else being equal.

### Size — weight: low-medium

| Lines changed | Tag | Effect |
|---------------|-----|--------|
| < 50 | S | Quick review — slight boost (fast to unblock) |
| 50–200 | M | Standard |
| 200–500 | L | Significant — no automatic effect |
| > 500 | XL | Flag for possible split — not buried, but noted |

Smaller PRs get a slight boost because they are faster to unblock. XL PRs are flagged but not deprioritized — they may block the most downstream work.

### Labels — weight: override

Labels like "priority," "urgent," "critical," "hotfix," or "blocker" push the PR to the top regardless of other scores. These represent explicit team decisions about urgency.

### Updated Since Last Review

If a PR has reviews AND commits pushed after the most recent review, flag it: "New commits since last review — delta review needed." Boost priority. The author addressed feedback and is waiting for re-review.

---

## Tier Assignment

Group scored PRs into tiers:

| Tier | Criteria |
|------|----------|
| **Critical** | 1 approval + CI passing + no conflicts. Your review unblocks merge. |
| **High** | 0 reviews + CI passing. Or: updated since last review (author responded to feedback). |
| **Medium** | Reviewable but not urgent — CI mixed, very recently opened, or already has non-blocking reviews. |
| **Waiting on Author** | Changes requested with no author response since the blocking review. |

Review in tier order. Within a tier, use the scoring dimensions as tiebreakers.

---

## Prior-Review Gate

Before investing time in a PR you have already reviewed, run this decision gate:

### Step 1: Summarize Prior Review

State your prior review's outcome (approved, changes requested, commented), when it happened, and a one-line summary of what you covered.

### Step 2: Classify New Activity

Determine what changed since your last review:

- **Merge-only commits** — branch was rebased or merged from base. Likely no code changes.
- **Code commits** — actual new code since your review. Count them and note their scope.
- **New reviewer comments** — other reviewers may have covered ground you would duplicate.

### Step 3: Decide

| Situation | Action |
|-----------|--------|
| Merge-only commits, no code changes | **Skip** or quick manual verify |
| Small code commits addressing your feedback | **Delta review** — diff only new commits, check if feedback was addressed |
| Large code commits or significant new work | **Full review** — treat as a fresh evaluation |
| Other reviewers covered your concerns | **Skip** — your review adds no new value |

**Why this gate exists:** A rebase or merge-of-base produces "new commits since your last review" but often changes nothing in the PR's own code. Running a full review wastes time and produces identical findings. The prior-review gate prevents this wasted effort.

---

## Rules

- **Triage is routing, not evaluation.** Do not assess code quality during triage. That is what pr-review and code-audit are for.
- **The scoring is a framework, not a formula.** Adapt weights to your team's context. A team with a strict SLA on review turnaround might weight age higher. A team with frequent CI flakiness might weight CI status lower.
- **Author-response detection prevents misclassification.** Always check for post-review commits before labeling a PR as "waiting on author."
- **"Already reviewed" does not mean "already approved."** Distinguish carefully — a commented review with no verdict is not a completed review.
- **Respect explicit team signals.** Priority labels, blocker tags, and team conventions override the scoring framework.
