# Intake Workflows

This file defines the clarification questions to ask for each learning-goal
type before generating or updating a `learning-plan.json`. Use judgment about
batching: ask only what's needed to scope the roadmap correctly, not an
exhaustive interview. If the user has already supplied an answer earlier in
the conversation, don't ask again.

Every workflow below should result in a populated `meta` object (see
`references/learning-plan.schema.json`) before module generation begins.
`meta.goal_type` should be set to whichever of `mastery`, `research`,
`career`, `exam-prep`, or `general` best matches.

For evaluation-method selection once scoping is done, see
`domain-evaluation-guide.md`. For resource handling, the rule is the same
everywhere: **never invent a book, course, paper, dataset, or tool**. If the
user hasn't specified one, add a `resources` entry with `"source": "needed"`
describing what's needed, and move on -- don't block the whole roadmap on it.

---

## 1. Broad-Goal Mastery

**Triggers:** "I want to learn X", "help me master Y", "I want a deep
understanding of Z" -- for any discipline, technical or not.

**Questions:**
1. **Scope.** If the stated domain is broad enough that a single roadmap
   could span years (e.g. "mathematics", "history", "philosophy"), don't
   guess at a sub-area. Either ask which sub-area/starting focus they want,
   or propose a short menu of plausible scopes ("e.g. analysis, algebra,
   discrete math -- or a survey across all three at an intro level?") and
   confirm before proceeding.
2. **Current level.** What's their existing background in this subject and
   adjacent subjects?
3. **Target outcome.** What does "mastery" mean to them here -- academic
   depth, practical application, professional competence, personal interest?
4. **Timeline / pace.** A deadline, a rough pace (hours/week), or "no fixed
   timeline."
5. **Resource posture.** Do they have specific books/courses/platforms they
   want to use, or should the plan flag resource gaps for them to fill?

**Output:** `meta.goal_type = "mastery"` (or `"general"` if it doesn't fit
cleanly), plus the standard module-generation pipeline in `SKILL.md`.

---

## 2. Research-Level Understanding

**Triggers:** "I want intensive/research-level knowledge of X", "I want to be
able to read papers in this field", "I want to study X deeply enough to do
original work."

**Questions:**
1. **Theoretical baseline.** What's their current mathematical/theoretical
   maturity relative to what the field assumes? (This drives how many
   prerequisite modules are needed before frontier material.)
2. **What "research-level" means to them.** Reading and critiquing papers?
   Reproducing results? Producing original research? These imply different
   capstones.
3. **Known landmarks.** Are there specific subfields, techniques, or papers
   they already know they want to cover? (If they name specific papers, those
   can be referenced directly -- the "never invent resources" rule applies to
   the skill suggesting unverified citations, not to using ones the user
   provides.)
4. **Timeline.** Research-level roadmaps are often open-ended; confirm
   whether there's a target horizon.

**Output:** `meta.goal_type = "research"`. Structure modules as
foundations -> advanced -> frontier, with explicit prerequisite gating
(don't let "advanced" modules become `available` until the maturity
prerequisites are `completed`). Include:
- A "paper-reading capability" module framed as a *skill* (how to read,
  annotate, and critique papers in this field), not a reading list.
- "Open problems / active directions" framed generally (e.g., "current open
  questions in X"), not as citations to specific unverified papers.
- Reproduction-study and literature-review entries in `evaluation`.
- A research-project module as the capstone (`is_milestone: true`).

---

## 3. Career or Role-Oriented Learning

**Triggers:** "I want to become an X", "what do I need to learn to get a job
as a Y."

**Questions:**
1. **Target role specifics.** Seniority level (entry/mid/senior), and any
   sector/company-type context that changes expectations.
2. **Current background.** Existing skills/experience relevant to the role.
3. **Timeline.** Is there a job-search deadline driving pace?

**Output:** `meta.goal_type = "career"`. Decompose the role into competency
areas (rather than a single linear subject), and:
- Write `industry_expectations` per module against the stated seniority level
  -- be concrete about what "job-ready" looks like, not generic.
- Favor role-realistic `evaluation` entries: portfolio projects, mock
  interviews, system design exercises, case studies, as appropriate to the
  role.

---

## 4. Interview / Exam / Deadline-Oriented Preparation

**Triggers:** "Prepare me for [exam]", "I have N weeks/months for X
interviews", "help me prepare for finals."

**Questions:**
1. **Exact deadline.** A date, not just "soon."
2. **Available study time.** Hours per week, realistically.
3. **Syllabus / topic list.** Ask the user to provide the official syllabus,
   past papers, or interview topic list. Do not assume or fabricate one --
   if they don't have it, ask them to find it before scoping module coverage,
   or scope based only on topics they explicitly name.
4. **Current level on those topics.** Can be folded into a gap analysis
   (Section 5) if the user has a sense of their own strengths/weaknesses.
5. **Assessment format.** Timed written exam, oral interview, take-home
   project, etc. -- this drives evaluation method choice.

**Output:** `meta.goal_type = "exam-prep"`, `meta.timeline` set to the
deadline. Prioritize and compress:
- High-yield/frequently-tested topics get `priority: high`.
- Lower-yield topics get `category: optional` or `skippable: true` so they're
  visibly de-scoped under time pressure, without deleting them.
- `evaluation` entries should be exam-realistic: timed problem sets, mock
  exams, past papers (only if the user supplies them).
- The Dashboard's Timeline view (view 3 in `assets/dashboard.template.md`,
  produced by `render_dashboard.py`) is the primary tracking view for this
  goal type.

---

## 5. Skill Gap Analysis

**Triggers:** "Here's what I already know", "analyze my current skills",
"what am I missing for X."

**Process:**
1. Ask the user to describe what they already know, at whatever granularity
   they're comfortable with (topics, courses completed, years of experience,
   etc.). If a target roadmap already exists or is being built, you can also
   walk through its module list and ask the user to self-rate each.
2. **Do not mark a module `completed` purely from self-report.** Self-reported
   knowledge is a strong signal for *de-prioritizing* a module, not for
   skipping validation entirely:
   - For modules the user claims strong familiarity with, set
     `skippable: true` and add a short note in `notes` recommending a
     lightweight validation check (using the module's own `evaluation`
     entries) before treating it as done.
   - For modules where the user reports partial/weak knowledge, keep
     `category: core` (or raise `priority`) and proceed normally.
3. Once the user confirms a validation check (or explicitly says to skip it),
   use `scripts/update_progress.py --complete <id>` to mark it completed and
   recompute downstream availability.

---

## 6. Learning Using Existing Resources

**Triggers:** "I already own these books/courses", "build the roadmap around
these resources."

**Process:**
1. Collect the full list of resources the user has (titles + type: book,
   course, paper, documentation, dataset, etc.).
2. While generating modules, map each resource to the module(s) it covers:
   add a `resources` entry with `"source": "user-provided"` and the resource
   title/notes (e.g., which chapters).
3. For any module where none of the supplied resources apply, add a
   `resources` entry with `"source": "needed"` and a description of what kind
   of resource would fill the gap (e.g., "a reference covering X") --
   **never** invent a specific title to fill it.
4. Surface the list of "needed" gaps to the user at the end so they know
   what to go find.

---

## 7. Updating an Existing Roadmap

**Triggers:** "I finished these modules", "update my progress", "add an
advanced module on X", "what's unblocked now?"

**Process:**
1. Locate the existing `learning-plan.json` (ask for its path if not already
   known from context).
2. Run `scripts/validate_plan.py` on it first -- catch any structural issues
   before editing.
3. For completions/status changes, run:
   `scripts/update_progress.py <plan.json> --complete id1,id2,...`
   (or `--in-progress`, `--reset` as appropriate). This recomputes
   `locked`/`available` status and progress percentages, and reports newly
   unblocked modules.
4. For adding new modules, edit `learning-plan.json` directly: append new
   module objects following the schema, set `prerequisites`/`parent_id` to
   wire them into the existing graph correctly, then re-run
   `scripts/validate_plan.py` to confirm no cycles or dangling references
   were introduced.
5. Re-render both artifacts:
   `scripts/render_plan.py <plan.json>` and
   `scripts/render_dashboard.py <plan.json>`.
6. Summarize for the user: what changed, what's newly available, and updated
   progress percentages.
