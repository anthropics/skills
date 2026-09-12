---
name: skill-triage
description: Pick the right Claude Code skill for a task. Ranks installed skills, emits a routing plan, and falls back to web discovery if nothing matches. Use before non-trivial tasks (3+ steps, architectural decisions, or destructive operations).
---

# Skill Triage

Routing meta-skill. Decides how to approach a task. Prefers skills the user already has installed. When nothing matches, searches a short allow-list of curated registries (and, as a last resort, the open web with URL verification) to suggest skills the user could install. Never recommends an installed skill just because it exists.

## What this skill does

Given a task, produce a short, structured recommendation:

1. Restated task (one sentence)
2. Complexity tier (simple / medium / complex / high-risk)
3. Risk flags (destructive, secrets, prod, irreversible, mass edit)
4. Relevant installed skills (ranked, with one-line "why")
5. Skills to avoid (with reason — prevents misfires)
6. Recommended order, grouped by phase: **pre** (plan / brainstorm / research) → **impl** (build / fix) → **post** (review / test / docs / ship)
7. Suggested slash-command invocations
8. Verdict: **proceed directly** | **proceed with skill(s)** | **stop and ask**

When the answer is "no skill needed," collapse to a single line — do not pad the template with empty sections.

## When to invoke

**Always run before:**
- Any task with 3+ steps or cross-file work
- Any architectural decision
- Anything destructive (deletes, force-push, schema changes, migrations on prod, secret writes)
- Any task where multiple plausible skills exist (e.g., a `review` skill vs. a code-quality auditor vs. a security review)

**Skip for:**
- Trivial one-step edits ("rename this var", "add a console.log")
- Pure read/lookup ("what does X do", "find the config")
- The user is mid-flow inside another skill

**Heuristic:** if you can finish the task confidently in one tool call, skip. If you'd have to pick between approaches or workflows, run the triage.

**One-time-only per task.** Do not re-run on follow-up turns inside an existing skill flow — the routing is already decided.

## How to run it

### Step 1 — Read the task and project context (cheap)

Pull only what's already free or one shell call away:
- The user's task wording (verbatim — do not paraphrase before classifying)
- Project `CLAUDE.md` if loaded in context (already in system reminder)
- `git status` and `git log -5 --oneline` (one bash call each, parallel; skip if not a git repo)

Do **not** read source files, config, or other directories at this stage. Cheap context only.

### Step 2 — Classify complexity (4-tier rubric)

Treat complexity and risk as orthogonal. A task lands in the higher of the two tiers.

| Tier | Signals |
|---|---|
| **simple** | 1-2 steps, single file, no state change, no decisions |
| **medium** | 3-5 steps, single domain, reversible, no external side effects |
| **complex** | Multi-domain, architectural, cross-file refactor, new feature, ambiguous requirements |
| **high-risk** | Destructive (rm -rf, DROP, force-push, db migration on prod), secrets handling, package publish, mass edits >20 files, irreversible network calls, anything touching production |

A "simple" task that drops a prod table is **high-risk**.

### Step 3 — Scan installed skills

Run the bundled scanner. It reads SKILL.md frontmatter only (cheap), caches for 10 min, and emits one line per skill: `name|source|description`.

```bash
bash ~/.claude/skills/skill-triage/scripts/scan-skills.sh
```

Source is `personal`, `plugin:<name>`, or `project`. If a skill was just installed, pass `--refresh` to bust the cache:

```bash
bash ~/.claude/skills/skill-triage/scripts/scan-skills.sh --refresh
```

### Step 4 — Triage

From the scanner output:

1. **Filter** by keyword overlap with the task (substring match against name + description). Drop the rest.
2. **Rank** the remaining 0-10 candidates by fit. Heuristic: process skills (planning, debugging, brainstorming) first if the task hasn't been scoped; implementation skills next; post skills (review, test, docs, ship) if the task is "complete X and merge."
3. **Read full SKILL.md** for at most the top 1-3 candidates. Use the `Read` tool. Skip if the frontmatter description already gives you enough to decide.
4. **Resolve conflicts.** When several skills overlap (e.g., two reviewers, two designers), pick exactly one winner per role and list the rejected ones with a one-line reason. Do not chain redundant skills "for safety."

### Step 4b — Apply the skill budget (HARD CAP)

After triage, check your "Relevant skills" list against this budget by complexity tier:

| Tier | Max relevant skills |
|---|---|
| simple | 0 (use short-form) |
| medium | 1-2 |
| complex | 3-5 |
| high-risk | 1-2 (the safety wrap + at most one planner) |

**One skill per role.** Roles: scope/brainstorm, plan, design, implement, review, test, ship, debug. If the user has two planning skills, pick one and demote the others to **Avoid** with the reason "redundant with X." Same for two reviewers, two designers, two debuggers.

**Self-check before emitting.** Count "Relevant skills" entries.
- Over budget? Cut the weakest. Move it to Avoid with a one-line reason. Re-count.
- At or under budget? Proceed.

A router that lists 8 plausible skills is not routing — it is a directory dump. The user can read the directory themselves. The value is the cut.

### Step 4c — Discovery fallback (when nothing matches)

Trigger this step **only** when one of the following is true after Step 4b:

- The scanner returned zero skills (new Claude Code user, no skills installed).
- The scanner returned skills but none match the task by keyword + role fit.

Otherwise skip this step entirely.

**Privacy first.** Before any web call, scrub the task to safe keywords. Drop emails, names, IDs, file paths, URLs, hostnames, secrets, and any quoted user data. Send only generic terms (e.g., for "delete the user with email foo@bar.com from prod" send `database delete row`). The user's raw task must not leave the machine.

Search for skills the user could install. Use this allow-list **first**, in order:

1. `https://raw.githubusercontent.com/anthropics/skills/main/README.md` — official Anthropic skills repo
2. `https://raw.githubusercontent.com/travisvn/awesome-claude-skills/main/README.md` — community awesome list
3. `https://raw.githubusercontent.com/hesreallyhim/awesome-claude-code/main/README.md` — community awesome list

Use `WebFetch` on each. If a `main`-branch URL returns 404 or empty content, retry once with `master` in place of `main`. Extract candidate skills whose name + description overlap with the (scrubbed) task keywords. If the allow-list yields nothing useful, fall back to `WebSearch` with the (scrubbed) query:

```
claude code skill <safe keywords> site:github.com
```

For every candidate from either path, **verify** before suggesting:

- `WebFetch` `https://raw.githubusercontent.com/<owner>/<repo>/main/SKILL.md`. If 404, try `https://raw.githubusercontent.com/<owner>/<repo>/main/skills/<skill-name>/SKILL.md`, then the same two paths on the `master` branch.
- If all four 404, drop the candidate. Never invent a name.
- Reject any candidate whose name contains shell metacharacters (`spaces`, `;`, `|`, `&`, backticks, `$`, `(`, `)`).

Cap discovery output at **3** suggestions. One per role.

Emit using this template (instead of the regular routing plan):

```markdown
## Discovery suggestion

No installed skill matches this task. Verified candidates from the web:

- **<skill-name>** ([repo](<github-url>)) — <one-line description from the source>
  - Install:
    ```
    SKILL=<skill-name>
    DIR=$(mktemp -d) && git clone --depth 1 <repo-url> "$DIR" \
      && mkdir -p ~/.claude/skills \
      && cp -r "$DIR/skills/$SKILL" ~/.claude/skills/ \
      && rm -rf "$DIR"
    ```
  - Source: <anthropics/skills | travisvn/awesome-claude-skills | hesreallyhim/awesome-claude-code | web-search:<owner>/<repo>>
  - Note: third-party skill — review its SKILL.md and any bundled scripts before running.

**Verdict:** install one of the above and re-run skill-triage, or `proceed directly` without a skill.
```

If the upstream repo's directory layout differs from `skills/<name>/` (some community repos place `SKILL.md` at the root), say so in the suggestion and link the repo's README instead of emitting a possibly-wrong install command.

If discovery itself returns nothing usable, fall through to a plain `proceed directly` verdict — do not invent suggestions.

**Tool availability.** `WebFetch` and `WebSearch` may not exist in every Claude Code environment. Try them; on tool error, fall through to `proceed directly`. Do not retry, do not error-out.

### Step 5 — Risk gate

If the task is **high-risk**, the verdict is **stop and ask** — even if a skill perfectly matches. Use `AskUserQuestion` with concrete options (proceed / dry-run first / abort) before doing anything irreversible. Quote the destructive command verbatim in the question.

If the task is **complex** but reversible, the verdict is **proceed with skill(s)** — emit the recommendation and continue without asking.

If **simple** or **medium** with a clear single skill, **proceed with skill(s)**.

If **simple** with no skill that adds value, **proceed directly** (no skill).

### Step 6 — Emit the recommendation

Use this exact template. The "no skill needed" case uses the short form below; never emit the full template with empty sections.

```markdown
## Routing plan

**Task:** <one-sentence restatement>
**Complexity:** simple | medium | complex | high-risk
**Risk flags:** <none | destructive | secrets | prod | irreversible | mass-edit>

**Relevant skills:**
- `<skill-name>` (<source>) — <one-line why this fits>
- ...

**Avoid:**
- `<skill-name>` — <one-line why not (e.g., "scope mismatch", "post-impl only", "redundant with X")>

**Recommended order:**
1. **pre:** `/skill-a` — <purpose>
2. **impl:** `/skill-b` — <purpose>
3. **post:** `/skill-c` — <purpose>

**Verdict:** proceed directly | proceed with skill(s) | stop and ask
```

**Short form (no skill needed):**

```markdown
**Routing:** No skill needed — <one-line reason>. Proceeding directly.
```

### Step 7 — Gate (when applicable)

If verdict is **stop and ask**, immediately follow the recommendation with an `AskUserQuestion` call. Options should be concrete and mutually exclusive — never "proceed / abort" alone; include a middle path like "dry-run first" or "narrow scope to X."

If `AskUserQuestion` is not available in the current environment (some non-Claude-Code agents), ask in plain text and wait for a reply before doing anything irreversible.

If verdict is **proceed with skill(s)**, do **not** ask — just execute the first recommended skill.

If verdict is **proceed directly**, do not ask, do not invoke a skill.

## Design principles (read these — they explain the *why*)

**Conservative by default.** Most tasks need 0-1 skills, not 3. The triage exists to *prevent* skill thrash, not justify it. If you are recommending 4+ skills for a single task, you are wrong — re-read the task.

**Installed skills first, web second.** The default mode is to route among what the user already has. The web discovery fallback exists only because a brand-new install of skill-triage on a machine with no other skills would otherwise be useless. Discovery is the cold-start fix, not the main loop.

**Don't blow context.** The scanner returns ~300 skill descriptions in a few KB. Do not `Read` every SKILL.md — only the 1-3 finalists. Progressive disclosure means triage on metadata first.

**Pick winners, name losers.** Listing every plausible skill is unhelpful — the user already has them listed. The value is the *judgment*: this one, not those, because X. The "Avoid" section prevents future-you from reaching for the wrong tool 10 minutes later.

**Risk gates before skill matches.** A perfect skill for a destructive task still requires user confirmation. Triage does not bypass safety. Quote destructive commands verbatim — never paraphrase `rm -rf` as "delete some files."

**Phase ordering matters.** Calling a review skill before code is written wastes a turn. Calling a brainstorming skill after implementation is too late. The pre/impl/post grouping forces honest sequencing.

**Advisory, not authoritative.** Skill-triage does not enter plan mode. It does not block tool calls. It emits a recommendation and lets the caller (Claude or the user) decide. If the user overrides — "no, just do it directly" — drop the recommendation and comply.

## Examples

> **Note.** Skill names in these examples (`writing-plans`, `careful`, `frontend-design`, `review`, `ship`, `brainstorming`) are placeholders. Substitute with whatever the scanner emits on the user's machine. If a placeholder skill is not installed, drop it from the recommendation — do not pretend it exists.

### Example 1 — medium task, single skill

User: "add a new column `last_login` to the users table and surface it in the profile page"

```markdown
## Routing plan

**Task:** Add users.last_login column and display on profile page.
**Complexity:** medium
**Risk flags:** none (dev DB; migration is additive, reversible)

**Relevant skills:**
- `writing-plans` — multi-file change with schema + UI; benefits from explicit phase plan

**Avoid:**
- `ship` — premature; nothing built yet
- `security-review` — additive non-sensitive column, no auth surface change

**Recommended order:**
1. **pre:** `/writing-plans` — break into migration + server action + UI tasks
2. **impl:** direct edits, no skill
3. **post:** `/review` — diff review before commit

**Verdict:** proceed with skill(s)
```

### Example 2 — high-risk, stop and ask

User: "drop the events table, we're not using it"

```markdown
## Routing plan

**Task:** DROP TABLE events from database.
**Complexity:** high-risk
**Risk flags:** destructive, irreversible (no backup mentioned)

**Relevant skills:**
- `careful` — wraps destructive commands with a confirmation gate

**Avoid:**
- a generic plan-execute skill — overkill for one-line SQL; bypasses the safety conversation

**Recommended order:**
1. **pre:** verify backup exists; confirm zero readers/writers in code
2. **impl:** `/careful` then issue DROP

**Verdict:** stop and ask
```

Then immediately invoke `AskUserQuestion`: "Destructive: `DROP TABLE events;` is irreversible. Proceed?" with options: dry-run (count rows + grep references), proceed after confirming backup, abort.

### Example 3 — simple, no skill

User: "rename `getUser` to `fetchUser` in src/api/user.ts"

```markdown
**Routing:** No skill needed — single-file mechanical rename, fully reversible. Proceeding directly.
```

### Example 4 — complex, multi-skill chain

User: "I want to ship a new dashboard page that pulls from our analytics warehouse and renders charts"

```markdown
## Routing plan

**Task:** Build analytics dashboard page with warehouse-backed charts and ship it.
**Complexity:** complex
**Risk flags:** none (new surface, additive)

**Relevant skills:**
- `brainstorming` — scope is fuzzy ("a dashboard"); needs requirements pass first
- `frontend-design` — distinctive UI required, not boilerplate
- `review` — pre-merge diff review
- `ship` — final merge + deploy step

**Avoid:**
- a second design skill — overlaps with `frontend-design`; pick one to avoid contradictory style guidance
- an autonomous-fix QA skill on first pass — better as report-only initially

**Recommended order:**
1. **pre:** `/brainstorming` — pin down dashboard scope, charts, data shape
2. **pre:** `/frontend-design` — design the page
3. **impl:** direct build
4. **post:** `/review` then `/ship`

**Verdict:** proceed with skill(s)
```

## What NOT to do

- Do not recommend a skill-creator skill unless the user explicitly wants a new skill.
- Do not recommend more than one skill per role (one planner, one reviewer, etc.).
- Do not silently omit a strong candidate — list it under "Avoid" with a reason.
- Do not invent slash commands. Verify the skill exists in the scanner output (or, in discovery fallback, on a verified web URL) before suggesting `/<name>`.
- Do not run discovery fallback when the scanner already returned at least one matching skill. The fallback is for empty-result cases only.
- Do not invent or hallucinate skill names from `WebSearch` results. If the candidate URL 404s or its repo has no `SKILL.md`, drop it.
- Do not enter plan mode. Leave that to the caller's configuration.
- Do not paraphrase destructive commands. Quote them.
- Do not run on follow-up turns inside an existing skill flow — would duplicate routing.

## Bundled resources

- `scripts/scan-skills.sh` — frontmatter-only scanner across personal / plugin / project skill dirs. Cached 10 min per-UID under `${XDG_CACHE_HOME:-$HOME/.cache}/skill-triage/`. Pass `--refresh` to rescan.
- `examples/examples.json` — illustrative test prompts for iterating on this skill.

## Limitations

- The scanner uses an `awk` YAML parser. It handles `description:`, `description: |`, `description: >`, and the `|-` / `>-` chomp variants, plus quoted forms. Adversarial frontmatter may still misparse — restrict to what's between the leading `---` delimiters.
- Plugin discovery assumes the default `~/.claude/plugins/cache/<plugin>/` layout. Custom plugin install paths will not be picked up.
- The discovery fallback sends scrubbed task keywords to GitHub raw URLs and (as a last resort) a `WebSearch` query. Raw user-task text is never sent. See SECURITY.md.
- Linux + macOS supported. Windows untested.
