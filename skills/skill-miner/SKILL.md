---
name: skill-miner
description: Mine past coding-agent session history (Claude Code, Codex CLI, opencode, pi, …) to discover and build the reusable skills a person or team should create. Use whenever the user wants to extract skills, conventions, or workflows from their session transcripts — "what skills should we create", "go through my past sessions", "turn my corrections into rules", "build a skill catalog" — or wants to run this across a whole team by collecting sanitized findings from each member's local history. Works for individuals and organizations alike.
---

# Skill Miner

Mine the user's past coding-agent sessions to discover which reusable **skills** they (or their team) should create — then help them build and prove the best one. Work in phases and check in between them; don't go dark.

## Phase 0 — Inventory what already exists

Before proposing anything, detect which harnesses are in use on this machine and list what's already encoded so you don't re-propose it (per-harness paths: `references/harnesses.md`):

- Skills & plugins: every skill directory the user's harnesses read — `~/.claude/skills/`, `~/.codex/skills/`, `~/.config/opencode/skills/`, `~/.pi/agent/skills/`, their project-level equivalents, and installed plugins
- Standing instructions: global + project `CLAUDE.md` / `AGENTS.md`, memory files

Treat overlap with any of these as a reason to **extend or fold in**, not to create a competing skill.

## Phase 1 — Index, don't read

Mine **every** harness that has history on this machine, not just the one currently running. Session stores (details and formats in `references/harnesses.md`):

- Claude Code: `~/.claude/projects/<project-dir>/*.jsonl` (top-level files are main sessions; subdirectories hold subagent transcripts)
- Codex CLI: `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl`
- opencode: `~/.local/share/opencode/storage/` (`session/`, `message/`, `part/`)
- pi: `~/.pi/agent/sessions/` (organized by working directory)

Sessions can be tens of MB — **never read whole files**.

1. Build a manifest: for each session — project, file size, message count, and the first real user message (skip tool results and `<`-prefixed system noise).
2. Write a small digest script that, given one session file, extracts: user turns, a tool-usage histogram, and the bash commands run. You will reuse it constantly.
3. Cluster the sessions by theme from the manifest (infra, data/analytics, incidents, docs, meta). If the corpus is large, fan out subagents — one per cluster — each armed with the digest script, and have them return structured findings.

## Phase 2 — Hunt the right signals

Two kinds of gold, in priority order:

**A. Conventions — "how we do things here."** Rules that apply to ANY person doing ANY task in this environment. Highest-value signals:

- **Mid-flow corrections** — every place the user corrected the AI: "no, we always…", "that should have been…", "you should have asked…", "why didn't you use…". Grep the user turns for these patterns. Each one is a rule the AI gets wrong by default, which makes it the highest-leverage thing to encode.
- **Hard requirements** stated more than once (commit signing, PR templates, approval gates, "never do X from the agent").
- **Repeated standard commands** — the same validate/regenerate/format/lint step run before every commit across sessions.
- **Topology** — which repo/system owns what; where a namespace, secret, workspace, or CI check actually gets created.
- **Traps** — generated files people hand-edit, prerequisites that fail silently, defaults that are wrong for this environment.

**B. Workflows — repeatable multi-step procedures.** The same shape of task appearing 3+ times:

- Sessions that **open with a pasted "handoff" / role / context doc** — that document is a skill screaming to exist.
- The same investigation, analysis, or setup sequence rebuilt from scratch each time.
- Knowledge that already lives in the user's notes/memory as prose, but the AI still re-derives the *executable procedure* every session. (Operationalizing notes they already maintain is the cheapest high-value skill.)

**⚠ The trap that ruins this exercise:** confusing what the user *happens to be working on* with how their environment *works*. First passes reliably surface project-storyline workflows that look impressive but help nobody else. Litmus-test every candidate: **"Would this matter to a different person doing a different task in this environment?"** If it's specific to one project's storyline, it's context — drop it. (Solo user? The test becomes: "will this matter in their next unrelated project?")

## Phase 3 — Verify every fact before encoding it

- Check each claim against the **live authoritative source at write time** — the platform API, the actual Makefile, the real directory layout — never memory, notes, or cached local state (e.g. a repo's true default branch comes from the hosting API, not a possibly-stale local `origin/HEAD`). Expect to catch real errors here; that's the point of the step.
- **Prefer live resolution over snapshots:** if a single command can answer a question live (default branch, current version, resource owner), the skill should encode *the command*, not the answer. Static lookup tables rot — one probably already rotted during your verification.
- Where a snapshot is unavoidable, date-stamp it and bundle a refresh script next to it.
- **Point at executable sources of truth** (existing scripts, make targets, internal tools) instead of restating what they do. Restatements drift; pointers don't. The skill is the index plus the rules the tools *can't* enforce.

## Phase 4 — Propose a prioritized catalog

Present a tiered catalog — **build-first / high-value / nice-to-have / fold-into-existing** — where every candidate has:

- one-liner · the recurring pain it removes · evidence (session + short quote) · recurrence count
- what it encodes · trigger phrases · bundled assets (scripts, templates, reference files)
- overlap with existing skills · value · effort (S/M/L)

Then run an **adversarial critique pass** with fresh eyes (a subagent works well): What did the synthesis miss? What's over-proposed — a one-off dressed up as a pattern? What's mis-tiered? Verify the critique's claims before accepting them, apply the corrections, and show the user the final catalog to pick from.

## Phase 5 — Build and prove the winner

1. **Draft** — a lean `SKILL.md` (aim under ~150 lines): a pushy trigger `description` (skills under-trigger by default — say *when* to use it, not just what it is), imperative rules with the *why* attached, bulk detail in `references/`, anything mechanical as a bundled script.
2. **Test** — run 3–4 realistic tasks twice, with and without the skill, and compare correctness, speed, and tokens. Include at least one "bait" case built from a real past correction. (Caveat: diligent eval agents may verify their way to the right answer anyway, so the skill's edge shows up as speed/cost; the real-world correctness edge is on fast paths where nobody stops to verify.)
3. **Fix what the eval exposes** — especially any fact the eval proves stale. An eval that finds a bug in the skill has paid for itself.
4. **Ship in stages** — install locally, dogfood for a week, then publish to the team. Schedule the publish reminder *now* so it actually happens.

Throughout: terse updates between phases; evidence over inference; and when the user's correction contradicts your finding, their correction wins — encode it.

---

# Collaborative mode — mining a whole team's history

Solo mining has a blind spot: one person's sessions only contain *their* corrections and *their* corner of the system. The teammate who set up CI has conventions in their history that appear in nobody else's. But **raw transcripts must never leave each person's machine** — they contain echoed secrets, tokens, customer data, and private context. So collaborate map-reduce style: each person mines locally, only a sanitized findings file travels, and one maintainer merges.

## Step 1 — Each contributor runs this locally

Send teammates this self-contained prompt (they don't need to know the method — it's encoded):

> Mine my coding-agent history for skill candidates and produce a **findings file** — do NOT build any skills.
>
> 1. Find every session store on this machine and mine them all — Claude Code: `~/.claude/projects/<project-dir>/*.jsonl` (top-level files only); Codex: `~/.codex/sessions/**/rollout-*.jsonl`; opencode: `~/.local/share/opencode/storage/`; pi: `~/.pi/agent/sessions/`. They're huge — never read whole files. Build a manifest (project, size, first user message per session), then write a digest script that extracts user turns, tool histograms, and bash commands from one session at a time.
> 2. Hunt, in priority order: (a) **my mid-flow corrections** to the AI ("no, we always…", "that should have been…") — grep the user turns; (b) hard requirements I stated more than once; (c) the same commands/sequences repeated across sessions; (d) which repo/system owns what; (e) sessions that open with a pasted context/handoff doc; (f) multi-step procedures I rebuilt 3+ times.
> 3. Litmus-test each candidate: would this matter to a *different person doing a different task* in our environment? Storyline-specific work is context, not a finding — drop it.
> 4. Write every finding to `skill-findings-<myname>-<date>.md` in this exact format:
>
> ```
> ## <imperative rule or workflow name>
> - kind: convention | workflow
> - domain: git/PR | deploy | infra | data | docs | other
> - evidence: <date + one-line PARAPHRASE — never verbatim transcript text>
> - recurrence: <N sessions>
> - ai_got_it_wrong_by_default: yes | no
> - scope_guess: org-wide | my-team | just-me
> ```
>
> 5. **Sanitize before anything leaves this machine:** evidence is paraphrase-only; no secrets, tokens, hostnames, customer data, or ticket contents. Run a secret scanner over the findings file. Then show it to me for review — I am the privacy gate, and nothing is shared until I've read every line.

Contributors submit the reviewed file via PR to a shared location (a `findings/` dir in the team's plugins repo works — PR review doubles as a second privacy check).

## Step 2 — One maintainer merges

Merge prompt, run over all submitted findings files:

> Merge these findings files into one candidate catalog. Rules:
>
> - **Cross-person corroboration is the strongest signal.** The same rule surfacing independently in 2+ people's histories outranks 5 recurrences from one person. Sum evidence, note who corroborated.
> - **Conflicts are gold, not noise.** If A's findings say "PRs target dev" and B's say "main," don't average — verify against the live source. Either someone's wrong (fix the finding) or both are right (it's per-team/per-repo variance → encode the *lookup or live-resolution command*, not one team's answer).
> - **Single-source findings get triaged, not dropped.** They're either specialist knowledge (often the most valuable material in the whole exercise — the thing only the person who built it knows; interview them, then encode it) or personal habit (mark `just-me`, exclude from the org skill).
> - Dedupe near-identical rules, keep the best-evidenced phrasing, and carry forward `ai_got_it_wrong_by_default` — those candidates lead the catalog.
>
> Then continue with Phases 3–5 of the solo mode above: verify every merged fact against live sources yourself (contributor evidence is testimony, not proof), build the tiered catalog, run the adversarial critique, and build the winner.

## What multiple people buy you

- **Corroboration** — independent recurrence separates real conventions from one person's habits.
- **Conflict detection** — divergent findings surface undocumented team differences (or quietly wrong practice) that no single history reveals.
- **Coverage** — the CI owner's, data engineer's, and on-call engineer's histories each contain a slice nobody else has. The union is the team's actual operating manual.
- **Cadence** — findings files are dated and incremental; re-run quarterly and merge only the deltas.
