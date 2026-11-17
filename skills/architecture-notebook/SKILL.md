---
name: architecture-notebook
description: >
  Maintains a living, brief text file (architecture-notes.txt) inside any coding
  project that tracks system architecture, pipelines/data flow, and security
  aspects, written at an AI-engineer level (naming design patterns, tradeoffs, and
  "why", not just "what"). Use this skill whenever the user is writing, editing,
  reviewing, or discussing code in a project, even if they didn't explicitly ask
  for documentation. Create the notes file the first time a coding project is
  touched if it doesn't exist yet, and update the relevant section any time a
  meaningful change happens - a new component or service, a changed data flow or
  pipeline step, a new dependency, or anything touching auth, secrets, or access
  control. Also use this skill whenever the user asks to "recap the architecture,"
  "what have I built so far," "summarize this project for an interview," or
  similar. Do not trigger for trivial edits like variable renames, formatting,
  typo fixes, or comment changes.
---

# Architecture Notebook

A skill for keeping a short, always-current engineering notes file alongside code —
so the user (an AI engineer building solo projects) can recall design decisions,
patterns, and security posture later without re-reading the whole codebase, and can
turn it into interview-ready talking points on demand.

## Core behavior

1. **On first touching a coding project in a session**, check the project root for
   `architecture-notes.txt`. If it doesn't exist, create it using the template below.
2. **After any meaningful code change**, update the relevant section — don't wait to
   be asked. "Meaningful" means:
   - A new component, module, service, or route
   - A changed or new data/pipeline flow (e.g., new API call chain, new job, new
     queue, new ETL step)
   - A new external dependency or integration
   - Anything touching authentication, authorization, secrets, input validation,
     or data exposure
   - A deliberate design-pattern choice (e.g., switching to a repository pattern,
     adding a factory, introducing a cache layer, event-driven vs. request-driven)
3. **Skip trivial edits** — renames, formatting, comment-only changes, typo fixes,
   dependency version bumps with no behavior change. Don't touch the file for these.
4. **Keep every entry short.** Bullet points, not paragraphs. One or two lines per
   item. If you can't say it in two lines, you're explaining implementation, not
   architecture — trim it back to the decision and its rationale.
5. **Write for an engineer skimming it months later**, not for a first-time reader
   of the codebase. Name the actual pattern or concept (e.g., "circuit breaker
   around the payments API", not "added error handling"). This is what makes the
   file useful for interview prep and self-review — it should read like a changelog
   of decisions, not a code summary.

## File template

Create `architecture-notes.txt` in the project root with this structure:

```
# <Project name> — Architecture Notes
Last updated: <date>

## Architecture
- <component/service> — <what it does, one line>
- <key design pattern used> — <why, one line>

## Pipelines
- <flow name>: <source> -> <steps> -> <destination>
- <notable async/batch/streaming behavior>

## Security
- Auth: <mechanism, e.g. JWT / OAuth / API key>
- Secrets handling: <where/how stored>
- Known risks / open items: <anything intentionally deferred>

## Changelog
- <date>: <one-line summary of what changed and why>
```

The `## Changelog` section is the running log — append a line each time you update
the file, so the user can later reconstruct "what did I build, in what order, and
why" for an interview narrative without digging through commit history.

## Updating the file

- Read the existing file before editing — append/amend the relevant section, don't
  regenerate the whole file from scratch each time (this preserves history and
  avoids losing earlier rationale).
- Update `Last updated` and add one `Changelog` line per meaningful change, even if
  it's a single sentence.
- If a change spans multiple sections (e.g., a new service that also introduces a
  new auth flow), update all relevant sections in the same pass.

## When asked to recap or summarize (e.g., for an interview)

If the user asks something like "summarize this project" or "help me talk about
this in an interview," read `architecture-notes.txt` and restructure the content
into a short narrative: what was built, what design decisions were made and why,
what tradeoffs were considered, and what security/architecture concepts it
demonstrates. Keep this conversational and concise — this is a different output
format from the file itself, which stays terse.
