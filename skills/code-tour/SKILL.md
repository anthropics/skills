---
name: code-tour
description: Create CodeTour .tour files — persona-targeted, step-by-step walkthroughs that link to real files and line numbers. Activate when the user asks to "create a tour", "make a code tour", "generate a tour", "onboarding tour", "tour for this PR", "architecture tour", "explain how X works", "vibe check", "PR review tour", "contributor guide", or any request for a structured walkthrough through code. Supports 20 developer personas and all CodeTour step types.
---

# Code Tour

Create **CodeTour** files — persona-targeted, step-by-step walkthroughs of a codebase that link directly to files and line numbers. CodeTour files live in `.tours/` and work with the [VS Code CodeTour extension](https://github.com/microsoft/codetour).

A great tour is not just annotated files. It is a **narrative** — a story told to a specific person about what matters, why it matters, and what to do next.

**Only create `.tour` JSON files. Never create, modify, or scaffold any other files.**

## When to Use

- User asks to create a code tour, onboarding tour, or architecture walkthrough
- User says "tour for this PR", "explain how X works", "vibe check", "RCA tour"
- User wants a contributor guide, security review tour, or bug investigation walkthrough
- Any request for a structured walkthrough through code with file/line anchors

## How It Works

### Step 1: Discover the repo

Before asking the user anything, explore the codebase:
- List the root directory, read the README, check key config files
- Identify language(s), framework(s), and what the project does
- Map the folder structure 1-2 levels deep
- Find entry points: main files, index files, app bootstrapping
- **Note which files actually exist** — every path in the tour must be real

### Step 2: Infer the intent

One message from the user should be enough. Read their request and infer persona, depth, and focus.

| User says | Persona | Depth |
|-----------|---------|-------|
| "tour for this PR" / "#123" | pr-reviewer | standard |
| "why did X break" / "RCA" | rca-investigator | standard |
| "onboarding" / "new joiner" | new-joiner | standard |
| "quick tour" / "vibe check" | vibecoder | quick |
| "architecture" / "system design" | architect | deep |
| "security" / "auth review" | security-reviewer | standard |
| "explain how X works" | feature-explainer | standard |

### Step 3: Read the actual files

**Every file path and line number in the tour must be verified by reading the file.** A tour pointing to the wrong file or a non-existent line is worse than no tour.

### Step 4: Write the tour

Save to `.tours/<persona>-<focus>.tour`.

#### Tour root structure

```json
{
  "$schema": "https://aka.ms/codetour-schema",
  "title": "Descriptive Title — Persona / Goal",
  "description": "One sentence: who this is for and what they'll understand after.",
  "ref": "main",
  "isPrimary": false,
  "steps": []
}
```

#### Step types

**Content step** — narrative only, no file. Max 2 per tour (intro + closing).
```json
{ "title": "Welcome", "description": "markdown..." }
```

**Directory step** — orient to a module.
```json
{ "directory": "src/services", "title": "Service Layer", "description": "..." }
```

**File + line step** — the workhorse.
```json
{ "file": "src/auth/middleware.ts", "line": 42, "title": "Auth Gate", "description": "..." }
```

**Selection step** — highlight a block of code.
```json
{
  "file": "src/core/pipeline.py",
  "selection": { "start": { "line": 15, "character": 0 }, "end": { "line": 34, "character": 0 } },
  "title": "The Request Pipeline", "description": "..."
}
```

**Pattern step** — match by regex instead of line number.
```json
{ "file": "src/app.ts", "pattern": "export default class Application", "title": "...", "description": "..." }
```

**URI step** — link to external resources (PRs, issues, docs).
```json
{ "uri": "https://github.com/org/repo/pull/456", "title": "The PR", "description": "..." }
```

### Step count calibration

| Depth | Steps | Use for |
|-------|-------|---------|
| Quick | 5-8 | Vibecoder, fast exploration |
| Standard | 9-13 | Most personas |
| Deep | 14-18 | Architect, RCA |

### Writing descriptions — the SMIG formula

Every description answers four questions:
- **S — Situation**: What is the reader looking at?
- **M — Mechanism**: How does this code work?
- **I — Implication**: Why does this matter for this persona?
- **G — Gotcha**: What would a smart person get wrong here?

### Step 5: Validate

After writing the tour, verify:
- [ ] Every `file` path is relative to repo root (no leading `/` or `./`)
- [ ] Every `file` confirmed to exist by reading it
- [ ] Every `line` number verified (not guessed)
- [ ] First step has a `file` or `directory` anchor (content-only first step = blank page in VS Code)
- [ ] At most 2 content-only steps
- [ ] `nextTour` matches another tour's `title` exactly if set

## The 20 Personas

| Persona | Goal | Must cover |
|---------|------|------------|
| **Vibecoder** | Get the vibe fast | Entry point, request flow, main modules. Max 8 steps. |
| **New joiner** | Structured ramp-up | Directories, setup, business context, service boundaries |
| **Bug fixer** | Root cause fast | User action -> trigger -> fault points, test locations |
| **RCA investigator** | Why did it fail | Causality chain, state transitions, observability anchors |
| **Feature explainer** | One feature end-to-end | UI -> API -> backend -> storage |
| **PR reviewer** | Review correctly | Change story, invariants, risky areas, reviewer checklist |
| **Architect** | Shape and rationale | Module boundaries, design tradeoffs, extension points |
| **Security reviewer** | Trust boundaries | Auth flow, input validation, secret handling |
| **Refactorer** | Safe restructuring | Seams, hidden deps, extraction order |
| **External contributor** | Contribute safely | Safe areas, conventions, landmines |

## Narrative Arc

1. **Orientation** — must be a `file` or `directory` step (never content-only first step)
2. **High-level map** (1-3 directory steps) — major modules
3. **Core path** (file/line steps) — the specific code that matters
4. **Closing** (content) — what the reader can now do, suggested follow-ups

## Anti-Patterns

| Anti-pattern | Fix |
|---|---|
| **File listing** — visiting files with "this contains the models" | Tell a story. Each step should depend on seeing the previous one. |
| **Generic descriptions** | Name the specific pattern unique to this codebase. |
| **Line number guessing** | Never write a line number you didn't verify. |
| **Too many steps** for a quick tour | Actually cut steps, don't just label it "quick". |
| **Hallucinated files** | If a file doesn't exist, skip the step. |

## Examples

- Full skill with validation scripts and schema: [code-tour repo](https://github.com/vaddisrinivas/code-tour)
- Real-world tours: [coder/code-server](https://github.com/coder/code-server/blob/main/.tours/contributing.tour), [a11yproject](https://github.com/a11yproject/a11yproject.com/blob/main/.tours/code-tour.tour)
- Share tours instantly: `https://vscode.dev/github.com/<owner>/<repo>`
