---
name: ham
description: Set up and maintain Hierarchical Agent Memory (HAM) — scoped CLAUDE.md files per directory that reduce token spend from 5-15k to 300-800 tokens per request. Use when setting up agent memory, optimizing CLAUDE.md files, reducing token spend, or when agents keep forgetting context, re-proposing rejected solutions, or burning tokens re-reading files. Works across Web, iOS, Android, Flutter, React Native, Python, Rust, and Go projects.
license: MIT
---

# HAM (Hierarchical Agent Memory)

Zero-dependency, file-based memory system. Scopes agent context to the directory level instead of loading one massive root file on every request.

## System Architecture

Three layers:

**Layer 1 — Root CLAUDE.md** (always loaded, under 250 tokens)
Tech stack, hard rules, operating instructions. No implementation details.

**Layer 2 — Subdirectory CLAUDE.md files** (loaded per-directory, under 300 tokens each)
Scoped context per major directory. Agent reads root + target directory file only.

**Layer 3 — .memory/ directory** (referenced on demand)
- `decisions.md` — Confirmed Architecture Decision Records
- `patterns.md` — Confirmed reusable code patterns
- `inbox.md` — Quarantine for inferred items awaiting developer confirmation
- `sessions/YYYY-MM-DD.md` — Disposable session scratchpads

Never write inferred knowledge directly to `decisions.md` or `patterns.md`. All inferences go to `inbox.md` and stay there until the developer explicitly confirms them.

```
project-root/
├── CLAUDE.md                     # Layer 1: Global (~150-250 tokens)
├── .memory/
│   ├── decisions.md              # Confirmed ADRs
│   ├── patterns.md               # Confirmed patterns
│   ├── inbox.md                  # Inferred items awaiting confirmation
│   └── sessions/
│       └── YYYY-MM-DD.md         # Session scratchpads (disposable)
├── src/
│   ├── CLAUDE.md                 # Layer 2: Shared src conventions
│   ├── api/
│   │   └── CLAUDE.md             # API-specific context
│   ├── components/
│   │   └── CLAUDE.md             # UI component context
│   └── db/
│       └── CLAUDE.md             # Database & schema context
└── ...
```

## Setup Flow

### Step 1: Detect Platform and Maturity

Detect the platform first, then determine project maturity.

| Signal Files | Platform |
|---|---|
| `*.xcodeproj`, `*.xcworkspace`, `Package.swift` | iOS (Swift/SwiftUI) |
| `build.gradle`, `build.gradle.kts`, `settings.gradle` | Android (Kotlin) |
| `pubspec.yaml` | Flutter |
| `react-native.config.js`, `metro.config.js`, or `package.json` with `react-native` | React Native |
| `package.json` with `next`, `nuxt`, `svelte`, `remix`, or `astro` | Web (JS/TS Framework) |
| `package.json` with `express`, `fastify`, `hono`, or `koa` | Web (Node Backend) |
| `pyproject.toml`, `requirements.txt` with `django`, `flask`, or `fastapi` | Python Web |
| `Cargo.toml` | Rust |
| `go.mod` | Go |

If multiple signals exist (e.g., `package.json` + `ios/` + `android/`), treat as cross-platform.

Determine maturity:
- Source directory has multiple subdirectories with code → **Brownfield**
- Source directory has fewer than 3 subdirectories with code → **Early Stage**
- No source directory, or user says starting fresh → **Greenfield**

### Step 2: Run the Appropriate Setup Path

#### Path A: Greenfield (New Project)

1. Ask the user for their stack (framework, language, database, deployment target).
2. Generate root `CLAUDE.md` with declared stack, default rules, and operating instructions.
3. Generate `.memory/decisions.md` — empty, structured with ADR format header.
4. Generate `.memory/patterns.md` — empty, structured with pattern format header.
5. Generate `.memory/inbox.md` — empty, with header explaining the review process.
6. Generate `.memory/sessions/` — empty directory with `.gitkeep`.
7. Do NOT create subdirectory CLAUDE.md files. Operating instructions tell the agent to create them as directories are created.

#### Path B: Early Stage (2-4 weeks in)

1. Scan: project config, directory structure, existing CLAUDE.md files. Identify stack, conventions, top 2-3 directories.
2. Generate root `CLAUDE.md` — lean, accurate stack, operating instructions.
3. Generate `.memory/inbox.md` — pre-populate with 3-5 inferred decisions.
4. Generate `.memory/decisions.md` — empty, structured.
5. Generate `.memory/patterns.md` — extract 2-3 high-confidence patterns.
6. Generate subdirectory `CLAUDE.md` files for the 2-3 directories with meaningful code only.

#### Path C: Brownfield (Established Project)

1. Analyze the codebase deeply.
2. Generate root `CLAUDE.md` — lean, accurate stack, operating instructions.
3. Generate `.memory/inbox.md` — populate with every inferred decision and pattern with confidence levels.
4. Generate `.memory/decisions.md` — empty, structured.
5. Generate `.memory/patterns.md` — populate only with high-confidence patterns (consistent across 3+ files).
6. Generate subdirectory `CLAUDE.md` files for every major directory with meaningful code.
7. If existing CLAUDE.md is bloated, decompose into the hierarchical system. Show before/after token comparison.

## Operating Instructions

Embed this block in the root `CLAUDE.md` of every project:

```markdown
## Agent Memory System

### Before Working
1. Read this file first for global context.
2. Read the target directory's CLAUDE.md before making changes there.
3. If a task spans multiple directories, read each affected directory's CLAUDE.md (limit 3).
4. Check .memory/decisions.md before proposing architectural changes.
5. Check .memory/patterns.md before implementing common functionality.

### During Work
6. When creating a new directory, create a CLAUDE.md in it documenting:
   - Purpose of this directory
   - Conventions specific to this directory
   - Active integrations or dependencies
   - Patterns unique to this area

### After Work
7. If you changed conventions, patterns, or architecture: update memory.
8. Log new conventions/patterns to the relevant directory's CLAUDE.md.
9. Log architectural decisions to .memory/decisions.md using ADR format.
10. Log reusable patterns to .memory/patterns.md.
11. Never delete confirmed decisions. Mark as [superseded] and add new entry.
12. If uncertain about an inference, write to .memory/inbox.md — never to canonical files.

### Memory Safety
- Never record API keys, secrets, user data, or customer information.
- Never record speculative debugging hypotheses outside session scratchpads.
- Never overwrite confirmed decisions — only supersede with new entries.
- Never promote items from inbox.md without explicit developer confirmation.
```

## Memory Audit

When the user says "audit memory" or "check memory health," run these checks:

1. **Missing files:** Find directories under source root containing code but no CLAUDE.md.
2. **Oversized files:** Flag root CLAUDE.md over ~60 lines or subdirectory files over ~75 lines.
3. **Stale inbox:** If `.memory/inbox.md` has content, remind user to review.
4. **Bloated memory:** Flag `decisions.md` or `patterns.md` exceeding ~100 entries.
5. **Orphaned references:** Check if subdirectory CLAUDE.md files reference patterns that no longer exist.

Present as a checklist. Do not auto-fix — the developer decides.

## Token Budget

- Root `CLAUDE.md`: under 250 tokens (~60 lines)
- Subdirectory `CLAUDE.md`: under 300 tokens (~75 lines)
- `decisions.md`: archive superseded entries past ~100 entries
- `patterns.md`: keep code examples minimal
- `inbox.md`: review weekly

## Root CLAUDE.md Templates

### Web
```markdown
# Project: [Name]

## Stack
- Framework: [e.g., Next.js 15 (App Router)]
- Language: [e.g., TypeScript (strict)]
- Database: [e.g., Supabase]
- Styling: [e.g., Tailwind CSS]

## Critical Rules
- Never modify .env files directly
- All DB changes go through migrations
- Use server actions for mutations
```

### iOS
```markdown
# Project: [Name]

## Stack
- Language: Swift [version]
- UI: SwiftUI (min iOS [version])
- Architecture: [MVVM | TCA | VIPER]
- Persistence: [SwiftData | Core Data]

## Critical Rules
- All new views use SwiftUI
- Keychain for sensitive data
- Never force-unwrap optionals
```

### Android
```markdown
# Project: [Name]

## Stack
- Language: Kotlin [version]
- UI: [Jetpack Compose | XML]
- Architecture: [MVVM | MVI] with [Hilt | Koin]
- Min SDK: [version]

## Critical Rules
- All new UI in Compose
- EncryptedSharedPreferences for sensitive data
- ViewModels expose StateFlow
```

### Flutter
```markdown
# Project: [Name]

## Stack
- Framework: Flutter [version]
- State Management: [Riverpod | Bloc | GetX]
- Navigation: [GoRouter | Navigator 2.0]

## Critical Rules
- All state through [chosen solution]
- Secure storage for tokens
- No business logic in widgets
```

### React Native
```markdown
# Project: [Name]

## Stack
- Framework: React Native [version] [Expo | Bare]
- Navigation: [React Navigation | Expo Router]
- State: [Zustand | Redux Toolkit]

## Critical Rules
- Functional components with hooks
- Sensitive data in react-native-keychain
- Platform-specific code uses .ios.tsx/.android.tsx
```

## Subdirectory CLAUDE.md Template

```markdown
# [Directory Name] Context

## Purpose
[One sentence: what this directory is responsible for]

## Conventions
- [Convention specific to this directory]

## Active Integrations
- [Integration]: [One-line description]

## Key Patterns
- [Pattern name]: [One-line description]

## Gotchas
- [Non-obvious thing that will trip up an agent]
```

## decisions.md Template

```markdown
# Architecture Decision Records

### ADR-[NNN]: [Title] ([Date])
**Status:** [active | superseded | deprecated]
**Context:** What problem or choice prompted this
**Decision:** What was chosen
**Alternatives Considered:** What was rejected, with brief reasoning
**Consequences:** What this means for future development
```

## patterns.md Template

```markdown
# Reusable Patterns

### [Pattern Name]
**When to use:** [Situation that calls for this pattern]
**Implementation:**
```[language]
// Concise code example
```
**Gotchas:**
- [Non-obvious edge case]
```

## inbox.md Template

```markdown
# Memory Inbox

Items here are inferred or unconfirmed. Review periodically:
- **Confirm:** Move to decisions.md or patterns.md, delete from here.
- **Reject:** Delete if incorrect.
- **Revise:** Edit to be accurate, then promote.

### Inferred Decision: [Title] ([Date])
**Confidence:** [high | medium | low]
**Evidence:** [File paths suggesting this]
**Proposed ADR:** [What the decision would be if confirmed]
```

The inbox is never authoritative context. The agent reads `decisions.md` and `patterns.md` for confirmed knowledge.
