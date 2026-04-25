# CLAUDE.md Best Practices Reference

Comprehensive reference from the official Claude Code documentation (https://code.claude.com/docs/en/memory).

## Table of Contents

1. [File Locations and Scope](#file-locations-and-scope)
2. [Writing Effective Instructions](#writing-effective-instructions)
3. [Import System](#import-system)
4. [Rules Organization](#rules-organization)
5. [Auto Memory vs CLAUDE.md](#auto-memory-vs-claudemd)
6. [Anti-Patterns](#anti-patterns)
7. [Examples of Good Instructions](#examples-of-good-instructions)
8. [Examples of Bad Instructions](#examples-of-bad-instructions)

---

## File Locations and Scope

| Scope | Location | Purpose | Shared with |
|-------|----------|---------|-------------|
| **Managed policy** | OS-specific system path | Org-wide instructions by IT/DevOps | All users in org |
| **Project** | `./CLAUDE.md` or `./.claude/CLAUDE.md` | Team-shared project instructions | Team via source control |
| **User** | `~/.claude/CLAUDE.md` | Personal preferences for all projects | Just you |

Resolution order (most specific wins):
1. Managed policy CLAUDE.md (cannot be excluded)
2. CLAUDE.md files from current directory up to root
3. `.claude/rules/` files (unconditional ones at launch, path-scoped on demand)
4. User `~/.claude/CLAUDE.md`
5. Subdirectory CLAUDE.md files (loaded when Claude reads files in those dirs)

## Writing Effective Instructions

### Size Guidelines

- **Target**: Under 200 lines per CLAUDE.md file
- **Why**: Loaded into every session's context window; longer files consume tokens and reduce adherence
- **If too long**: Split using `@` imports or `.claude/rules/` files
- **Auto memory**: Only first 200 lines of MEMORY.md loaded; this doesn't apply to CLAUDE.md (loaded in full)

### Structure

- Use markdown headers (`##`, `###`) to group related instructions
- Use bullet lists for scannable items
- Avoid dense paragraphs
- Logical flow: build commands → test commands → code style → architecture → conventions → pitfalls

### Specificity

Concrete and verifiable instructions work best:

| Bad | Good |
|-----|------|
| Format code properly | Use 2-space indentation |
| Test your changes | Run `npm test` before committing |
| Keep files organized | API handlers live in `src/api/handlers/` |
| Use good naming | Components: PascalCase, hooks: use- prefix, utils: camelCase |
| Handle errors well | Wrap API calls in try/catch, log to Sentry, return user-friendly message |

### Consistency

- Review all CLAUDE.md files and `.claude/rules/` for contradictions
- If two rules conflict, Claude picks one arbitrarily
- In monorepos, use `claudeMdExcludes` to skip irrelevant CLAUDE.md files

## Import System

Use `@path/to/file` syntax to import additional files:

```markdown
See @README for project overview.
See @package.json for available npm commands.

# Additional Instructions
- git workflow @docs/git-instructions.md
```

Rules:
- Both relative and absolute paths allowed
- Relative paths resolve relative to the file containing the import
- Maximum 5 hops of recursive imports
- First encounter shows approval dialog to user
- Personal imports: `@~/.claude/my-project-instructions.md` (not checked in)

## Rules Organization

### Basic Setup

```
.claude/
├── CLAUDE.md           # Main project instructions
└── rules/
    ├── code-style.md   # Code style guidelines
    ├── testing.md      # Testing conventions
    └── security.md     # Security requirements
```

### Path-Specific Rules

```markdown
---
paths:
  - "src/api/**/*.ts"
---

# API Development Rules
- All endpoints must include input validation
```

### Glob Patterns

| Pattern | Matches |
|---------|---------|
| `**/*.ts` | All TypeScript files in any directory |
| `src/**/*` | All files under `src/` |
| `*.md` | Markdown files in project root |
| `src/components/*.tsx` | React components in a specific directory |
| `src/**/*.{ts,tsx}` | Multiple extensions with brace expansion |

### User-Level Rules

Personal rules in `~/.claude/rules/` apply to every project. Loaded before project rules (project rules take higher priority).

### Symlinks

`.claude/rules/` supports symlinks for sharing rules across projects:
```bash
ln -s ~/shared-claude-rules .claude/rules/shared
ln -s ~/company-standards/security.md .claude/rules/security.md
```

## Auto Memory vs CLAUDE.md

| Aspect | CLAUDE.md | Auto Memory |
|--------|-----------|-------------|
| **Who writes** | You | Claude |
| **Content** | Instructions and rules | Learnings and patterns |
| **Scope** | Project, user, or org | Per working tree |
| **Loaded** | Every session (full) | Every session (first 200 lines) |
| **Best for** | Coding standards, workflows, architecture | Build commands, debugging insights, preferences |
| **Location** | Project root or `.claude/` | `~/.claude/projects/<project>/memory/` |

Use CLAUDE.md when you want to guide Claude's behavior explicitly.
Use auto memory to let Claude learn from corrections without manual effort.

## Anti-Patterns

### Things to Avoid in CLAUDE.md

1. **Code patterns derivable from reading code** — Claude can read the codebase
2. **Git history** — `git log` / `git blame` are authoritative
3. **Debugging solutions** — The fix is in the code; commit message has context
4. **Generic programming advice** — Claude already knows this
5. **Ephemeral task details** — Temporary state doesn't belong in persistent instructions
6. **Long reference documentation** — Put in `.claude/rules/` or external files with `@` import
7. **Contradicting instructions** — Claude picks arbitrarily between conflicts
8. **ALL CAPS EMPHASIS** — Explain the "why" instead of shouting
9. **Overly rigid MUSTs/NEVERs without explanation** — Claude follows reasoned instructions better

### Size Anti-Patterns

- Putting everything in one giant CLAUDE.md (split into rules)
- Including full API documentation (use `@` imports)
- Duplicating information from README or package.json (reference them instead)

## Examples of Good Instructions

```markdown
## Build & Run

- `pnpm dev` — start dev server on localhost:3000
- `pnpm build` — production build (runs type check first)
- `pnpm lint` — eslint + prettier check

## Test

- `pnpm test` — run all tests with vitest
- `pnpm test src/utils/date.test.ts` — run single test file
- Tests use MSW for API mocking; handlers are in `src/mocks/handlers.ts`

## Code Style

- 2-space indentation, no tabs
- Named exports only (no default exports except pages)
- Import order: react → external libs → @/ internal → relative → types
- `import type` on separate line from value imports

## Architecture

- App Router (Next.js 14): pages in `app/`, components in `src/components/`
- Server Components by default; 'use client' only when needed
- API routes in `app/api/` — all use the `withAuth` middleware wrapper
- Database queries through Prisma; schema at `prisma/schema.prisma`

## Gotchas

- `NEXT_PUBLIC_*` env vars are in client bundle — never put secrets there
- The `users` table has a soft-delete (`deleted_at`) — always filter in queries
- Auth tokens expire in 15min; refresh logic is in `src/lib/auth.ts`
```

## Examples of Bad Instructions

```markdown
# Bad: Too vague
- Write clean code
- Follow best practices
- Make sure tests pass

# Bad: Derivable from code
- The User model has fields: id, name, email, created_at
- The fetchUsers function takes a page parameter

# Bad: Too long / reference doc
- [500 lines of API documentation that should be a separate file]

# Bad: Generic advice
- Use meaningful variable names
- Don't repeat yourself
- Keep functions small

# Bad: Contradicting
- Always use semicolons (in one section)
- No semicolons (in another section)

# Bad: Ephemeral
- We're currently working on the auth migration (ticket #1234)
- The staging server is down today
```
