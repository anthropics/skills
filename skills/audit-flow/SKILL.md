---
name: audit-flow
description: Interactive system flow tracing across CODE, API, AUTH, DATA, NETWORK layers with SQLite persistence and Mermaid export. Use for security audits, compliance documentation, flow tracing, feature ideation, brainstorming, debugging, architecture reviews, or incident post-mortems. Triggers on audit, trace flow, document flow, security review, debug flow, brainstorm, architecture review, post-mortem, incident review.
license: MIT
compatibility: Requires Python 3.8+ (stdlib only, zero dependencies). Optional pyyaml for YAML export. Git for merge/diff driver features.
metadata:
  author: ArunJRK
  version: "1.0.0"
---

## ⚠️ MANDATORY ENTRY POINT — Execute Before ANY Other Action

**Step 1: Read schema.sql**
```bash
# ALWAYS read the schema first to understand tables, constraints, views
cat .claude/skills/audit-flow/schema.sql
```

**Step 2: Check if DB exists — NEVER recreate**
```bash
# Check for existing database
ls -la .audit/audit.db 2>/dev/null && echo "DB EXISTS - DO NOT RECREATE" || echo "No DB - safe to init"
```

**Step 3: If DB exists, show current state**
```bash
python .claude/skills/audit-flow/scripts/audit.py list
```

### 🚫 FORBIDDEN ACTIONS

| Action | Why Forbidden |
|--------|---------------|
| `rm .audit/audit.db` | Destroys audit history |
| `audit.py init` when DB exists | Overwrites existing data |
| `DROP TABLE` | Destroys audit history |
| `sqlite3 .audit/audit.db < schema.sql` when DB exists | Overwrites existing data |

**Rule:** If `.audit/audit.db` exists, ONLY use `audit.py list`, `show`, `export`, or INSERT operations. NEVER recreate.

---

# Audit Flow

Interactive tracing of system flows with SQLite persistence. Supports multiple named flows per session, non-linear flows (branching/merging), and multi-format exports.

## Organization Principles

**Directory structure by purpose:**
- **Audits/Documentation/Compliance:** `docs/audits/{name}-{YYYY-MM-DD}/`
- **Ideation/Brainstorming:** `docs/ideation/{name}-{YYYY-MM-DD}.md` (single file, no subdirectory unless artifacts needed)
- **Debugging/Incident Review:** `docs/audits/{name}-{YYYY-MM-DD}/` (same as audits — captures evidence)
- **Architecture Review:** `docs/audits/{name}-{YYYY-MM-DD}/` (same as audits — captures structural analysis)

**Required files:**
- INDEX.md (manifest, entry point)
- README.md (executive summary)
- {name}-audit.md (flow trace)

**Lazy initialization:** Create subdirectories only when artifacts exist
- `screenshots/` `network-traces/` `diagrams/` `code-samples/` `test-results/` `evidence/`

**Naming:** `{audit-name}-{type}.md`

## DB-First Discipline

**Invariant:** SQLite = sole source of truth. Context window: volatile, compacts without notice, hallucinates state.

**🚨 CRITICAL: NEVER DESTROY EXISTING DATA**
- If `.audit/audit.db` exists → it contains irreplaceable audit history
- NEVER run `init` when DB exists — use `list` to see what's there
- NEVER delete, drop, or recreate — only append

**Constraints:**

| Operation | Rule | Blocked rationalization |
|-----------|------|------------------------|
| **Entry** | Read `schema.sql` FIRST, check if DB exists SECOND | "I'll just start working" |
| **Init** | ONLY if `.audit/audit.db` does NOT exist | "Let me reinitialize to start fresh" |
| Schema | Read `schema.sql` BEFORE any SQLite command — understand tables, constraints, views first | "I know the schema from context" |
| Write | INSERT each tuple/edge/finding before moving to the next code location | "I'll batch-insert at the end" |
| Read | SELECT from DB before referencing tuple IDs, counts, or flow structure | "I remember the flow so far" |
| Export | `audit.py export` only — never generate mermaid/markdown from context | "Let me generate mermaid directly" |
| Resume | `audit.py show <session>` before any operation that references prior tuples | "I have the full trace in context" |
| Reference | Query tuple IDs from DB — IDs are DB-assigned, never inferred | "The tuple ID should be N" |
| **Default** | **When uncertain of flow state → query DB before proceeding** | *(any unlisted rationalization)* |

**Checkpoint:** Every 5 tuples → `audit.py show <session> <flow>`

---

## Interactive Workflow - ALWAYS ASK USER

### 1. Session Start - Ask:
```
Name: ___
Purpose: security-audit | documentation | compliance | ideation | brainstorming | debugging | architecture-review | incident-review
Description: ___ (optional)
```

Initialize directory immediately. Lazily create subdirectories when artifacts are generated.

### 2. Granularity - Ask:
```
[fine]   Function-level trace (~50-200 tuples)
         Use: Security audits, debugging

[coarse] Boundary-level trace (~10-30 tuples)
         Use: Documentation, high-level flows

Choose: fine / coarse
```

### 3. During Trace:
Ask at decision points: trace deeper? mark concern? add finding (severity)? note?

### 4. On Export:
Ask format: `json | yaml | md | mermaid | all`

Post-export: Generate INDEX.md manifest. Organize artifacts by type. Prune empty directories.

## Quick Reference

| Command | Purpose |
|---------|---------|
| `/audit-flow start` | New session (name, purpose, granularity) |
| `/audit-flow flow {name}` | Add new flow to session |
| `/audit-flow add {layer} {desc}` | Add tuple to current flow |
| `/audit-flow link {from} {to} {rel}` | Create edge (supports conditions for branches) |
| `/audit-flow finding {desc}` | Record finding |
| `/audit-flow show` | View session/flow details |
| `/audit-flow export` | Export (json/yaml/md/mermaid) |
| `/audit-flow git-setup` | Configure git merge/diff drivers (once) |

**Layers:** `CODE` | `API` | `NETWORK` | `AUTH` | `DATA`

**Relations:** `TRIGGERS` | `READS` | `WRITES` | `VALIDATES` | `TRANSFORMS` | `BRANCHES` | `MERGES`

## Semantic Rules for Relations

| Relation | Meaning | Use When | NOT For |
|----------|---------|----------|---------|
| `TRIGGERS` | A causes B to execute | Function calls, event handlers, HTTP requests | Static observations |
| `READS` | A consumes data from B | Cookie reads, DB queries, config lookups | Mutations |
| `WRITES` | A mutates data in B | Cookie writes, DB inserts, state updates | Read-only access |
| `VALIDATES` | A checks/verifies B | Auth checks, input validation, expiry checks | Chaining analyst observations |
| `TRANSFORMS` | A converts/maps data for B | Token exchange, response formatting | Unrelated processing |
| `BRANCHES` | A has conditional paths | if/else, switch, error vs success | **Must have condition label** |
| `MERGES` | Multiple paths converge at B | Parallel paths rejoin, error recovery | Single-path flow |

**CRITICAL: BRANCHES Must Have Conditions.** Every BRANCHES edge requires a `condition` describing which path. Example: `BRANCHES [token expired]` vs `BRANCHES [token valid]`.

## Observations vs Flow Steps

**Flow steps** = things the SYSTEM DOES (function calls, data reads, network requests). Verified by tracing code.

**Observations** = things the ANALYST NOTES (missing features, potential risks). Record as **findings**, not tuples.

**Wrong pattern:**
```
T50 "NO cross-tab sync"       ← observation, not a system action
T51 "React state NOT shared"  ← observation
T50 --VALIDATES--> T51         ← chaining observations as flow
```

**Correct pattern:**
```sql
-- Record as finding instead:
INSERT INTO findings (flow_id, session_id, severity, category, description)
VALUES (?, ?, 'medium', 'state-management',
        'No cross-tab sync: React state not shared across tabs');
```

**Rule:** NEVER chain observations with VALIDATES. If describing what the system DOESN'T do, use a finding.

## Data Model

```
Session (audit container)
  └── Flow (named DAG with entry point)
       └── Tuple (node: layer + action + subject)
            └── Edge (relation + optional condition)
```

## Storage & CLI

```bash
# Core
python .claude/skills/audit-flow/scripts/audit.py init              # Initialize DB
python .claude/skills/audit-flow/scripts/audit.py list              # List sessions
python .claude/skills/audit-flow/scripts/audit.py show <session>    # Show flows
python .claude/skills/audit-flow/scripts/audit.py show <session> <flow>  # Show flow details
python .claude/skills/audit-flow/scripts/audit.py export <session>  # Export all
python .claude/skills/audit-flow/scripts/audit.py export <session> -f <flow>  # Export one flow
python .claude/skills/audit-flow/scripts/audit.py validate <session>         # Validate flows

# Git integration
python .claude/skills/audit-flow/scripts/audit.py git-setup         # Configure merge/diff drivers (once)
python .claude/skills/audit-flow/scripts/audit.py db-merge %O %A %B # Git merge driver (auto-called)

# CSV backup/portability (optional)
python .claude/skills/audit-flow/scripts/audit.py csv-export               # DB → .audit/csv/*.csv
python .claude/skills/audit-flow/scripts/audit.py csv-import               # .audit/csv/*.csv → DB
python .claude/skills/audit-flow/scripts/audit.py csv-merge <theirs_dir>   # Merge two CSV sets
```

## Non-Linear Flows

**Branching:** One tuple → multiple outgoing edges with conditions
```sql
INSERT INTO edges (from_tuple, to_tuple, relation, condition)
VALUES (5, 6, 'BRANCHES', 'token valid'),
       (5, 7, 'BRANCHES', 'token expired');
```

**Merging:** Multiple tuples → one tuple
```sql
INSERT INTO edges (from_tuple, to_tuple, relation)
VALUES (6, 8, 'TRIGGERS'),
       (9, 8, 'MERGES');  -- refresh path merges back
```

## Files

- [scripts/audit.py](scripts/audit.py) - CLI for all commands (init, list, show, export, validate, db-merge, git-setup, csv-*)
- [COMMANDS.md](COMMANDS.md) - Detailed SQL reference
- [EXAMPLES.md](EXAMPLES.md) - Full examples with non-linear flows
- [schema.sql](schema.sql) - Database schema
- `.gitattributes` - Git merge/diff driver config for audit.db

## Git Context

Capture on session start: commit hash, branch, working tree status. Include in all exports.

## Mermaid Validation

Run `python .claude/skills/audit-flow/scripts/audit.py validate <session>` before export.

| Check | Severity | Description |
|-------|----------|-------------|
| BRANCHES without condition | ERROR | Every BRANCHES edge needs a condition label |
| Node count >= 60 | ERROR | Split into sub-flows |
| Node count >= 40 | WARN | Consider splitting |
| Orphan nodes | WARN | Node with no edges (disconnected) |
| Duplicate labels | WARN | Same action text without subject disambiguation |
| No entry point | WARN | All nodes have incoming edges |

**Post-export features (automatic):**
- **Step numbers**: BFS topological order from entry point (`1. action`, `2. action`)
- **Entry point**: Stadium shape with green styling
- **Edge arrows**: `-->` solid (TRIGGERS/VALIDATES/TRANSFORMS/BRANCHES/MERGES), `-.->` dotted (READS), `==>` thick (WRITES)
- **Observations**: Separated into dashed-border OBSERVATIONS subgraph
- **Direction**: `--direction LR` flag for horizontal layouts

## Diagram Readability Requirements

**All diagrams MUST be produced by `audit.py export`.** Never hand-craft mermaid. The exporter enforces:

1. **Entry point marker** — Green stadium-shape node `([label]):::entryPoint`
2. **Step numbers** — BFS topological order: `1. action`, `2. action`, `3. action`
3. **Legend block** — classDef styles for entryPoint, concern, observation
4. **Observation separation** — Concern-only chains go to OBSERVATIONS subgraph, not main flow
5. **Label safety** — HTML entities for `()`, `""`, `<>`, `|`, `[]` characters (auto-sanitized)

**Reading flow must be obvious.** A reader opening the diagram cold must immediately see:
- WHERE to start (green entry node)
- WHAT ORDER to read (step numbers)
- WHICH PATH is happy vs error (branch conditions on edges)
- WHAT THE COLORS MEAN (legend)

**Node label rules:**
- Use concrete nouns/verbs: `handleCallback()`, `exchangeCodeForTokens()`
- NOT bare verbs: ~~"Configure"~~, ~~"Select"~~, ~~"Enable"~~
- Disambiguate duplicates: auto-suffixed with subject when action repeats

**Size limits:**
- 40+ nodes → warning, consider splitting
- 60+ nodes → error, MUST split into sub-flows
- If flow has 5+ independent sub-flows → split by purpose

---

## Git Workflow — Custom Merge Driver

**Problem:** SQLite is binary — `git merge` can't auto-resolve `.audit/audit.db`.

**Solution:** Custom git merge driver. `audit.db` stays in git (small, single file). On conflict, git calls `audit.py db-merge` to auto-merge using SQL.

### One-Time Setup

```bash
python .claude/skills/audit-flow/scripts/audit.py git-setup
```

This configures (in `.git/config`):
- **Merge driver:** `merge.sqlite-audit` — calls `audit.py db-merge %O %A %B` on conflict
- **Diff driver:** `diff.sqlite` — `sqlite3 .dump` for readable `git diff` output

Also requires `.gitattributes` (already in repo):
```
.audit/audit.db diff=sqlite merge=sqlite-audit
```

### How It Works

1. You commit `audit.db` normally — `git add .audit/audit.db && git commit`
2. `git diff` shows SQL text (via textconv)
3. On `git merge` with conflict → git calls the merge driver automatically
4. Driver opens both DBs, merges sessions by name (later `updated_at` wins), remaps IDs
5. Result written to ours — merge completes cleanly

### Merge Strategy

| Table | Merge Key | Conflict Resolution |
|-------|-----------|-------------------|
| sessions | `name` (unique) | Keep later `updated_at` |
| flows | `(session_name, flow_name)` | Follow parent session winner |
| tuples | Parent flow | All tuples from winning flow kept |
| edges | Both endpoint tuples | Kept if both endpoints survive |
| findings | `(session_name, category, description)` | Dedup by content |

All INTEGER PKs remapped sequentially. Foreign keys updated.

### CSV Backup (Optional)

CSV export/import still available for portability and backup:
```bash
python .claude/skills/audit-flow/scripts/audit.py csv-export   # DB → .audit/csv/*.csv (QUOTE_ALL)
python .claude/skills/audit-flow/scripts/audit.py csv-import   # CSV → DB (recreates from scratch)
```

---

## Output Quality

**Principles:**
- ASCII sequence diagrams for complex flows
- Side-by-side tables for alternatives
- Real code from traced files with `file:line` references
- What/Why/Example pattern
- No generic templates

## Completion Checklist

- [ ] Directory exists with ISO date suffix
- [ ] INDEX.md manifest generated
- [ ] README.md (executive summary)
- [ ] Naming convention: `{name}-{type}.md`
- [ ] Artifacts in typed subdirectories (lazy init)
- [ ] Git context captured
- [ ] Git merge driver configured (`audit.py git-setup`)
- [ ] No orphaned files
- [ ] Diagrams pass `audit.py validate`

## Anti-Patterns

Flat structure, empty directories, orphan nodes, unlabeled branches, generic identifiers, missing git context, no manifest, hand-crafted mermaid, bare-verb labels.
