---
name: stack-map
description: >
  Maps the full call stack of an API endpoint or function top-down, AND traces the data write path back to its source, marking every place that needs a change with a one-line numbered comment — without implementing anything. Use this skill whenever the user wants to: add a new parameter/filter/dimension to an existing endpoint; understand the full chain of code and tables that need to change before implementing; plan a cross-cutting change across services, DAOs, jobs, and schema migrations; or says things like "mark all the places", "trace the call stack", "map the changes", "where does this data come from", "what do I need to update", or "stack map". This is a planning tool — it produces a numbered comment map, not code.
---

# stack-map

You are mapping a change through a codebase by placing one-line numbered comments at every location that needs to be modified. You are **not implementing anything** — only leaving markers so the developer can find every touch point before writing a single line of real code.

## Phase 0: Ask before you map

Before placing any markers, scan the call chain for architectural forks — decisions where the wrong choice would force a complete rewrite of the map. Ask about at most **two** of these upfront. If there are no meaningful forks, skip straight to mapping.

### What counts as a fork worth asking about

A fork is worth asking about when the answer changes a large portion of the map — not just one marker. Common examples:

| Fork | Why it matters |
|------|---------------|
| Add column to existing table vs. create a new parallel table | Changes every touch point: table class, migration, DAO read, DAO write, conflict key |
| Filter existing data vs. store a new pre-aggregated dimension | Changes whether refreshers/jobs need new write paths |
| Extend existing API contract vs. add a new endpoint | Changes #1 and all downstream callers |

A fork is **not** worth asking about when:
- It only affects one or two markers (just note both options inline on that marker)
- The code already constrains the answer (e.g. the table is partitioned and altering the index would be risky — that's a fact, not a choice)
- It's a detail the developer can decide while implementing

### How to ask

One short question per fork, with two concrete options. Don't explain the whole map first — just ask and wait. Example:

> Before I map this: should the `product_id` be added to the existing `customer_buckets_history` table, or stored in a new parallel table (`customer_buckets_history_product`)?
> - **Existing table** — simpler, but requires rebuilding the unique index on a live partitioned table
> - **New parallel table** — no changes to existing table or refreshers; new write path alongside the old one

### Mid-map questions

Only pause mid-map for a genuine blocker — a fork you couldn't detect from reading the code, where the answer changes what you'd mark next. If the decision only affects one marker, annotate it inline with both options and continue.

---

## What you produce

One-line comments of the form `// #N <what needs to change here>`, placed in-file at each touch point. When you're done, you report the full numbered map.

## Numbering scheme

Numbers represent stack depth and follow the data flow **from API down to the read, then back up the write path to the data source**:

| Number | Meaning |
|--------|---------|
| `#1` | API entry point (resource/controller/handler) |
| `#2` | First callee (service method called by the API) |
| `#2.1`, `#2.2` | Siblings at the same depth |
| `#3` | Read from a table/store (DAO read method) |
| `#3.1` | Schema migration — **only when a new column is actually being added** |
| `#4` | Write to that same table (DAO write/upsert method) |
| `#5` | Caller of the write — who drives the upsert/insert |
| `#5.1`, `#5.2` | Sub-steps within that caller |
| `X.0` | Table class definition — **only when a new column field needs to be added to the class** |
| `X.N` | Sub-level N within depth X |
| `X.N.0` | Table class for a nested sub-chain under X.N |

**The X.0 / X.1 pattern only applies when schema changes are needed.** If the required column already exists, skip X.0 and X.1 and note "no schema change needed" in the comment instead.

**Key pattern for each table that needs a new column:**
```
X     = read method  (add filter parameter)
X.0   = table class  (add new TableField here)
X.1   = migration    (DDL: ALTER TABLE ADD COLUMN IF NOT EXISTS ...)
X+1   = write method (set the new field in insert/upsert)
```

## Comment format

One line only. Start with `// #N`. State:
- What parameter/field/return type needs to change
- What the dependency is when applicable (e.g. `requires #3.1 column`)
- What other numbers this feeds or receives from

**Examples:**
```kotlin
// #1 add @QueryParam("productId") productIds: List<Long>? here and pass to service

// #3 add productIds: List<Long>? parameter; filter by t.productId IN productIds (requires #3.1 column)

// #3.0 add val productId: TableField<Long> = createBigIntField("product_id")

// #3.1 ADD COLUMN IF NOT EXISTS product_id BIGINT — read (#3) and write (#4) both depend on this

// #4 set t.productId in insert; update onConflict key to include t.productId (requires #3.1)

// #3 no schema change needed — customerId column already exists; add .and(t.customerId.eq(customerId)) when non-null
```

## Traversal order

### Starting at an API endpoint (top-down)

1. **#1** — the API resource/handler. Mark where the new parameter enters.
2. **Follow the call chain down** — each callee gets the next number. Siblings (multiple calls at same depth) get decimal suffixes.
3. **At the DAO read** — mark the read method. If a new column is needed: also mark the table class (X.0) and note that a migration is required (X.1). If the column already exists, say so inline and skip X.0/X.1.
4. **Find the write** — grep for who writes/upserts to this table. Mark the write method (X+1). Note if the `onConflict` key needs updating.
5. **Recurse up the write chain** — mark callers until you reach an external source (job, queue consumer, ingest pipeline).
6. **Nested sub-chains** — if the read path branches (e.g. "use pre-computed table if today, else recalculate"), trace each branch separately under the parent number (X.N.0, X.N.1, etc.).

### Starting mid-chain (e.g. at a refresher or writer)

When the user gives you a writer/refresher as the starting point, trace in both directions:

- Number the **write side** starting from the given file (e.g. `#1` = the refresher's write method)
- Mark the **table class** (`#1.0`) and **migration** (`#1.1`) if a new column is needed
- Trace **who reads from this table** — these get earlier numbers (`#R` where R < 1, or re-number with the write as the anchor and readers as sub-numbers like `#1.R1`, `#1.R2`). The clearest approach: use the write as `#N`, then list readers as `R1`, `R2`... in the summary noting they consume the data written at `#N`.
- Trace **who calls the write** (job, trigger) — these get higher numbers (`#2`, `#3`...)

## Scope: what to mark and what to skip

**Mark:**
- API resources/handlers
- Service methods in the call chain
- DAO read and write methods
- Table class definitions (when a new column is needed)
- Migration files (when a new column is needed)
- Background jobs / queue consumers that call the write
- Any caller of a marked function that also needs to pass the new parameter

**Do not mark:**
- Test files — tests are not part of the change map (they'll need updating, but that's the developer's job after implementing)
- Pure pass-through methods that don't need signature changes (note them in the summary instead)
- Table classes when no new column is needed (just note "column already exists" in the read method's comment)

## Final scan (do this after placing all comments)

Before reporting the map, verify:
- Every table read has a corresponding write path marked (or explicitly noted as read-only)
- Every table class marked `X.0` has a migration `X.1` noted
- Every caller of a marked function is itself marked (grep for callers of each marked method)
- If the call path branches, both branches are covered
- Multi-tenant check: every new query still passes `organizationId` in the WHERE clause

Report any gaps you find.

## Output: the map

After placing all comments, print a summary table:

```
#    | File (relative to repo root)                          | Line | What changes
-----|-------------------------------------------------------|------|---------------------------
#1   | src/.../HealthScoreOverTimeResource.kt                | 26   | add @QueryParam productIds
#2   | src/.../CustomerBucketsHistoryService.kt              | 62   | add productIds param, pass to dao.read
#3   | src/.../CustomerBucketsHistoryDao.kt                  | 95   | filter by productId (requires #3.1)
#3.0 | src/.../CustomerBucketsHistoryDao.kt                  | 130  | add val productId TableField
#3.1 | src/.../db/migration/2026_06/V2026_0617_1200__....sql | 1    | ADD COLUMN product_id BIGINT
#4   | src/.../CustomerBucketsHistoryDao.kt                  | 81   | set t.productId; update conflict key
```
