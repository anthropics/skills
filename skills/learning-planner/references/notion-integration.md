# Notion Integration

`learning-plan.json` is always the canonical source of truth. Notion (when
available) is a *presentation and tracking surface* generated/synced from it
-- never the other way around, and never a hard dependency. This file covers
two paths:

- **Path A** -- a Notion MCP connector is available and authorized.
- **Path B** -- no Notion MCP (or the user doesn't want it). This path always
  works and requires nothing beyond the scripts already in `scripts/`.

Always check availability before assuming either path. Never tell the user
Notion integration "isn't possible" -- Path B is always available.

---

## Step 0: Determine What's Available

1. Check whether a Notion MCP connector is configured and authorized in the
   current environment.
2. If available, confirm it has access to a workspace/page the roadmap can
   live under (ask the user which page/workspace to use if not obvious).
3. If unavailable, or the user says they don't use Notion, go straight to
   Path B -- don't ask about Notion again unless the user brings it up.
4. If a connector exists but errors (auth, permissions, no accessible pages),
   explain the issue, fall back to Path B, and offer to retry Path A later.

---

## Path A: Notion MCP Available

### A.1 Database Property Schema

Create one Notion database for the roadmap (or use one the user points to).
Each module becomes one row/page. Map `learning-plan.json` module fields to
Notion properties as follows:

| `learning-plan.json` field | Notion property name | Notion property type | Notes |
|---|---|---|---|
| `title` | Title | Title | Page title |
| `id` | ID | Rich text | Stable key for re-sync; never change after creation |
| `status` | Status | Select (or Status type) | Options: Locked, Available, In Progress, Completed -- mirrors `STATUS_LABELS` in the render scripts |
| `category` | Category | Select | Options: core, optional, advanced |
| `sequencing` | Sequencing | Select | Options: sequential, parallel |
| `priority` | Priority | Select | Options: high, medium, low |
| `skippable` | Skippable | Checkbox | |
| `is_milestone` | Is Milestone | Checkbox | |
| `estimated_effort` | Estimated Effort | Rich text | Free text; not a date/duration since units vary by discipline |
| `prerequisites` | Prerequisites | Relation (self-referencing) | Set in a second pass once all pages exist (A.3) |
| `parent_id` | Parent module | Relation (self-referencing), or Notion's native sub-item relation if the database supports it | Set in a second pass (A.3) |

Fields not in this table (`learning_objectives`, `deep_understanding_concepts`,
`common_mistakes`, `expected_competence`, `industry_expectations`,
`mastery_goals`, `evaluation`, `real_world_competence`, `resources`, `notes`)
are **not** Notion properties -- they go into the page *body* (A.5). Putting
them in properties would make the database table unreadable and duplicates
what the Detailed Learning Plan already does well.

If the user already has a database with a different property layout, prefer
mapping onto their existing properties over forcing this exact schema --
ask before restructuring a database that predates this roadmap.

### A.2 Creating Pages

1. Compute hierarchical order the same way `render_plan.py`/`render_dashboard.py`
   do (`ordered_modules`: top-level modules in JSON order, each followed
   recursively by its submodules).
2. Create one page per module in that order, setting all scalar properties
   from the table above (everything except Prerequisites and Parent module,
   which need page IDs that don't exist yet).
3. Keep a mapping of `module.id -> Notion page ID` as pages are created --
   this is needed for A.3 and for re-sync (A.6).

### A.3 Wiring Relations

Once every page exists:

1. For each module with `prerequisites`, set its Prerequisites relation
   property to the Notion page IDs corresponding to those prerequisite
   module IDs (via the `id -> page ID` map from A.2).
2. For each module with a non-null `parent_id`, set its Parent module
   relation to the parent's Notion page.

This two-pass approach (create-then-link) is necessary because Notion
relations reference existing pages by ID -- there's no forward-reference.

### A.4 Setting Up the Nine Dashboard Views

The Dashboard's nine views (see `assets/dashboard.template.md`) map onto
native Notion database views. Create these views on the database:

| Dashboard view | Notion view type | Configuration |
|---|---|---|
| 1. Roadmap List | Table or List | Default sort: creation order (matches hierarchical order from A.2). Optionally group by Parent module. |
| 2. Kanban | Board | Group by Status (Locked / Available / In Progress / Completed) |
| 3. Timeline | Table or List | Sorted in hierarchical order; show Estimated Effort column. Notion's Timeline view requires date properties, which this schema deliberately doesn't have (effort is free-text and not scheduled to calendar dates) -- a Table sorted by hierarchical order is the closest equivalent. If the user wants calendar-based scheduling, that's a separate request: it would mean adding explicit date properties and computing them, which should be discussed with the user rather than assumed. |
| 4. Priority | Board or Table | Group by Priority (high / medium / low) |
| 5. Milestones | Table | Filter: Is Milestone = true |
| 6. Dependency | -- | Notion has no native graph view. Show the Prerequisites relation column in Table view so links are visible, but treat the Mermaid diagram in `dashboard.md` (from `render_dependency_view`) as the primary dependency visualization. Mermaid code blocks can be pasted into a Notion code block (won't render as a diagram) or a "Code" embed depending on workspace settings -- mention this limitation to the user rather than working around it. |
| 7. Available Tasks | Table or Board | Filter: Status = Available |
| 8. Advanced Topics | Table | Filter: Category = advanced |
| 9. Optional Topics | Table | Filter: Category = optional |

### A.5 Page Body Content

For each module's page body, add the same content `render_plan.py` puts into
its markdown section (learning objectives, deep-understanding concepts,
common mistakes, expected competence, industry expectations, mastery goals,
evaluation, real-world competence, resources, notes), translated to Notion
blocks (headings + bulleted lists). This keeps the page body equivalent to
the Detailed Learning Plan entry for that module -- don't invent additional
structure beyond what the schema/template already define.

### A.6 Re-syncing After Updates

`learning-plan.json` remains canonical. After `scripts/update_progress.py`
runs (or any manual edit to the JSON):

1. Re-read `learning-plan.json`.
2. For each module, look up its existing Notion page via the ID property
   (don't recreate pages -- match on `id`).
3. Update changed properties (typically Status, and anything else that
   changed) on the existing page.
4. If new modules were added, create new pages for them (A.2) and wire their
   relations (A.3); existing pages/relations don't need to be touched unless
   their own fields changed.

Never treat edits made directly in Notion as authoritative -- if the user
has been updating status in Notion instead of via `update_progress.py`, ask
which direction should win before overwriting, and consider reading the
Notion statuses back into `learning-plan.json` as the resolution.

---

## Path B: No Notion MCP (Always Available)

This path requires nothing beyond `scripts/render_plan.py` and
`scripts/render_dashboard.py`, which are always run regardless of Notion
availability.

### B.1 Markdown Dashboard (primary fallback)

`dashboard.md` (from `render_dashboard.py`) is fully self-contained: all nine
views, including the Mermaid dependency graph, render directly in any
markdown viewer -- GitHub, Obsidian, VS Code, or pasted into a Notion page
(Notion renders pasted Mermaid code blocks as diagrams in most workspaces).
This alone satisfies the dual-output requirement with zero setup.

### B.2 Notion-Importable CSV (optional)

`render_dashboard.py <plan.json> --notion-csv dashboard.csv` produces a CSV
with columns: Title, ID, Status, Category, Sequencing, Priority, Skippable,
Is Milestone, Estimated Effort, Prerequisites, Parent. The user can import
this into Notion (Import > CSV) to get a starting database.

**Limitations of CSV import** (tell the user these up front):
- Notion creates all imported columns as text/select properties. Prerequisites
  and Parent will be **plain text (titles), not relations** -- Notion's CSV
  import doesn't create relation properties automatically. If the user wants
  true relations and dependency-aware views, they'd need to convert these
  columns to relation properties manually afterward, which is a manual Notion
  UI step outside this skill's scope.
- Row order in the CSV follows the same hierarchical order as the other
  artifacts, but Notion may not preserve this as a persistent sort -- the
  user can re-sort manually after import.
- After import, the view configurations in A.4 can still be created manually
  in the Notion UI (they don't require the relation properties to exist,
  except for the Dependency view's relation column).

### B.3 Recommendation

For most users without active Notion MCP access, `dashboard.md` alone is
sufficient and stays perfectly in sync (it's regenerated from
`learning-plan.json` every time). Offer the CSV only if the user specifically
wants a Notion database to track progress in Notion's UI.

---

## General Rule

Regardless of path: **`learning-plan.json` is the only thing that should be
hand-edited or updated via `scripts/update_progress.py`.** Both
`learning-plan.md` and `dashboard.md` (and any Notion database) are
generated/synced outputs. After any change to the plan, re-run:

```
python3 scripts/render_plan.py <plan.json>
python3 scripts/render_dashboard.py <plan.json>
```

and, if Path A is in use, re-sync the Notion database (A.6).
