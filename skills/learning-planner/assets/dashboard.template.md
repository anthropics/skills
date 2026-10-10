<!--
  Template for the Dashboard, used by scripts/render_dashboard.py.

  Unlike learning-plan.template.md (which is filled in once per module),
  this template is filled in ONCE: each {{..._view}} placeholder is a
  complete, pre-rendered markdown block computed by render_dashboard.py
  from learning-plan.json. The template only controls the overall
  arrangement, headings, and ordering of the nine views.

  Placeholders use {{name}} syntax (double curly braces) -- see the note in
  learning-plan.template.md for why this is used instead of $-substitution.

  Do not remove or reorder the section markers -- render_dashboard.py
  extracts the body via TEMPLATE:DASHBOARD / END:TEMPLATE:DASHBOARD.
-->

<!-- TEMPLATE:DASHBOARD -->
# {{plan_title}} -- Dashboard

_Generated from learning-plan.json. Last updated: {{last_updated}}._

## Progress Summary

{{progress_summary}}

---

## 1. Roadmap List View

Hierarchical view of all modules and submodules with status, category, and priority.

{{roadmap_list_view}}

---

## 2. Kanban View

{{kanban_view}}

---

## 3. Timeline View

Modules in suggested learning order with estimated effort. Useful for pacing
against a deadline (effort estimates are free-text and not summed/scheduled
automatically -- see references/intake-workflows.md for deadline planning).

{{timeline_view}}

---

## 4. Priority View

{{priority_view}}

---

## 5. Milestones View

{{milestones_view}}

---

## 6. Dependency View

{{dependency_view}}

---

## 7. Available Tasks View

Modules whose prerequisites are fully satisfied and that are not yet started.
This is the "what can I work on next" view.

{{available_view}}

---

## 8. Advanced Topics View

{{advanced_view}}

---

## 9. Optional Topics View

{{optional_view}}
<!-- END:TEMPLATE:DASHBOARD -->
