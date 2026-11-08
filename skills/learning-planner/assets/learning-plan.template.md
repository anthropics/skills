<!--
  Template for the Detailed Learning Plan, used by scripts/render_plan.py.

  This file has two sections, delimited by the HTML comment markers below:
    - TEMPLATE:HEADER -- rendered once, with overall roadmap metadata
    - TEMPLATE:MODULE -- rendered once per module, in hierarchical order
                         (top-level modules first, each followed by its
                         submodules, recursively)

  Placeholders use {{name}} syntax (double curly braces). This deliberately
  avoids Python's string.Template ($name) syntax, since learning-plan content
  may legitimately contain literal '$' (prices, currency) or single '{'/'}'
  (Mermaid diagram syntax in the dashboard template), which would collide
  with $-based or .format()-based substitution.

  Fields whose schema type is an array (e.g. learning_objectives) are
  pre-rendered into a markdown bullet list (or "_None specified._" if
  empty) by render_plan.py before substitution -- so {{learning_objectives_list}}
  expands to a multi-line bullet block, not a raw JSON array.

  Do not remove or reorder the section markers -- render_plan.py splits the
  file on them. Everything outside the two marked sections (including this
  comment) is ignored.
-->

<!-- TEMPLATE:HEADER -->
# {{plan_title}}

**Discipline:** {{discipline}}
**Goal type:** {{goal_type}}
**Target outcome:** {{target_outcome}}
**Current level:** {{current_level}}
**Timeline:** {{timeline}}
**Created:** {{created_date}} | **Last updated:** {{last_updated}}

{{roadmap_notes}}

---

## Module Index

{{module_index}}

---
<!-- END:TEMPLATE:HEADER -->

<!-- TEMPLATE:MODULE -->
{{heading_marker}} {{title}}{{milestone_marker}}

- **ID:** `{{id}}`
- **Status:** {{status}}
- **Category:** {{category}} | **Sequencing:** {{sequencing}} | **Priority:** {{priority}} | **Skippable:** {{skippable}}
- **Estimated effort:** {{estimated_effort}}
- **Prerequisites:** {{prerequisites_list}}

#### What to Learn

{{learning_objectives_list}}

#### Concepts Requiring Deep Understanding

{{deep_understanding_concepts_list}}

#### Common Mistakes

{{common_mistakes_list}}

#### Expected Competence

{{expected_competence}}

#### Industry Expectations

{{industry_expectations}}

#### Mastery Goals

{{mastery_goals_list}}

#### Evaluation

{{evaluation_list}}

#### Real-World Competence

{{real_world_competence_list}}

#### Resources

{{resources_list}}
{{module_notes_section}}
---
<!-- END:TEMPLATE:MODULE -->
