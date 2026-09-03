# Triggering test cases

Phrases used to check that the `tubi-dashboard` skill fires when it should and stays quiet
when it shouldn't. Feed these to the skill-creator eval harness, or use them as a manual
smoke test after editing the `description`.

## Should trigger (positive)

1. "Build me a dashboard in our Tubi style."
2. "Make an HTML dashboard for the CDP time-to-Tubi data."
3. "Mock up a KPI view like our Tableau dashboards."
4. "Restyle this dashboard to match Tubi branding."
5. "Create a dashboard with filters, KPI cards, and a trend chart."
6. "Turn this notebook output into an interactive dashboard page."
7. "I need a dark-theme version of the engagement dashboard."
8. "Recreate this Tableau report as an HTML page in our house style."
9. "Give me a report page with delta tables and section headers, Tubi-branded."
10. "Build a shareable dashboard where clicking a bar filters the page."

## Should NOT trigger (negative)

1. "What's the median TTT for Priority titles?" (data question, not a dashboard build)
2. "Write a Word summary of these metrics." (docx skill)
3. "Make a slide deck from this report." (pptx skill)
4. "Clean up this spreadsheet and add a column." (xlsx skill)
5. "Explain what a Gini coefficient measures." (explanation)
6. "Fix the SQL in this query." (code task)
7. "Build a generic React dashboard component library." (not Tubi house style / not this shell)
8. "Design a marketing landing page." (not a data dashboard)

## Edge cases (judgment)

- "Make a chart of this data." → Prefer the skill only if they want a full dashboard/page; a single
  standalone chart may not need the shell. Ask if ambiguous.
- "Build a dashboard" with no Tubi/house-style cue, in a non-Tubi context → the skill still applies if
  the user is at Tubi and wants the branded look; otherwise confirm.

## How to run (skill-creator)

Load the `skill-creator` skill and point its eval/benchmark flow at this file to measure trigger
precision/recall and to tune the one-line `description` in `SKILL.md`. Re-run after any description edit.
