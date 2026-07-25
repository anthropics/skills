# Continuous Discovery Canon

The method layer behind `discovery_cadence_tracker.py` and `ost_linter.py`. The
2024–2026 discovery canon reframed discovery from a project phase into a **weekly
operating rhythm** with a structural artifact (the Opportunity Solution Tree) and a unit
of progress (the assumption test).

## The weekly habit (Torres)

Teresa Torres' definition of continuous discovery: the product trio (PM, designer,
engineer) has **at least weekly touchpoints with customers**, in pursuit of a desired
**outcome**, conducting **small research activities** (interviews, assumption tests).
Corollaries the tracker scores:

- **Cadence, not volume**: 4 interviews in one week then silence for a month is a broken
  habit — hence the streak (30 pts) and week-coverage (30 pts) components.
- **Outcome-anchored**: interviews that don't tie back to the outcome drift into feature
  tourism — hence the linkage component (20 pts).
- **Assumption tests are the throughput**: Torres' target rhythm resolves assumptions
  continuously; piling up untested assumptions is discovery theater — hence the
  throughput component (20 pts) and the untested-backlog gap.

## The Opportunity Solution Tree (why each lint rule exists)

- **O1 — one measurable outcome root**: the tree hangs from exactly one outcome, stated
  with a metric and target. Multiple outcomes = multiple trees.
- **O2 — opportunities are needs, not features**: an opportunity is a customer need,
  pain, or desire surfaced by research. "Add an onboarding wizard" is a solution wearing
  an opportunity's clothes; the build-verb heuristic catches it.
- **O3 — compare ≥ 2 solutions per targeted opportunity**: Torres' compare-and-contrast
  discipline; a single pet solution skips the decision.
- **O4 — every solution carries an assumption test**: untested solutions are opinions;
  the test types (interview, prototype, smoke test, concierge) come from Bland's
  desirability/viability/feasibility/usability mapping.
- **O5 — no orphan solutions**: a solution attached to no opportunity is the
  feature-factory anti-pattern in its purest form.

## Assumption mapping & test sequencing (Bland)

Rank assumptions by **importance × evidence-weakness** and test the riskiest first
(leap-of-faith assumptions). Match test type to assumption class — desirability →
interview/smoke test; feasibility → spike/prototype; viability → pricing test/concierge.
This is `product-discovery/scripts/assumption_mapper.py`'s scoring model; the tracker's
untested-backlog gap feeds it.

## JTBD switch interviews (Moesta)

When interviews need depth, run the switch interview: reconstruct a real past purchase
timeline (first thought → passive looking → active looking → decision) and code the four
forces — push of the current situation, pull of the new solution, anxiety of the new,
habit of the present. Progress happens when push + pull outweigh anxiety + habit.

## Story mapping (Patton)

The bridge from a validated opportunity to a sliced backlog: backbone of activities
left-to-right, stories vertically, release slices horizontally — each slice an
end-to-end walking skeleton, never a vertical feature column.

## Sources

1. Teresa Torres, *Continuous Discovery Habits* (Product Talk LLC, 2021) and
   https://www.producttalk.org/opportunity-solution-trees/
2. David J. Bland & Alexander Osterwalder, *Testing Business Ideas* (Wiley, 2019)
3. Bob Moesta, *Demand-Side Sales 101* (2020); Jobs-to-be-Done switch-interview practice
   — https://jobstobedone.org/
4. Jeff Patton, *User Story Mapping* (O'Reilly, 2014)
5. Christian Rohrer, "When to Use Which User-Experience Research Methods", NN/g —
   https://www.nngroup.com/articles/which-ux-research-methods/
6. Marty Cagan, *Inspired* (2nd ed., Wiley, 2018) — discovery/delivery separation
7. Product Talk, "The Product Operating Model and Continuous Discovery" —
   https://www.producttalk.org/the-product-operating-model/
