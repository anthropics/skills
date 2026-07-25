# Research Repository and Synthesis

Reference for turning observations into governed insights. Pairs with `insight_synthesizer.py`.

## Observation vs insight

The foundational discipline of ResearchOps is the distinction between an **observation** (a single piece of evidence — one participant did or said one thing) and an **insight** (a pattern that recurs across independent sources and carries an implication). Promoting an observation to an insight because it was vivid or confirmed a prior is the cardinal sin of synthesis. The synthesizer enforces a source threshold: a candidate supported by fewer than the threshold of distinct participants is labeled an ANECDOTE and is never promoted.

## Atomic research

Tomer Sharon's **atomic research** model (and the "Polaris" repository concept) decomposes research into reusable units: *Experiments → Facts (observations) → Insights → Recommendations*. Facts are tagged and stored so that insights can be traced back to evidence and reused across studies. The payoff is a repository where a claim can always be drilled down to the observations that support it — and where the same evidence can support future questions.

## Affinity mapping

The classic synthesis technique is affinity mapping: cluster observations into emergent themes bottom-up, then name the themes. The `insight_synthesizer.py` tool is a deterministic, tag-based proxy for this — it clusters by the codes you assign and ranks by cross-participant recurrence. The human still does the interpretive naming; the tool enforces the counting discipline.

## Repository governance and democratization

As organizations democratize research (PMs and designers running their own studies), the repository becomes the guardrail. Governance practices: a consistent tagging taxonomy, evidence linked to every insight, a confidence field, and a review step before an insight is marked "validated." Without governance, democratized research produces a pile of unsearchable anecdotes; with it, the repository compounds in value.

## Sources

1. Sharon, T., *Validating Product Ideas Through Lean User Research* (Rosenfeld, 2016) and the atomic-research / Polaris model.
2. ResearchOps Community, *Research Repositories* and *Democratization* working-group reports.
3. Braun, V., & Clarke, V., *Thematic Analysis: A Practical Guide* (Sage, 2022).
4. Beyer, H., & Holtzblatt, K., *Contextual Design* (1998) — affinity diagramming.
5. Dovetail / EnjoyHQ practitioner guides on insight repositories and tagging taxonomies.
6. Kaplan, K., *Taxonomy 101* and *Research Repositories* — Nielsen Norman Group.
