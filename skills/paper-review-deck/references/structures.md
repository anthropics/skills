# Slide Structures

## Single mode (10 sections)
1. Title — paper title, authors, venue/year, presenter
2. Outline
3. Background & Motivation
4. Problem Definition — limitations of prior work
5. Proposed Method — core idea + 1 key equation
   - 5-2 Implementation — **reproduction results** from running the official code (reproduced vs paper table, plots). Not code excerpts
6. Experiments — data, baselines, main results
   - 6-2 Demo (when a demo video exists)
7. Contributions — 3-line summary
8. Limitations & Critique — Step 3 output
9. Relevance — connection to the Step 0 talk context (study group, research, class). Omit if there is no context
10. References / Appendix — paper, reference links, equation derivations, code excerpts (only when needed)

## Bundle mode (2–5 papers)
1. Title — topic title
2. Outline
3. Common Background & Problem — the problem the papers solve in common
4. Landscape — timeline/lineage diagram of how the papers relate + introduction of the comparison axes
5. Paper-by-Paper — 2–3 slides per paper, same template for every paper
   - a. One-line core idea + architecture figure
   - b. Core of the method (1 equation) + **reproduction/implementation results** (reproduction plot, reproduced vs paper table; a Repro box if it could not be run)
   - c. 1 representative result (table/chart) + 1-line limitation
   - d. Demo (when a video exists) — before/after videos side by side
6. Comparison — comparison table + shared-benchmark chart (only when a shared benchmark exists)
7. Common Limitations & Open Problems
8. Summary — one key line per paper + the overall arc (what evolved, and how)
9. References / Appendix

Bundle mode principles:
- Per-paper slides keep the same layout, figure position and title format, and carry a `[abbr]` tag at the start of the title. This lets the audience compare papers by looking at the same spot.
- Numbers that cannot be compared because datasets or experimental setups differ are marked "not comparable" in the comparison table and are not placed side by side. Putting numbers from different conditions next to each other invites false rankings.

## Content principles (common)
- 1 key equation + a one-line interpretation only. Derivations go to the Appendix
- Analogy before equation, intuition first. Match depth to the Step 0 audience background
- Keep phrases to one line wherever possible
- Code does not go in the main body of the slides. Implementation is shown as results from running it
