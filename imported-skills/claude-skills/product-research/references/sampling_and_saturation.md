# Sampling and Saturation

Reference for how many participants. Pairs with `saturation_planner.py`.

## Usability: the "5 users" result

Nielsen and Landauer's model says the proportion of usability problems found with n users is 1 − (1 − p)ⁿ, where p is the average probability that a single user surfaces a given problem (~0.31 in their data). At n = 5, that is ~85% of problems — hence "test with 5 users." Two crucial caveats the planner enforces:

1. **Per segment.** The 5-user result holds *within a homogeneous user group*. If you have distinct segments that behave differently, you need ~5 per segment.
2. **Problems, not rates.** A small-n usability test finds *whether* a problem exists; it cannot estimate the *prevalence* of that problem in the population. Never report "60% of users struggled" from a 5-person test.

Faulkner (2003) showed real variance: while the average across many 5-person samples is ~85%, individual 5-person runs ranged from ~55% to 100%. When stakes or heterogeneity are high, run more.

## Qualitative: thematic saturation

For interview-based thematic research, Guest, Bunce & Johnson (2006) found that **saturation** — the point where new interviews stop yielding new themes — typically occurs by ~12 interviews in a homogeneous group, with the basic elements present by ~6. Saturation is **observed, not guaranteed**: track the new-theme rate and stop when it flattens, rather than committing to a fixed n blindly. Heterogeneous populations need more, and per-group saturation applies just as in usability.

## Reporting confidence honestly

The planner attaches a confidence label (LOW / MODERATE / MODERATE-HIGH) and explicit limits to every plan, because the failure mode in product research is not too-small samples per se — it is **over-claiming** from whatever sample you ran. State the method, the n, and what the method can and cannot support.

## Sources

1. Nielsen, J., & Landauer, T., *A mathematical model of the finding of usability problems* — INTERCHI 1993.
2. Nielsen, J., *Why You Only Need to Test with 5 Users* — NN/g (2000).
3. Faulkner, L., *Beyond the five-user assumption* — Behavior Research Methods 2003;35:379-383.
4. Guest, G., Bunce, A., & Johnson, L., *How many interviews are enough?* — Field Methods 2006;18:59-82.
5. Braun, V., & Clarke, V., *Using thematic analysis in psychology* — Qual Res Psychol 2006;3:77-101.
6. Sauro, J., & Lewis, J., *Quantifying the User Experience*, 2nd ed. (2016) — confidence intervals for small samples.
