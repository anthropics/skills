# Journal: Generic materials journal (default) — writing

Use this when the target journal is undecided, not in the dedicated list, or when the user has not yet named a venue. This is the `default` value of the `journal_family` axis.

## Audience and scope

Generic materials-science journals (Elsevier, Springer, Wiley, T&F materials titles) share a common baseline: experimental papers with both performance and mechanism evidence, standard-cited methods, and statistical reporting. Once the user names a specific journal, switch to that journal's fragment for venue-specific limits and desk-rejection patterns.

## Drafting priorities

- **Experimental papers are the default expectation.** Lead with the material system, the property tested, and the mechanism evidence.
- **Performance and mechanism are both required.** Performance without mechanism reads as incomplete; mechanism without performance reads as speculative. Pair them.
- **Cite the test standard for every property.** ASTM, EN, ISO, GB/T, JIS — unnamed methods weaken reproducibility and invite reviewer pushback.
- **Statistical reporting is expected.** Mean ± SD (or SE), replicate count, and the test used. `Significant` only with a stated test and p-value.
- **Foreground the comparator.** Improvement needs a named baseline material or mix.

## Word and figure budget (research article)

Most materials journals sit in the 6,000–10,000-word band with no hard figure cap. Plan a balanced budget:

| Section | Suggested budget |
|---|---|
| Introduction | ~1,000 |
| Methods | ~1,800 |
| Results & Discussion | ~3,500 |
| Conclusion | ~500 |

Adjust toward Methods for methods-heavy papers; toward Results & Discussion for performance-rich papers.

## When to switch to a dedicated fragment

Ask the user for the target journal early. If they name one of the following, switch the `journal_family` axis:

- **CBM** — Construction and Building Materials → `static/fragments/journal/cbm.md`
- **CCC** — Cement and Concrete Composites → `static/fragments/journal/ccc.md`
- **RMPD / IJPE** — Road Materials and Pavement Design / International Journal of Pavement Engineering → `static/fragments/journal/rmpd.md`
- **JBE** — Journal of Building Engineering → `static/fragments/journal/jbe.md`

If the named journal is not in this list, keep using this generic fragment and note the venue so its specific limits can be checked before submission.

## Pre-drafting checklist

- [ ] Is the target journal named? If yes, is the correct fragment loaded?
- [ ] Is every property backed by a cited test standard?
- [ ] Is every mechanism claim backed by characterization evidence?
- [ ] Is every improvement claim backed by a named comparator and statistics?
