# Response Risk Checklist

Audit the full response package.

## Severity

| Level | Typical failure | Required action |
|---|---|---|
| High | Defensive tone, fabricated data/completion, ignored comment | Stop; correct or block the row |
| Medium | Missing proof, evidence mismatch, vague action | Verify the change |
| Low | Grammar, units, labels, format | Polish after technical checks |

## High-Risk Checks

**Defensive tone.** Flag attacks or `obviously`, `clearly`,
`as already stated`, `wrong`, and `misunderstood`. Replace blame:

- `The reviewer is wrong` -> `We respectfully clarify, based on [evidence], that...`
- `Obviously, the data show` -> `The supplied data in [figure/table] indicate...`
- `It is impossible` -> `This test is constrained by [verified reason]; we therefore...`

**Fabricated or unsupported completion.** Verify the file and location for
each claimed experiment, figure, table, citation, or revision. If absent, use
`AUTHOR_INPUT_NEEDED`, set `author_input_needed=true`, leave `revision_proof`
empty, and keep status `blocked` or `drafted`.

**Compound-comment silent drop.** Split each comment into atomic concerns and
map every question, request, and criticism to an action. Keep unanswered
subparts as explicit blocked rows.

## Medium-Risk Checks

**Revision proof.** A completed-change claim requires verified section,
paragraph, figure, table, or line-range proof. Placeholders, proposed
locations, and unsupplied tracked-change locations are not proof.

**Evidence consistency.** Cross-check values, units, trends, sample counts,
tests, labels, and claim strength across response, manuscript, data, and
captions. Resolve contradictions before release.

## Concise Language Replacements

| Avoid | Use |
|---|---|
| `We have revised accordingly` | `Revision status/location: AUTHOR_INPUT_NEEDED` |
| `We will do this later` | `Proposed/limited because [verified reason]` |
| `The reviewer misunderstood` | `The original wording may have been unclear` |
| `The result proves` | `The supplied evidence supports/indicates` |

## Final Preflight

- [ ] Preserve every original reviewer comment verbatim in its stable row; map each compound subpart.
- [ ] Tone is professional and free of defensive wording.
- [ ] Completion claims have evidence and verified revision proof.
- [ ] Missing experiments, images, text, or locations use `AUTHOR_INPUT_NEEDED`.
- [ ] Response/manuscript evidence, values, units, labels, and claims agree.
- [ ] Placeholders and unresolved author inputs remain visible.
- [ ] Technical/proof checks pass before language polishing.
