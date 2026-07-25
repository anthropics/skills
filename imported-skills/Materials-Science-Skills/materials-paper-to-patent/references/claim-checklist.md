# Claims Self-Check Checklist (Civil Materials)

A pre-validation checklist for claims. Run through every claim before
calling `validate_patent_claims.py`. Each item is YES / NO / NA.

## Independent claim

- [ ] Starts with "一种 X" or "X 的 Y 方法"
- [ ] Contains "其特征在于" (or equivalent transitional phrase)
- [ ] Lists all essential technical features after the transitional phrase
- [ ] Essential features trace to source evidence (P/E/F/C IDs)
- [ ] Does not contain future-tense, aspirational, or marketing language
- [ ] Method claims end with a concrete domain output (e.g., 抗压强度 X MPa)
- [ ] No pure functional limitation ("用于 X 的装置")
- [ ] For process-material: lists raw materials, steps, conditions, ranges, units

## Dependent claims

- [ ] References a single earlier claim by number
- [ ] Numbering is continuous (no gaps)
- [ ] Adds concrete technical features (composition, parameter, structure)
- [ ] Does not reference a non-existent claim number

## Composition claims

- [ ] Every range has a unit (wt%, vol%, mol%, mm, nm, °C, h, MPa, GPa)
- [ ] Range endpoints are from source data points
- [ ] Sum of constituent fractions makes physical sense
- [ ] "其余为 ..."  used when the composition is partially specified

## Method claims

- [ ] Steps are in the order they are actually performed
- [ ] Each step has measurable parameters where applicable
- [ ] Final step names a concrete technical output

## Cross-document consistency

- [ ] Every term used in claims appears in the specification
- [ ] Figure numbers match between specification and abstract
- [ ] Units are consistent (no MPa vs 兆帕混用)
- [ ] Formula symbols are defined in the specification

## Anti-patterns

- [ ] No "商业方法" / "商业模式" / pure business method language
- [ ] No "[TO CONFIRM]" markers in formal claims
- [ ] No placeholder ranges like "若干" or "适当"
- [ ] No "大约/约" used to extend an unsupported range
