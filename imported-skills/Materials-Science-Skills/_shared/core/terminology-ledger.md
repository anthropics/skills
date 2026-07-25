# Terminology Ledger

A manuscript must use one name for one thing. The same material, modifier, test method, standard, or concept must not drift across shifting names, spellings, or capitalisation. Reviewers read inconsistent terminology as careless work, and a term that changes between sections forces the reader to re-learn it.

Build the ledger **before** drafting or polishing prose, and treat it as the single source of truth for the rest of the job. Consistency against a standard is impossible if the standard was never written down.

## 1. Build the ledger on first contact

When you first receive a manuscript, draft, or set of notes, extract every recurring domain term into a ledger before editing any prose:

- materials, binders, modifiers, additives, fibers, fillers (e.g., "waterborne epoxy modified emulsified asphalt" vs "WEMEA" vs "epoxy-asphalt emulsion")
- test methods and standards (e.g., "GB/T 16777" vs "GB16777" vs "the Chinese standard")
- units and symbols (e.g., "MPa" vs "Mpa" vs "mega-pascal")
- abbreviations and acronyms, each with its full form
- key concepts the paper defines or repeatedly relies on

For each term, record its canonical form, its first-use expansion (for abbreviations), and any variants already present in the source.

## 2. Present the ledger to the user

Show a compact table before or alongside the first output:

| Canonical term | First-use definition | Variants seen in source | Decision |
|---|---|---|---|
| waterborne epoxy modified emulsified asphalt | waterborne epoxy modified emulsified asphalt (WEMEA) | "epoxy-asphalt emulsion", "WMEA", "modified asphalt" | spell out once, then use "WEMEA" |
| yttria-stabilized zirconia | yttria-stabilized zirconia (YSZ) | "zirconia", "ZrO2-Y2O3", "YSZ ceramic" | spell out once, then use "YSZ" |
| 7075-T6 aluminum alloy | 7075-T6 aluminum alloy | "AA7075-T6", "Al-7075", "7075 Al alloy" | use "7075-T6 aluminum alloy" |

Flag every collision explicitly: the same concept under different names, or one name reused for two different concepts. Ask the user to confirm the canonical choice only when the decision is genuinely ambiguous or domain-sensitive. Otherwise adopt the form the source uses most often and state that choice.

## 3. Lock and enforce

Once set, the ledger is fixed for the whole job:

- Use only canonical forms in every output. Do not introduce synonyms to vary the prose. Terminology consistency outranks lexical variety in scientific writing.
- Define each abbreviation once, at first use, then use the short form.
- Keep units, symbols, and notation identical across every section.
- When drafting or polishing a later section, reference the ledger built from the earlier sections instead of re-deciding term by term.
- If the user later renames a term, change every occurrence in the manuscript, not just the current passage, and update the ledger.

## 4. Do not invent terms

Do not coin new names for the author's materials, methods, or concepts. If a term is missing, undefined, or used inconsistently in ways you cannot resolve from the source, ask the user or flag it. Never fill the gap with a guessed name.

## 5. Chinese-English mapping

For Chinese-authored manuscripts, maintain a bilingual column:

| Chinese | English canonical | Notes |
|---|---|---|
| 乳化沥青 | emulsified asphalt | not "emulsified bitumen" (unless UK journal) |
| 粘层 | tack coat | not "bonding layer" or "adhesive layer" |
| 固化剂 | curing agent | not "hardener" (avoid ambiguity) |
| 针入度 | penetration | unit: 0.1 mm |
| 氧化钇稳定氧化锆 | yttria-stabilized zirconia (YSZ) | ceramics family; not "zirconia ceramic" |
| 固溶强化 | solid-solution strengthening | metals family; not "solution hardening" |

## Initializing the ledger from an experiment record

If the user supplies an `experiment-record.yaml`, seed the terminology ledger from its `terminology` block before reading any manuscript text:

1. For each entry, use `canonical` as the authoritative term.
2. If `abbreviation` is present, record the first-use expansion as `canonical (abbreviation)`.
3. Add `variants` as terms that must be normalized to `canonical`.
4. Treat `unit` fields in `response_variables`, `factors`, and `terminology` as locked notation; do not allow drift (e.g., `MPa` vs `Mpa`).

Present the seeded ledger to the user in the usual table format and ask only if conflicts exist between the record and the source text.
