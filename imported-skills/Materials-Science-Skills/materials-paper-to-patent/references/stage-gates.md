# Patent Generation Workflow

Run all applicable stages in order. A later stage must not silently repair
missing evidence from an earlier stage.

## Stage 0 - Intake and risk flags

Record source files, deliverables, target jurisdiction (CNIPA invention),
publication status, known disclosure dates, and missing inventor facts.

Output: `work/00-intake.json`.

Gate: every input file identified; unknown facts explicitly marked.

## Stage 1 - Source map

Extract the entire substantive disclosure, not only the abstract. Assign
stable IDs to text blocks, equations, figures, and supplementary evidence.
Keep page, section, caption, file, or line locators.

Output: `work/01-source-map.json`.

Gate: method, implementation, experiments, formulas, and methodology figures
all inspected or marked unavailable.

## Stage 2 - Technical inventories

Create:

- terminology ledger with one canonical Chinese term per object;
- input-operation-output map;
- formula inventory with symbols and technical role;
- figure inventory distinguishing methodology figures from result charts;
- implementation-gap list.

Output: `work/02-technical-inventory.json`.

## Stage 3 - Evidence ledger

Convert candidate features into an evidence ledger. Assign support state,
source IDs, technical role, effect, and proposed destination.

Output: `work/03-evidence-ledger.json`.

Gate: no candidate essential feature is `unsupported`; every
`needs-confirmation` feature becomes an inventor question or is removed.

## Stage 4 - Invention concept and claim strategy

Write the one-sentence concept:

`technical problem -> cooperating technical means -> specific technical output/effect`

Select the principal protected object, essential feature chain, fallback
positions, and appropriate claim categories. Use `patent_kb.yaml` to align
with CNIPA examination conventions for the detected invention type.

Output: `work/04-claim-strategy.json`.

## Stage 5 - Claims

Draft the principal independent claim first. Then dependent claims in the
same technical order, then other supported categories. Create a claim-
feature map from every material limitation to evidence IDs.

Output:

- `work/05-claims.txt`;
- `work/05-claim-map.json`.

Gate: `scripts/audit_claims.py` has no ERROR; every formal claim has mapped
source support; no `[TO CONFIRM]` marker remains in formal claims;
`scripts/validate_patent_claims.py` returns 0 for the detected
`invention_type`.

## Stage 6 - Specification and figures

Draft the specification around the claims while adding implementation detail
from the source. Include core formulas, symbol definitions, alternatives,
figure descriptions, and embodiments. Request methodology figures from
`materials-figure` (do not generate charts inside this skill).

Output: `work/06-draft.json`.

Gate: every claimed term appears in the specification; every claim step is
explained; every figure is referenced; every core formula has editable-math
source and symbol definitions.

## Stage 7 - Abstract and package

Draft the abstract last. Keep terminology aligned with the principal claim.
Use the same main figure as the abstract figure and a specification figure.

Output: separate Chinese DOCX files, figures, structured JSON, and audit
reports under `outputs/`.

Gate: `scripts/validate_patent_draft.py` and
`scripts/build_patent_package.py` complete without errors.

## Stage 8 - Final review

Score evidence support, claim architecture, consistency, enablement,
technical-effect reasoning, formula coverage, and figure alignment. List
unresolved inventor questions and publication risks.

Gate: meet thresholds in `static/core/output-contract.md`; otherwise label
the package `incomplete draft`.
