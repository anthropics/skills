# Common model and workbook runtime

Read when constructing the complete JSON model or producing its workbook.
Domain references define scope and domain-specific records; use these local
tools for the shared interchange, rendering and validation mechanics.

## Local resources

- [model.py](../scripts/model.py) validates all eleven `EstimateModel` sections
  and their required record keys. Retain empty arrays and complete metadata.
- [workbook-contract.json](../scripts/workbook-contract.json) defines the twelve
  sheets, task columns, scenarios and publication checks. Keep every sheet;
  explain irrelevant sections with `Non applicable` rather than removing them.
- [workbook_builder.py](../scripts/workbook_builder.py) produces the editable
  XLSX with tables, named ranges and formulas; numeric inputs remain numbers.
- [diagram_renderer.py](../scripts/diagram_renderer.py) and
  [icon-policy.json](../scripts/icon-policy.json) render explicit inventory
  nodes and evidenced edges with labelled neutral symbols by default.
- [recalculate.py](../scripts/recalculate.py) recalculates formulas and checks
  caches; [workbook_validator.py](../scripts/workbook_validator.py) independently
  checks the resulting workbook without repairing or recalculating it.
- [LICENSE](../LICENSE) supplies the full methodology licence. Provider artwork
  remains a separate optional runtime input with verified provenance and terms.

## Calling the local package

Requires Python 3.11+, `openpyxl` 3.1+ and Pillow. Native Excel or LibreOffice is
optional unless the requested gate requires native opening. Resolve paths from
the installed skill directory; add that directory to Python's import path or
run the consuming driver there. Import `scripts` as a package so the shared
modules' relative imports work. These are function interfaces, not standalone
CLI entrypoints:

```python
from pathlib import Path
from scripts.model import load_model
from scripts.workbook_builder import build_workbook
from scripts.diagram_renderer import render_diagram
from scripts.recalculate import recalculate
from scripts.workbook_validator import validate_workbook

model = load_model(Path("estimate-model.json"))
workbook = build_workbook(model, Path("estimate.xlsx"), architecture=graph)
calculation = recalculate(workbook)
report = validate_workbook(workbook, asserted_totals=numeric_claims,
                           diagram_inventory_ids=inventory_ids)
```

`graph` contains `nodes` with inventory `id`, plus optional `component`,
`environment`, `zone`, `provider`, `icon`; `edges` carry `id`, `source`, `target`
and optional `label`. Node IDs match inventory exactly. Omitting architecture
draws inventory nodes without inferring connections. `render_diagram(graph,
svg: Path, png: Path, icon_pack: Path | None = None)` returns IDs, output hashes,
provenance and warnings; the builder embeds the PNG and manifest.

Keep JH low/likely/high finite, non-negative and ordered, with resolved task
dependencies. Preserve `Economique`, `Standard`, `Resilient`; required unique
assumptions are `scenario_global`, `taux_journalier`, `mois_par_an`. Add editable
`heures_par_jh` with default 8. Distinguish one-off Build JH, Run JH/month,
cloud OPEX and sourced non-cloud OPEX. Missing prices stay `A chiffrer` in
notes/assumptions and leave affected totals incomplete, never placeholder zero.

Inspect calculation `ok`, `engine`, `native_opened`, cache counts, errors and
warnings. Disclose the calibrated Python fallback and its native-opening limit.
Reopen formulas and cached values. `numeric_claims` maps `sheet!cell` to each
claimed number; `inventory_ids` comes from the final diagram. Inspect report
`ok`, errors, counts and grouped cost totals; omitted assertions are unchecked.
Independently check flow evidence, source facts and extra domain calculations.

## Distribution integrity

The local `manifest.json` hashes delivered files except itself and build debris;
its `generated_files` list identifies canonical shared copies. After an authored
resource changes, regenerate the manifest before bundling. A divergent shared
copy requires review: the synchronizer will only update a previous generated
version whose current bytes match its prior manifest. Hashes establish integrity,
not trusted authorship. Deliver the complete skill directory with the licence,
matching manifest and no build artifacts; never require a sibling skill's files.
