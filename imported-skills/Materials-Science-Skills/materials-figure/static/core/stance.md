# Default operating stance

## Materials science priorities

- Start by classifying the requested figure into one of the archetypes: `quantitative grid`, `schematic-led composite`, `image plate + quant`, `review heatmap`, `method/test matrix`, or `graphical abstract`.
- Prefer one **hero panel** plus subordinate evidence panels over filling the canvas with equal-sized subplots.
- If the user asks for a single chart, still identify its role in the manuscript claim: discovery, mechanism, validation, comparison, robustness, or materials-system relevance.
- Keep the background white for plots and diagrams; switch to black only for microscopy / volume-rendering image plates.
- Prefer direct labels over legends when categories are spatially fixed or the legend would force unnecessary eye travel.
- Keep one restrained palette per figure: use materials-domain semantic colors when meaningful (e.g. asphalt dark gray, cement light gray, ceramics warm orange, metals cool blue, polymers green), and reserve high-saturation colors for signal emphasis.
- Treat statistics, `n`, error-bar definitions, source-data traceability, and image-integrity notes as part of the figure, not as optional caption cleanup.

## Reviewer-safe defaults

- Show measured evidence and inferred links with different visual encodings.
- Use captions that state what the data support and what they do not prove.
- For SEM/TEM/fluorescence panels, preserve scale bars and image provenance.
- For FTIR/XRD/TG/DSR spectra, do not overstate chemistry or field durability from a single evidence layer.
- For review figures, link panels to a table-system row or `source_map.json` anchor when available.
- Deliver figure packages with source data, script, exports, caption, QA report, and asset manifest when the user asks for a journal-ready figure.

## When to load this skill

- Python figures for **papers, slides, or reports** targeting materials science and engineering journals and publications.
- Requests involving **XRD/FTIR/TG/DTG spectra, SEM/TEM image plates, performance curves, mechanism schematics, multi-panel grids**, or **PDF/SVG/high-DPI** output.
- Any mention of "materials figure", "construction materials plot", "XRD pattern", "FTIR spectrum", "performance curve", "mechanism schematic", "review evidence map", or "论文配图、材料科学图、土木材料图".
- Requests to improve a figure's logic, aesthetics, panel layout, figure legend, export quality, or journal-readiness.

## When NOT to load

- Plotly, Altair, Bokeh, or other interactive/web-first plotting.
- EDA-only plots without a publication target.
- Primary workflow is 3D, GIS, or non-scientific illustration tooling.
- Illustrator / Figma–first layout.

## User-facing privacy rule

Do not disclose private local paths, private filenames, chat-attachment names, internal reference filenames, template identifiers, or the provenance of private working materials in user-facing replies, generated code comments, figure legends, reports, or manuscript text. Use generic descriptions such as "the provided template collection", "a private working draft", or "the internal figure contract". Only reveal an exact path or source file when the user explicitly asks for that audit trail.

## See also

- [contract.md](contract.md) — the eight-point figure contract, conditional materials knowledge validation, and multi-figure storyboard gate.
- [workflow.md](workflow.md) — the 8-step figure workflow (storyboard → contract → materials validation → backend → source data → plotting → package → QA/return).
