# Civil Concrete Strengthening Example

A complete end-to-end example showing how to use `materials-paper-to-patent`
on a civil materials paper disclosure.

## Files

- `draft.json` — pre-populated structured draft.
- `flow-steps.json` — method steps for the main flowchart.

## Running it

```bash
cd plugins/materials-skills/skills/materials-paper-to-patent

# 1. Validate structure
python scripts/validate_patent_draft.py examples/civil-concrete-strengthening/draft.json

# 2. Civil claims content check
python scripts/validate_patent_claims.py examples/civil-concrete-strengthening/draft.json \
    --invention-type process-material

# 3. Audit claims text
python scripts/audit_claims.py work/05-claims.txt

# 4. Render the main flowchart
python scripts/render_flowchart_svg.py examples/civil-concrete-strengthening/flow-steps.json \
    --output outputs/patent_main_flowchart.svg

# 5. Build the full DOCX package
python scripts/build_patent_package.py examples/civil-concrete-strengthening/draft.json \
    --output-dir outputs --prefix patent
```

## What it demonstrates

- One independent product claim and one dependent claim narrowing the
  aggregate to crushed stone.
- Source IDs (`P001`, `P002`, `P003`) tagging the disclosure.
- A single main figure (flowchart) reused as abstract figure.
- Range with unit (w/b=0.30-0.40) and explicit concrete strength output
  (50-60 MPa).
- All four documents: claims, specification, abstract, abstract figure.
