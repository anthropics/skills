---
name: bill-of-quantities
description: Generate detailed Bill of Quantities (BoQ) from construction drawings and project specifications. Use this skill whenever users need to extract quantities from technical documentation, organize construction costs, create cost estimates, prepare project documentation for tendering, analyze construction materials and labor, or generate structured BoQ spreadsheets and reports. This includes scenarios with specifications, drawings, site details, or project scope documents.
compatibility: Python 3.7+, openpyxl or pandas for Excel generation (optional but recommended)
---

# Bill of Quantities Generator

Generate professional, structured Bill of Quantities from construction drawings, specifications, and project documentation. This skill extracts quantities, organizes items by section, calculates costs, and produces multiple output formats suitable for tendering, estimation, and project planning.

## Quick Start

When given construction project documentation (drawings, specs, site descriptions), your goal is to:

1. **Extract** all relevant construction items with descriptions and quantities
2. **Organize** items into standard BoQ sections (Preliminaries, Groundwork, Structures, Finishes, Services, etc.)
3. **Validate** quantities and cross-reference against source documents
4. **Generate** outputs in structured formats with cost breakdowns

## BoQ Section Structure

Use this standard classification (RICS-aligned):

| Section | Purpose | Examples |
|---------|---------|----------|
| **A. Preliminaries** | Site setup, temporary works | Mobilization, site offices, insurance, hoardings |
| **B. Groundwork** | Earthworks and foundations | Excavation, backfill, pile caps, concrete bases |
| **C. Structures** | Main construction elements | Framing, columns, beams, structural concrete |
| **D. Finishes** | Surface treatments | Plastering, painting, flooring, ceiling |
| **E. Services** | MEP systems | Electrical, plumbing, HVAC, fire protection |
| **F. External Works** | Site utilities | Paving, landscaping, drainage, boundary works |
| **G. Contingency & PC Sums** | Risk & provisional items | Contingency allowance, prime cost sums, day works |

## Extraction Methodology

### Step 1: Parse Source Documentation
When provided with project information, identify:
- **Type of input**: Specifications, drawings (visual description), site conditions, architectural/engineering details
- **Key information**: Item descriptions, dimensions, quantities, materials, unit specifications
- **Context clues**: Building type, location, scale, standards implied

### Step 2: Extract Quantities
For each construction element in the documentation:
- **Item description**: What is being constructed/installed?
- **Specification**: Materials, standards, quality requirements
- **Quantity**: Extract or calculate from dimensions
  - Linear items: Length in meters (m)
  - Area items: Area in square meters (m²)
  - Volume items: Volume in cubic meters (m³)
  - Count items: Number of units (No.)
- **Unit**: Standard construction units (m, m², m³, No., kg, etc.)

**Example extraction:**
```
Source: "2m high concrete block wall, 45m length"
Item: Concrete block wall (200mm thick, solid concrete blocks)
Dimension: 45m × 2m = 90 m²
Quantity: 90
Unit: m²
```

### Step 3: Validate & Flag Assumptions

As you extract, note:
- Missing information (flag as "Assumed from context")
- Ambiguities in specifications
- Items that require clarification
- Calculation basis (e.g., "based on building footprint", "per drawing detail")

Create an **Assumptions & Notes** section listing all assumptions made during extraction.

## Output Generation

### Output 1: Structured CSV/Excel Spreadsheet

Create a spreadsheet with these columns:

```
Section | Code | Item Description | Specification | Qty | Unit | Rate (optional) | Amount (optional) | Notes
```

**Requirements:**
- One row per line item
- Grouped by section (Preliminaries, Groundwork, etc.)
- Subtotals for each section
- **Grand Total** at bottom
- Include section headers for clarity
- Calculate totals if rates are provided

**Example structure:**
```
A. PRELIMINARIES
A.1  Site Mobilization         Full mobilization and demobilization  1     Item    [rate]    [amount]
A.2  Temporary Site Office     Prefab office with utilities          1     Item    [rate]    [amount]
--- SUBTOTAL A: 2 items ---

B. GROUNDWORK
B.1  Excavation (General)      Bulk excavation, all soil types      250    m³     [rate]    [amount]
B.2  Structural Concrete Base  Concrete bed, 150mm thick, C25        45     m²     [rate]    [amount]
--- SUBTOTAL B: 2 items ---
```

### Output 2: Markdown Summary Table

A condensed, human-readable table for documentation:

```markdown
## Bill of Quantities Summary

| Section | Item | Qty | Unit |
|---------|------|-----|------|
| Preliminaries | Site Mobilization | 1 | Item |
| Preliminaries | Temporary Office | 1 | Item |
| Groundwork | Excavation | 250 | m³ |
| Groundwork | Concrete Base | 45 | m² |
| **TOTAL** | **3 items** | **296 units** | **mixed** |
```

### Output 3: Detailed Analysis Report

Include:
- **Project Summary**: Building type, location, scope
- **Extraction Basis**: What source documents were used
- **BoQ Breakdown**: Total items by section
- **Quantity Totals**: Summary by unit type (m³, m², No., etc.)
- **Assumptions & Notes**: All assumptions and clarifications
- **Recommendations**: Items needing further detail or clarification

**Report template:**
```
# Bill of Quantities Analysis Report

## Project Summary
- Building Type: [type]
- Project Scope: [scope]
- Total Items: [count]
- Source Documents: [list sources]

## Quantity Breakdown by Section
- A. Preliminaries: X items
- B. Groundwork: X items
- C. Structures: X items
- D. Finishes: X items
- E. Services: X items
- F. External Works: X items

## Quantity Totals
- Concrete: XXX m³
- Excavation: XXX m³
- Structural Steel: XXX tonnes
- [other materials]: [qty] [unit]

## Key Assumptions
1. [assumption #1]
2. [assumption #2]
...

## Recommended Clarifications
- [item needing further detail]
```

## Best Practices

### Accuracy & Completeness
- **Cross-reference quantities**: Check that dimensions align with building scale
- **Catch duplicates**: Ensure items aren't double-counted across sections
- **Round sensibly**: Use appropriate precision (e.g., m² to nearest 1, volume to nearest 5)
- **Flag ambiguities**: Mark items where spec is unclear

### Organization
- **Logical grouping**: Keep related items in same section
- **Consistent descriptions**: Use standard terminology (not "stuff for walls", but "Brick/block walls")
- **Include specs**: Every item should have enough detail for a contractor to price it
- **Progressive detail**: General items first (A), then specific elements (B-F)

### When Input is Limited
If documentation is incomplete:
- Extract what you CAN definitively from the source
- Clearly note missing items in "Assumptions & Notes"
- Suggest what additional information is needed
- Provide a partial BoQ marked as "Preliminary"

## Example Workflow

**Input:** "3-story office building. Ground floor 50m × 40m, two upper floors same. 200mm concrete block walls throughout, brick veneer on external walls. Ground floor slab 150mm concrete on fill, upper floors 200mm reinforced concrete. All rooms painted. Electrical & plumbing systems required."

**Extraction process:**
1. Calculate areas: Ground floor slab (50×40=2000m²), walls (perimeter ≈ 180m, height varies)
2. Identify items: Excavation, concrete slabs, block walls, brick veneer, finishes, M&E
3. Organize into sections (A-G)
4. Create outputs: CSV with line items, markdown table, report with assumptions

**Output items might include:**
- A.1: Site mobilization (1 Item)
- B.1: Excavation (2000 m³ estimated)
- C.1: Structural concrete slabs (4500 m² total)
- D.1: Block walls (2700 m²)
- D.2: Brick veneer (900 m²)
- E.1: Electrical systems (provisional)
- And so on...

## Handling Ambiguity

When specifications are unclear or incomplete:

✅ **DO:**
- State assumptions clearly
- Note where information is missing
- Provide "best estimate" with confidence level
- Suggest what additional detail is needed

❌ **DON'T:**
- Make wild guesses at quantities
- Omit items without noting the gap
- Create items that don't have source basis
- Assume standard prices if not given

## Output Formats

Generate outputs as:
1. **CSV/Excel file**: Importable into cost estimation tools
2. **Markdown table**: Pastable into documentation, emails, reports
3. **Text report**: Comprehensive analysis with assumptions

If the user needs only one format, provide the primary output (CSV) plus a brief markdown summary.

## Quality Checklist

Before delivering BoQ, verify:
- [ ] All items have clear descriptions and specifications
- [ ] Quantities are extracted from or calculated based on source docs
- [ ] Items are organized into logical sections
- [ ] Subtotals are provided for each section
- [ ] Assumptions and missing information are documented
- [ ] Output can be used for tendering/estimation
- [ ] Calculations (if any) are correct and verifiable
