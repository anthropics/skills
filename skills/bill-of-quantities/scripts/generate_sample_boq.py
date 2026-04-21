#!/usr/bin/env python3
"""
Helper script to generate sample BoQ output for evaluation and testing.
This demonstrates the expected format and structure for BoQ generation.
"""

import json
import csv
from datetime import datetime

def generate_sample_boq_csv(output_path):
    """Generate a sample BoQ in CSV format."""
    
    boq_data = [
        # Header row
        ["Section", "Code", "Item Description", "Specification", "Qty", "Unit", "Notes"],
        [],
        # A. Preliminaries
        ["A. PRELIMINARIES", "", "", "", "", "", ""],
        ["A", "A.1", "Site Mobilization & Demobilization", "Full site setup and clearance", "1", "Item", "Includes safety equipment"],
        ["A", "A.2", "Temporary Site Office", "Prefab office container with utilities", "1", "Item", ""],
        ["A", "A.3", "Site Hoardings & Safety Fencing", "2.4m high temporary fencing, 180m perimeter", "180", "m", ""],
        ["A", "A.4", "Site Insurance", "Contractor All Risks insurance", "1", "Item", ""],
        ["", "SUBTOTAL A (Preliminaries)", "", "", "4 items", "", ""],
        [],
        # B. Groundwork
        ["B. GROUNDWORK", "", "", "", "", "", ""],
        ["B", "B.1", "Bulk Excavation", "General excavation, mixed soil, average depth 0.5m", "1000", "m³", "Includes haul away"],
        ["B", "B.2", "Structural Concrete Foundation", "R.C. strip foundation, C25 concrete, 600mm deep, 400mm wide", "108", "m³", "Perimeter 180m"],
        ["B", "B.3", "Foundation Reinforcement", "Y16 rebar @ 300mm centres", "12", "tonne", "Approx 6% steel ratio"],
        ["B", "B.4", "Structural Concrete Slab on Grade", "Reinforced concrete slab, 150mm thick, C25", "300", "m³", "50m × 40m × 0.15m"],
        ["B", "B.5", "Slab Reinforcement", "Y12 rebar @ 300mm grid", "8", "tonne", ""],
        ["B", "B.6", "DPC & Waterproofing", "Bituminous damp proof course, 2 layers", "2000", "m²", "Under slab coverage"],
        ["", "SUBTOTAL B (Groundwork)", "", "", "6 items", "", ""],
        [],
        # C. Structures
        ["C. STRUCTURES", "", "", "", "", "", ""],
        ["C", "C.1", "Concrete Block Walls", "200mm concrete blocks, solid, all interior walls", "2700", "m²", "Est. from perimeter"],
        ["C", "C.2", "Blockwork Mortar", "1:3 cement:sand mortar", "81", "m³", "@ 0.03 m³/m² of wall"],
        ["C", "C.3", "Structural Concrete Roof Slab", "Reinforced concrete slab, 150mm thick, C25", "200", "m³", "50m × 40m × 0.15m"],
        ["C", "C.4", "Roof Slab Reinforcement", "Y12 rebar @ 300mm grid", "6", "tonne", ""],
        ["", "SUBTOTAL C (Structures)", "", "", "4 items", "", ""],
        [],
        # D. Finishes
        ["D. FINISHES", "", "", "", "", "", ""],
        ["D", "D.1", "Brick Veneer (External Walls)", "110mm solid brick, class A quality", "900", "m²", "External wall coverage"],
        ["D", "D.2", "Brick Veneer Mortar", "1:4 cement:sand mortar", "27", "m³", "@ 0.03 m³/m² of brick"],
        ["D", "D.3", "Plastering (Internal Walls)", "20mm cement:sand plaster, smooth finish", "2700", "m²", "Interior wall coverage"],
        ["D", "D.4", "Painting (Walls & Ceiling)", "Emulsion paint, 2 coats", "3000", "m²", "Interior coverage"],
        ["D", "D.5", "Ceramic Floor Tiles", "Mid-range ceramic tiles 600×600mm", "2000", "m²", "Ground floor coverage"],
        ["D", "D.6", "Tile Bedding & Grouting", "Thin bed mortar", "60", "m³", "@ 0.03 m³/m² of tile"],
        ["D", "D.7", "Doors (External)", "Aluminum frame, glazed, 1.2m wide", "2", "No.", "Main entry doors"],
        ["D", "D.8", "Doors (Internal)", "Timber frame, stained plywood, 0.9m wide", "8", "No.", ""],
        ["D", "D.9", "Windows", "Aluminum frame, double glazed, avg 1.2m × 1.5m", "12", "No.", ""],
        ["D", "D.10", "Window & Door Hardware", "Hinges, locks, handles", "20", "No.", ""],
        ["", "SUBTOTAL D (Finishes)", "", "", "10 items", "", ""],
        [],
        # E. Services
        ["E. SERVICES (MEP)", "", "", "", "", "", ""],
        ["E", "E.1", "Electrical Power Distribution", "Main board, sub-boards, distribution", "1", "Item", ""],
        ["E", "E.2", "Lighting Installation", "LED fixtures throughout, ~200 points", "200", "No.", ""],
        ["E", "E.3", "Wiring & Conduits", "3-core cables in PVC conduit, distribution", "2000", "m", "Est. linear distance"],
        ["E", "E.4", "Water Supply Piping", "20mm HDPE mains, distribution", "400", "m", ""],
        ["E", "E.5", "Waste Water Drainage", "100mm PVC pipes, waste from fixtures", "300", "m", ""],
        ["E", "E.6", "Sanitary Fixtures", "WC pans + cisterns", "2", "No.", ""],
        ["E", "E.7", "Sanitary Fixtures", "Wash basins", "2", "No.", ""],
        ["E", "E.8", "Kitchen Sink", "Single bowl stainless steel sink", "1", "No.", ""],
        ["E", "E.9", "Basic Ventilation", "Exhaust fans for bathrooms/kitchen", "3", "No.", ""],
        ["", "SUBTOTAL E (Services)", "", "", "9 items", "", ""],
        [],
        # F. External Works
        ["F. EXTERNAL WORKS", "", "", "", "", "", ""],
        ["F", "F.1", "External Paving", "Concrete paving, 100mm thick", "200", "m²", "Approach & loading area"],
        ["F", "F.2", "Site Drainage", "100mm PVC stormwater drain", "150", "m", ""],
        ["F", "F.3", "Landscape Preparation", "Topsoil spreading & seeding", "500", "m²", "Grassed areas"],
        ["", "SUBTOTAL F (External Works)", "", "", "3 items", "", ""],
        [],
        # Summary
        ["G. CONTINGENCY", "", "", "", "", "", ""],
        ["G", "G.1", "Provisional Sum for Contingency", "10% of main items", "1", "Item", "Risk allowance"],
        ["", "SUBTOTAL G (Contingency)", "", "", "1 item", "", ""],
        [],
        ["GRAND TOTAL", "", "", "", "37 items", "mixed units", "See assumptions"]
    ]
    
    with open(output_path, 'w', newline='') as f:
        writer = csv.writer(f)
        for row in boq_data:
            writer.writerow(row)
    
    print(f"✓ Sample BoQ CSV generated: {output_path}")

def generate_sample_boq_markdown(output_path):
    """Generate a sample BoQ in Markdown format."""
    
    markdown = """# Bill of Quantities - Sample Commercial Building

## Project Summary
- **Building Type**: Single-storey commercial building
- **Dimensions**: 50m × 40m × 4.5m
- **Total Floor Area**: 2,000 m²
- **Total Items**: 37 line items
- **Date Generated**: {date}

## Quantity Breakdown by Section

| Section | Item Count | Key Quantities | Notes |
|---------|-----------|-----------------|-------|
| A. Preliminaries | 4 items | Site setup, mobilization | |
| B. Groundwork | 6 items | 1,400 m³ concrete, 1,000 m³ excavation | Foundation + slab |
| C. Structures | 4 items | 2,700 m² blockwork, 500 m³ concrete | Walls + roof |
| D. Finishes | 10 items | 2,700 m² plastering, 900 m² brick veneer | Interior + exterior |
| E. Services | 9 items | Electrical, plumbing, ventilation | 2 toilets, 1 kitchen |
| F. External Works | 3 items | 200 m² paving, 150 m drainage | Site finishes |
| G. Contingency | 1 item | 10% allowance | Risk reserve |
| **TOTAL** | **37 items** | **Various units** | |

## Material Totals

| Material | Quantity | Unit | Notes |
|----------|----------|------|-------|
| Concrete (C25) | 608 | m³ | Foundation + slabs + roof |
| Reinforcement Steel | 26 | tonnes | Foundation, slabs, roof |
| Concrete Blocks (200mm) | 2,700 | m² | Interior walls |
| Bricks (Veneer) | 900 | m² | External walls (~45,000 bricks) |
| Plaster | 2,700 | m² | Interior wall finish |
| Paint | 3,000 | m² | Walls and ceiling |
| Ceramic Tiles | 2,000 | m² | Flooring |
| Timber Doors | 8 | No. | Internal |
| Aluminum Doors | 2 | No. | External |
| Windows | 12 | No. | 1.2m × 1.5m standard |
| Electrical Fixtures | 200+ | No. | Lighting + outlets |
| Sanitary Ware | 5 | No. | 2 WCs + 2 basins + 1 sink |

## Key Assumptions

1. **Foundation Design**: Assumed strip foundation based on building class; soil bearing capacity assumed 100 kN/m² (typical for medium soil)
2. **Excavation Depth**: Assumed 0.5m average depth for site leveling + foundation preparation
3. **Wall Heights**: Ground to roof assumed 4.5m total; window sills at 1.2m
4. **Perimeter Walls**: Assumed all perimeter 180m requires brick veneer; internal walls are blockwork only
5. **Floor Finish**: Ground floor assumed 100% tile coverage; standard commercial specification
6. **Window/Door Count**: Counted 12 windows (typical commercial spacing ~5-8m apart), 2 external doors, 8 internal doors
7. **Electrical/Plumbing**: Basic commercial standard assumed (no special systems); 2 toilets + 1 kitchenette (small facility)
8. **HVAC**: Basic ventilation only, no full air conditioning system
9. **Steel Reinforcement**: Assumed 6% steel ratio for concrete elements (standard for C25 grade, load case assumed)
10. **Waste Allowance**: No explicit waste factor added (typically 5-10% contingency should be applied during costing)

## Missing Specifications (Require Clarification)

- Detailed structural analysis / concrete grades for specific elements
- Exact electrical & plumbing load calculations
- HVAC capacity & specifications
- Fire safety provisions (sprinklers, alarm system)
- Acoustic treatment requirements
- Parking area specifications & quantities
- Landscaping design details
- Boundary fencing details (if required)
- Specific paint/tile brands and qualities

## Recommendations

1. **Obtain Detailed Drawings**: Current BoQ is based on general dimensions; detailed drawings needed for accuracy
2. **Structural Specs**: Clarify all structural concrete grades and reinforcement schedules
3. **MEP Scope**: Confirm electrical load, plumbing fixtures, HVAC requirements with client
4. **Costing Phase**: Obtain rates from suppliers & contractors for all items
5. **Review with Architect**: Validate all items align with design intent
6. **Site Inspection**: Verify soil conditions affect foundation design assumptions

---
*Generated: {date}*
*Note: This is a preliminary BoQ for estimation and budgeting purposes. Final BoQ should be verified against detailed design documents.*
""".format(date=datetime.now().strftime("%Y-%m-%d %H:%M"))
    
    with open(output_path, 'w') as f:
        f.write(markdown)
    
    print(f"✓ Sample BoQ Markdown generated: {output_path}")

def main():
    """Generate sample outputs."""
    import os
    
    # Create outputs directory
    output_dir = "sample_outputs"
    os.makedirs(output_dir, exist_ok=True)
    
    csv_path = os.path.join(output_dir, "sample_boq.csv")
    md_path = os.path.join(output_dir, "sample_boq.md")
    
    generate_sample_boq_csv(csv_path)
    generate_sample_boq_markdown(md_path)
    
    print("\n✓ Sample BoQ outputs generated successfully!")
    print(f"  CSV: {csv_path}")
    print(f"  Markdown: {md_path}")

if __name__ == "__main__":
    main()
