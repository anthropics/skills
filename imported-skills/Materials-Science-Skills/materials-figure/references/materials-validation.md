# Materials Knowledge Validation Guide

This reference explains how to validate materials-science claims against the knowledge base before plotting. The validation layer catches claims that contradict known PDF cards, FTIR assignments, or typical property ranges — errors that would otherwise survive into figure captions and trigger reviewer objections.

**Scope**: This is a conditional validation gate in LLM-as-artist mode. When a
figure contains materials-science entities (XRD peaks, FTIR wavenumbers, or
performance values), run it before plotting. The package must contain
`source_data.csv` and `figure_contract.md` for a plotting task. Figures without
materials-science entities (pure flowcharts, workflow diagrams) may skip this
gate.

---

## 1. Knowledge Base Structure

The knowledge base lives at `static/core/materials_kb.yaml` and contains four sections:

### 1.1 XRD Reference Cards

```yaml
xrd_cards:
  - phase: "Al2O3 (alpha-corundum)"
    pdf_card: "46-1212"
    crystal_system: "hexagonal"
    peaks:
      - {two_theta: 25.57, hkl: "012", relative_intensity: 0.75}
      - {two_theta: 35.15, hkl: "104", relative_intensity: 1.00}
      - {two_theta: 37.77, hkl: "110", relative_intensity: 0.55}
    claim_boundary: "phase ID requires full pattern matching, not single peak"
```

Each card contains:
- **phase**: Canonical phase name (e.g., "Al2O3 (alpha-corundum)")
- **pdf_card**: ICDD PDF card number
- **crystal_system**: Crystal system for context
- **peaks**: List of (2θ, hkl, relative_intensity) tuples
- **claim_boundary**: What a peak match can and cannot prove

**Tolerance**: ±0.5° for 2θ matching. A peak assigned to the wrong phase (e.g., 30° 2θ called Al2O3 when it is t-ZrO2 101) is an **error**.

### 1.2 FTIR Reference Groups

```yaml
ftir_groups:
  - {wavenumber: 915, functional_group: "oxirane ring", bond_type: "epoxy C-O-C cyclic", 
     notes: "disappears after curing; curing completion indicator"}
  - {wavenumber: 1730, functional_group: "C=O stretch", bond_type: "ester carbonyl",
     notes: "epoxy ester; WER-EA marker"}
```

Each entry contains:
- **wavenumber**: Position in cm⁻¹
- **functional_group**: Group name (e.g., "oxirane ring", "C=O stretch")
- **bond_type**: Bond context (e.g., "epoxy C-O-C cyclic")
- **notes**: Diagnostic value and context

**Tolerance**: ±20 cm⁻¹ for wavenumber matching. A wavenumber assigned to the wrong functional group (e.g., 915 cm⁻¹ called C=O when it is the oxirane ring) is an **error**.

### 1.3 Performance Relations

Named physical relations with formula, applicable materials, and valid range:

```yaml
performance_relations:
  - name: "Weibull strength"
    formula: "P_f = 1 - exp(-(sigma/sigma_0)^m)"
    applies_to: ["brittle ceramics", "glass", "concrete"]
    claim_boundary: "Weibull modulus m reflects flaw population; valid for same processing route"
```

### 1.4 Typical Property Ranges

Material-property-range triples for sanity-checking performance claims:

```yaml
typical_ranges:
  - {property: "flexural_strength", material: "Al2O3", range: "300-400 MPa"}
  - {property: "flexural_strength", material: "3Y-TZP ZrO2", range: "800-1200 MPa"}
  - {property: "elastic_modulus", material: "Al2O3", range: "380 GPa"}
  - {property: "bond_strength", material: "WER-EA modified", range: "0.8-1.5 MPa"}
```

Values far outside known ranges trigger a **warning** for review.

---

## 2. Validation Workflow

### 2.1 When to Validate

Validate claims **before plotting** when the figure contract contains:
- XRD peak positions and phase assignments
- FTIR wavenumber and functional group assignments
- Performance values with units (MPa, GPa, W/mK, etc.)

Skip validation when the figure is:
- A pure flowchart or workflow diagram
- A schematic without quantitative claims
- A review figure that cites literature values without asserting new measurements

### 2.2 Running the Validator

```bash
# Basic validation
python scripts/validate_materials_claims.py path/to/figure-package

# JSON output for programmatic processing
python scripts/validate_materials_claims.py path/to/figure-package --output validation-report.json

# Custom KB path
python scripts/validate_materials_claims.py path/to/figure-package --kb path/to/custom_kb.yaml
```

**Exit codes**:
- `0` = pass (no errors; warnings may still be reported)
- `1` = error (claims contradict KB)
- `2` = package files missing or malformed

### 2.3 Validation Results

Each check returns one of three results:

**confirmed** (✅): Claim matches KB within tolerance.
```
✅ [xrd] 35.15° matches Al2O3 (alpha-corundum) #46-1212 (104) peak
✅ [ftir] 915cm⁻¹ matches KB: oxirane ring (epoxy C-O-C cyclic)
✅ [performance] 350 MPa is within Al2O3 flexural_strength range (300-400 MPa)
```

**warning** (⚠️): Claim could not be verified (phase not in KB, wavenumber not found, property not in typical ranges). Allows plotting but flags for review.
```
⚠️ [xrd] phase 'unknown_phase' not in KB; cannot verify 28.5°
⚠️ [ftir] 1234cm⁻¹ not in KB (tolerance ±20cm⁻¹)
⚠️ [performance] custom_alloy elastic_modulus not in KB; cannot verify 250 GPa
```

**error** (❌): Claim contradicts KB. Blocks plotting until corrected.
```
❌ [xrd] 30.2° does not match Al2O3 #46-1212; it matches ZrO2 (tetragonal) #79-1769 (101)
❌ [ftir] 915cm⁻¹ is oxirane ring (epoxy C-O-C cyclic), not C=O stretch (which is at 1730cm⁻¹)
❌ [performance] 2000 MPa is outside Al2O3 flexural_strength range (300-400 MPa)
```

---

## 3. XRD Validation Details

### 3.1 Phase Aliases

The validator recognizes common aliases and maps them to canonical KB phase names:

```python
PHASE_ALIASES = [
    ("alpha-al2o3", "Al2O3 (alpha-corundum)"),
    ("alumina", "Al2O3 (alpha-corundum)"),
    ("t-zro2", "ZrO2 (tetragonal)"),
    ("3y-tzp", "ZrO2 (tetragonal)"),
    ("m-zro2", "ZrO2 (monoclinic)"),
    ("8ysz", "8YSZ (cubic fluorite)"),
    ("beta-sic", "SiC (3C, beta)"),
    ("portlandite", "Ca(OH)2 (portlandite)"),
    ("quartz", "Quartz (SiO2)"),
    ("anatase", "TiO2 (anatase)"),
    ("rutile", "TiO2 (rutile)"),
]
```

### 3.2 Peak Matching Logic

For each (2θ, phase) claim in the contract:

1. **Find the phase in KB**: If not found → warning.
2. **Check if 2θ matches any peak** (±0.5° tolerance):
   - Match found → confirmed.
   - No match in claimed phase, but matches a different phase → error (wrong phase assignment).
   - No match in any phase → warning (peak not in KB).

### 3.3 Common XRD Pitfalls

**Single-peak phase ID**: A single peak match does not prove phase identity. Full pattern matching is required. The KB's `claim_boundary` field reminds you of this:

```yaml
claim_boundary: "phase ID requires full pattern matching, not single peak; Rietveld refinement for quantification"
```

**Tetragonal vs monoclinic ZrO2**: The 28°/31° doublet is the monoclinic signature. Absence of this doublet confirms tetragonal stabilization:

```yaml
# ZrO2 (tetragonal)
peaks:
  - {two_theta: 30.2, hkl: "101", relative_intensity: 1.00}
  - {two_theta: 34.6, hkl: "110", relative_intensity: 0.65}

# ZrO2 (monoclinic)
peaks:
  - {two_theta: 28.2, hkl: "(-111)", relative_intensity: 1.00}
  - {two_theta: 31.5, hkl: "(111)", relative_intensity: 0.70}
```

**Anatase vs rutile TiO2**: Anatase 101 at 25.3° vs rutile 110 at 27.4°. The anatase→rutile transition occurs ~700°C.

### 3.4 Python Example: Extract and Validate XRD Claims

```python
from pathlib import Path
import yaml
import re

# Load KB
kb_path = Path("static/core/materials_kb.yaml")
kb = yaml.safe_load(kb_path.read_text())

# Extract XRD claims from contract text
contract_text = Path("figure_contract.md").read_text()

# Pattern: "35.15°" or "2θ = 35.15" near phase names
theta_pattern = r"(\d{1,2}\.\d{1,2})\s*°"
phase_pattern = r"(Al2O3|ZrO2|SiC|Si3N4|TiO2)"

for match in re.finditer(theta_pattern, contract_text):
    two_theta = float(match.group(1))
    # Find nearest phase mention
    context_start = max(0, match.start() - 100)
    context = contract_text[context_start:match.end() + 50]
    phase_match = re.search(phase_pattern, context, re.IGNORECASE)
    if phase_match:
        phase = phase_match.group(1)
        print(f"Claim: {two_theta}° for {phase}")
        
        # Validate against KB
        for card in kb["xrd_cards"]:
            if phase.lower() in card["phase"].lower():
                for peak in card["peaks"]:
                    if abs(two_theta - peak["two_theta"]) <= 0.5:
                        print(f"  ✅ Matches {card['pdf_card']} {peak['hkl']}")
                        break
                else:
                    print(f"  ❌ No match in {card['phase']}")
                break
```

---

## 4. FTIR Validation Details

### 4.1 Functional Group Categories

The validator groups functional groups into categories for cross-checking:

```python
FTIR_CATEGORIES = [
    ("oxirane", "epoxy"),
    ("epoxy", "epoxy"),
    ("c=o", "carbonyl"),
    ("ester", "carbonyl"),
    ("o-h", "hydroxyl"),
    ("hydroxyl", "hydroxyl"),
    ("c-h", "methylene_ch"),
    ("ch2", "methylene_ch"),
    ("c-o-c", "ether"),
    ("ether", "ether"),
    ("si-o-si", "silicate"),
    ("si-o", "silicate"),
    ("c-s-h", "csh"),
    ("so4", "sulfate"),
    ("ettringite", "sulfate"),
    ("co3", "carbonate"),
]
```

### 4.2 Wavenumber Matching Logic

For each (wavenumber, functional_group) claim:

1. **Find KB entry at this wavenumber** (±20 cm⁻¹ tolerance):
   - Not found → warning.
   - Found → check category match.
2. **Category match**:
   - Claimed group maps to same category as KB entry → confirmed.
   - Claimed group maps to different category → error (wrong assignment).
   - Claimed group not categorizable → confirmed with note.

### 4.3 Common FTIR Pitfalls

**915 cm⁻¹ oxirane ring**: This is the epoxy curing indicator. It disappears after curing. Do not confuse with C=O stretch (1730 cm⁻¹):

```yaml
- {wavenumber: 915, functional_group: "oxirane ring", bond_type: "epoxy C-O-C cyclic"}
- {wavenumber: 1730, functional_group: "C=O stretch", bond_type: "ester carbonyl"}
```

**3400 cm⁻¹ O-H stretch**: Broad peak from water/Al-OH/Si-OH. Distinguish from sharp 3640 cm⁻¹ portlandite O-H:

```yaml
- {wavenumber: 3640, functional_group: "O-H stretch", bond_type: "Ca(OH)2 portlandite",
   notes: "sharp; distinguishes portlandite from broad water O-H"}
- {wavenumber: 3400, functional_group: "O-H stretch", bond_type: "hydroxyl",
   notes: "broad; water/Al-OH/Si-OH"}
```

**1030 vs 950 cm⁻¹ silicate**: Both are Si-O stretches but 950 cm⁻¹ is specifically C-S-H (cement hydration product):

```yaml
- {wavenumber: 1030, functional_group: "Si-O stretch", bond_type: "silicate",
   notes: "cement/silica; C-S-H overlapping"}
- {wavenumber: 950, functional_group: "Si-O stretch", bond_type: "C-S-H",
   notes: "cement hydration product; overlaps with 1030"}
```

### 4.4 Python Example: Validate FTIR Claims

```python
# Extract FTIR claims from contract
wavenumber_pattern = r"(\d{3,4})\s*cm\s*[-−‐⁻]?\s*[1¹]"
group_pattern = r"(oxirane|epoxy|C=O|carbonyl|O-H|hydroxyl|C-H|C-O-C|ether|Si-O-Si|silicate)"

for match in re.finditer(wavenumber_pattern, contract_text):
    wavenumber = int(match.group(1))
    context_start = max(0, match.start() - 100)
    context = contract_text[context_start:match.end() + 50]
    group_match = re.search(group_pattern, context, re.IGNORECASE)
    
    print(f"Claim: {wavenumber} cm⁻¹")
    
    # Find KB entry within tolerance
    for entry in kb["ftir_groups"]:
        if abs(wavenumber - entry["wavenumber"]) <= 20:
            kb_group = entry["functional_group"]
            print(f"  KB: {kb_group} ({entry['bond_type']})")
            
            # Check category match
            if group_match:
                claimed_group = group_match.group(1).lower()
                if claimed_group in kb_group.lower():
                    print(f"  ✅ Category match")
                else:
                    print(f"  ❌ Category mismatch: claimed {claimed_group}")
            break
    else:
        print(f"  ⚠️ Not found in KB (±20 cm⁻¹)")
```

---

## 5. Performance Validation Details

### 5.1 Material and Property Aliases

The validator recognizes common aliases:

```python
MATERIAL_ALIASES = [
    ("3y-tzp", "3Y-TZP ZrO2"),
    ("wer-ea", "WER-EA modified"),
    ("asphalt-aggregate", "asphalt-aggregate"),
    ("cement", "Portland cement"),
    ("alumina", "Al2O3"),
    ("zirconia", "ZrO2"),
]

PROPERTY_KEYWORDS = [
    ("flexural strength", "flexural_strength"),
    ("compressive strength", "compressive_strength"),
    ("elastic modulus", "elastic_modulus"),
    ("young's modulus", "elastic_modulus"),
    ("thermal conductivity", "thermal_conductivity"),
    ("bond strength", "bond_strength"),
    ("weibull modulus", "weibull_modulus"),
]
```

### 5.2 Unit Conversion

The validator handles unit conversions:

```python
conversions = {
    ("MPa", "GPa"): lambda v: v / 1000.0,
    ("GPa", "MPa"): lambda v: v * 1000.0,
}
```

If units cannot be converted (e.g., MPa vs W/mK), the validator returns a warning.

### 5.3 Range Checking Logic

For each (material, property, value, unit) claim:

1. **Find KB entry**: If not found → warning.
2. **Parse KB range** (e.g., "300-400 MPa" or "380 GPa"):
   - Range format → check if value falls within [low, high].
   - Single value → allow ±25% tolerance.
3. **Unit conversion**: Convert claim value to KB unit if needed.
4. **Result**:
   - Within range → confirmed.
   - Outside range → error.
   - Within tolerance for single value → confirmed.

### 5.4 Common Performance Pitfalls

**Ceramic strength ranges**: Al2O3 flexural strength is 300-400 MPa, while 3Y-TZP is 800-1200 MPa. A claim of "Al2O3 with 800 MPa flexural strength" is an error:

```yaml
- {property: "flexural_strength", material: "Al2O3", range: "300-400 MPa"}
- {property: "flexural_strength", material: "3Y-TZP ZrO2", range: "800-1200 MPa"}
```

**WER-EA bond strength**: Unmodified asphalt-aggregate bond is 0.3-0.6 MPa; WER-EA modified is 0.8-1.5 MPa. A claim of "2.5 MPa bond strength for WER-EA" is outside typical range:

```yaml
- {property: "bond_strength", material: "asphalt-aggregate", range: "0.3-0.6 MPa"}
- {property: "bond_strength", material: "WER-EA modified", range: "0.8-1.5 MPa"}
```

**Weibull modulus**: Al2O3 typically 8-12, 3Y-TZP typically 10-15. Values outside these ranges suggest unusual flaw populations or testing issues.

### 5.5 Python Example: Validate Performance Claims

```python
# Extract performance claims
property_pattern = r"(flexural strength|compressive strength|elastic modulus|bond strength)"
value_pattern = r"(\d+\.?\d*)\s*(MPa|GPa|W/mK)"

for match in re.finditer(property_pattern, contract_text, re.IGNORECASE):
    property_name = match.group(1).lower()
    context_start = max(0, match.start() - 100)
    context = contract_text[context_start:match.end() + 100]
    
    # Find material and value
    material_match = re.search(r"(Al2O3|ZrO2|WER-EA|cement)", context, re.IGNORECASE)
    value_match = re.search(value_pattern, context)
    
    if material_match and value_match:
        material = material_match.group(1)
        value = float(value_match.group(1))
        unit = value_match.group(2)
        
        print(f"Claim: {material} {property_name} = {value} {unit}")
        
        # Find KB entry
        for entry in kb["typical_ranges"]:
            if (entry["property"] == property_name.replace(" ", "_") and
                material.lower() in entry["material"].lower()):
                kb_range = entry["range"]
                print(f"  KB range: {kb_range}")
                
                # Parse and check
                # (Simplified — actual validator handles range parsing)
                break
```

---

## 6. Integration with Figure Contract

### 6.1 Where to Place Validation

Run validation **after** writing the figure contract but **before** plotting:

```
1. Write the complete eight-point figure_contract.md
2. Put `figure_contract.md` and `source_data.csv` in the same figure-package directory
3. Run validate_materials_claims.py path/to/figure-package
4. Fix errors (❌) — these block plotting
5. Review warnings (⚠️) — these flag claims for review
6. Proceed to plotting if status is pass or warning
```

### 6.2 Handling Validation Results

**Errors** block plotting. Fix them by:
- Correcting phase assignments (e.g., change "Al2O3" to "ZrO2" for 30.2° peak)
- Correcting functional group assignments (e.g., change "C=O" to "oxirane" for 915 cm⁻¹)
- Correcting performance values or material names

**Warnings** allow plotting but flag claims for review. Address them by:
- Adding the missing phase/group/property to the KB (if it's a legitimate material not yet in the KB)
- Clarifying the claim in the caption (e.g., "consistent with" instead of "proves")
- Providing literature references for unusual values

### 6.3 Validation in Multi-Figure Workflows

When using the multi-figure storyboard, validate each figure's contract individually:

```bash
for fig_dir in fig1 fig2 fig3 fig4; do
    echo "Validating $fig_dir..."
    python scripts/validate_materials_claims.py $fig_dir
done
```

The storyboard's `check_storyboard.py` does not validate materials claims — it validates narrative structure. Use both tools together for complete validation.

---

## 7. Extending the Knowledge Base

### 7.1 Adding New XRD Cards

```yaml
xrd_cards:
  - phase: "New Phase Name"
    pdf_card: "XX-XXXX"
    crystal_system: "crystal system"
    peaks:
      - {two_theta: 25.0, hkl: "100", relative_intensity: 1.00}
      - {two_theta: 35.0, hkl: "110", relative_intensity: 0.50}
    claim_boundary: "what this card can and cannot prove"
```

### 7.2 Adding New FTIR Groups

```yaml
ftir_groups:
  - {wavenumber: 1500, functional_group: "new group", bond_type: "bond context",
     notes: "diagnostic value and context"}
```

### 7.3 Adding New Performance Ranges

```yaml
typical_ranges:
  - {property: "new_property", material: "new_material", range: "100-200 MPa"}
```

### 7.4 Adding New Performance Relations

```yaml
performance_relations:
  - name: "New Relation"
    formula: "sigma = f(epsilon)"
    applies_to: ["material class"]
    valid_range: "applicable range"
    claim_boundary: "limitations"
```

---

## 8. Best Practices

1. **Validate early**: Run validation after writing the contract, not after plotting. Catching errors early prevents rework.

2. **Understand claim boundaries**: The KB's `claim_boundary` fields remind you what a measurement can and cannot prove. A single XRD peak does not prove phase identity; full pattern matching is required.

3. **Use tolerances wisely**: ±0.5° for XRD and ±20 cm⁻¹ for FTIR are reasonable defaults. Tighter tolerances may reject legitimate matches; looser tolerances may accept wrong assignments.

4. **Distinguish errors from warnings**: Errors block plotting — fix them. Warnings flag claims for review — address them in the caption or provide additional evidence.

5. **Keep the KB current**: Add new materials, phases, and properties as they appear in your work. The KB is a living document, not a static reference.

6. **Combine with storyboard validation**: For multi-figure manuscripts, use both `validate_materials_claims.py` (for individual figure claims) and `check_storyboard.py` (for narrative structure).

---

## Related files

- [SKILL.md](../SKILL.md) — When to use this skill
- [contract.md](../static/core/contract.md) — The eight-point figure contract
- [materials_kb.yaml](../static/core/materials_kb.yaml) — The knowledge base
- [validate_materials_claims.py](../scripts/validate_materials_claims.py) — Validation script
- [multi-figure-storyboard.md](multi-figure-storyboard.md) — Multi-figure narrative orchestration
- [figure-package-protocol.md](figure-package-protocol.md) — Complete figure package workflow

---

## 9. KB schema migration (2026-06-20)

The materials knowledge base was rewritten in Phase 2 to use a family-grouped
schema that matches the Phase 1 validation engine
(`scripts/validate_materials_claims.py`). The earlier flat schema in this
document (sections 1–8) describes the historical format; the new schema is
authoritative for the engine and for any new entries.

### 9.1 What changed

- **Old schema** (pre-2026-06-20): top-level keys `xrd_cards`,
  `ftir_groups`, `typical_ranges`, `thermal_events_top`, with each entry
  tagged by `phase`, `material`, or `wavenumber` as a flat list across all
  materials families.
- **New schema** (2026-06-20): top-level `families:` with seven required
  family keys. Each family has four parallel lists:
  - `xrd_peaks` — declared `phase` with `peaks_2theta` list, `card` string,
    and `tolerance_deg`.
  - `ftir_wavenumbers` — declared `bond` with `wavenumber` and
    `tolerance`.
  - `performance_ranges` — `name` plus `typical_min`, `typical_max`, and
    `warning_threshold`.
  - `thermal_events` — `name` plus `temperature_c` and `tolerance`.

### 9.2 Engine alignment

The Phase 1 validation engine (`validate_materials_claims.py`) was already
shipped against the new schema in commit `7354911`. Its
`_check_xrd_peak_phase` and `_check_performance_range` functions read
`kb["families"][family]["xrd_peaks"]` and
`kb["families"][family]["performance_ranges"]` directly. Therefore, the
KB must remain in the new schema; do not reintroduce the old top-level
keys or the engine will silently skip the entries.

### 9.3 Family coverage

The new KB covers the seven materials families used throughout this skill
plus ≥30 entries per family (≥210 total):

| Family | xrd_peaks | ftir_wavenumbers | performance_ranges | thermal_events | Total |
|---|---|---|---|---|---|
| civil | 8 | 6 | 10 | 6 | 30 |
| polymers | 6 | 8 | 8 | 8 | 30 |
| metals | 8 | 4 | 10 | 8 | 30 |
| ceramics | 10 | 6 | 6 | 8 | 30 |
| functional | 8 | 6 | 8 | 8 | 30 |
| nano | 6 | 6 | 8 | 10 | 30 |
| thermal-insulation | 4 | 6 | 10 | 10 | 30 |
| **Total** | **50** | **42** | **60** | **58** | **210** |

### 9.4 Authoring rules going forward

1. Always add new entries under the matching `families.<family>.xrd_peaks`
   / `ftir_wavenumbers` / `performance_ranges` / `thermal_events` list.
2. Do not invent new top-level keys; the engine iterates over a fixed
   set of four sub-keys per family.
3. Keep each family at the documented coverage floor; validate with the public release gate and targeted script checks before publishing changes.
4. Use `tolerance_deg` (XRD) and `tolerance` (FTIR / thermal) values that
   match the engine's matching logic; too-tight tolerances will trigger
   false-positive `xrd_peak_phase_mismatch` errors against real data.
5. Phase aliases (e.g., `Al2O3` ↔ `Alumina α-Al2O3`) are resolved in the
   engine; you can keep canonical names without manually aliasing.

### 9.5 Migration safety net

The pre-migration KB is preserved at
`docs/superpowers/specs/_kb_old_schema.yaml.bak` (gitignored) for
reference. If a regression is suspected, diff that backup against the
new `materials_kb.yaml` to recover any entries that did not survive the
rewrite.

