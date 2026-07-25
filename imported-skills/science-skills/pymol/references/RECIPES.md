# Common Recipes

Copy-paste ready recipes for common PyMOL visualization tasks. Each recipe
assumes the init boilerplate has already been set up (see
[PYMOL_REFERENCE.md](PYMOL_REFERENCE.md)).

### Cartoon with secondary structure coloring

```python
cmd.load("data/structure.cif", "protein")
cmd.show("cartoon")
cmd.color("green", "ss h")
cmd.color("yellow", "ss s")
cmd.color("gray", "ss l+''")
cmd.orient()
cmd.png("output/cartoon.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### B-factor (pLDDT) coloring

```python
cmd.load("data/AF-P00520-F1-model_v4.cif", "protein")
cmd.show("cartoon")
cmd.spectrum("b", "red_white_blue", "polymer.protein")
cmd.orient()
cmd.png("output/bfactor.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### AlphaFold pLDDT coloring (canonical thresholds)

```python
cmd.load("data/structure.cif", "protein")
cmd.show("cartoon")
# Define AlphaFold's canonical pLDDT colors
cmd.set_color("af_very_low", [0xFF, 0x7D, 0x45])   # orange, pLDDT < 50
cmd.set_color("af_low",      [0xFF, 0xDB, 0x13])   # yellow, 50 <= pLDDT < 70
cmd.set_color("af_confident", [0x65, 0xCB, 0xF3])  # light blue, 70 <= pLDDT < 90
cmd.set_color("af_very_high", [0x00, 0x53, 0xD6])  # dark blue, pLDDT >= 90
# Apply from lowest to highest threshold
cmd.color("af_very_low", "polymer.protein")
cmd.color("af_low", "polymer.protein and b > 50")
cmd.color("af_confident", "polymer.protein and b > 70")
cmd.color("af_very_high", "polymer.protein and b > 90")
cmd.orient()
cmd.png("output/plddt.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Highlight specific residues

```python
cmd.load("data/structure.cif", "protein")
cmd.show("cartoon")
cmd.color("gray", "all")
cmd.select("active_site", "chain A and resi 100+102+150")
cmd.show("sticks", "active_site")
cmd.color("red", "active_site")
cmd.orient()
cmd.png("output/highlight.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Surface rendering

```python
cmd.load("data/structure.cif", "protein")
cmd.show("cartoon", "polymer.protein")
cmd.color("green", "polymer.protein and ss h")
cmd.color("yellow", "polymer.protein and ss s")
cmd.color("gray", "polymer.protein and (ss l+'')")
cmd.show("surface", "polymer.protein")
cmd.set("surface_color", "white", "polymer.protein")
cmd.set("transparency", 0.3, "polymer.protein")
cmd.orient()
cmd.png("output/surface.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Electrostatic surface rendering

```python
cmd.load("data/structure.cif", "protein")
cmd.remove("solvent")
cmd.show("cartoon", "polymer.protein")
cmd.color("gray80", "polymer.protein")
util.protein_vacuum_esp("polymer.protein", quiet=0)
cmd.show("surface", "polymer.protein")
cmd.set("transparency", 0.0, "polymer.protein")
cmd.set("two_sided_lighting", 1)
cmd.orient()
cmd.png("output/electrostatic.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Multi-chain complex colors

```python
cmd.load("data/complex.cif", "complex")
cmd.remove("solvent")
cmd.show("cartoon", "polymer.protein")

chain_colors = ["cyan", "salmon", "green", "yellow", "magenta",
                "orange", "slate", "limon", "deeppurple", "wheat"]
chains = cmd.get_chains("complex")
print(f"Chains found: {', '.join(chains)}")
for i, chain in enumerate(chains):
    color = chain_colors[i % len(chain_colors)]
    cmd.color(color, f"chain {chain}")
    print(f"  Chain {chain}: {color} ({cmd.count_atoms(f'chain {chain} and name CA')} residues)")

cmd.orient()
cmd.png("output/chains.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### B-factor putty analysis

```python
cmd.load("data/structure.cif", "protein")
cmd.remove("solvent")

cmd.show("cartoon", "polymer.protein")
cmd.cartoon("putty", "polymer.protein")
cmd.set("cartoon_putty_scale_min", 0.3)
cmd.set("cartoon_putty_scale_max", 3.0)
cmd.set("cartoon_putty_transform", 0)
cmd.spectrum("b", "blue_white_red", "polymer.protein")
cmd.orient()
cmd.png("output/putty.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Cavity and pocket visualization (including ligand focus)

```python
cmd.load("data/structure.cif", "protein")
cmd.remove("solvent")

cmd.show("cartoon", "polymer.protein")
cmd.color("gray80", "polymer.protein")

# If a ligand is present, isolate one to focus the cavity view
if cmd.count_atoms("organic") > 0:
    # Isolate a single ligand to prevent zoomed-out views on symmetrical complexes
    first_atom = cmd.get_model("organic").atom[0]
    cmd.select("target_ligand", f"organic and chain '{first_atom.chain}' and resi '{first_atom.resi}'")

    cmd.show("sticks", "target_ligand")
    util.cnc("target_ligand")

    # Orient on the single ligand and zoom with enough buffer to see the pocket context
    cmd.orient("target_ligand")
    cmd.zoom("target_ligand", buffer=10.0)
else:
    cmd.orient()

cmd.show("surface", "polymer.protein")
cmd.set("surface_color", "white", "polymer.protein")
cmd.set("transparency", 0.6, "polymer.protein")

cmd.set("surface_cavity_mode", 1)
cmd.set("surface_cavity_radius", 5.0)
cmd.set("surface_cavity_cutoff", -1.0)
cmd.set("cavity_cull", 50)

cmd.set("two_sided_lighting", 1)
cmd.png("output/cavities.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

**`surface_cavity_mode` values:** `0` = no cavity (default), `1` = show cavities
only, `2` = show outer surface trimmed around cavities.

### Multi-structure batch rendering

For comparing multiple structures side-by-side or generating consistent renders
across a set of PDB files. This is common in design campaigns.

```python
import os
import glob

structures = glob.glob("data/*.pdb") + glob.glob("data/*.cif")
print(f"Found {len(structures)} structures to render")

for struct_path in sorted(structures):
    name = os.path.splitext(os.path.basename(struct_path))[0]
    cmd.load(struct_path, name)

    n_atoms = cmd.count_atoms(name)
    if n_atoms == 0:
        print(f"  SKIP {name}: 0 atoms loaded")
        cmd.delete(name)
        continue

    cmd.show("cartoon", name)
    cmd.color("green", f"{name} and ss h")
    cmd.color("yellow", f"{name} and ss s")
    cmd.color("gray", f"{name} and (ss l+'')")
    cmd.orient(name)
    cmd.png(f"output/{name}.png", width=1200, height=900, dpi=150)
    print(f"  Rendered {name} ({n_atoms} atoms)")
    cmd.delete(name)
```

### Measure distance between residues

```python
cmd.load("data/structure.cif", "protein")
cmd.show("cartoon")
cmd.distance("d1", "chain A and resi 10 and name CA", "chain A and resi 50 and name CA")
print(f"Distance: {cmd.get_distance('chain A and resi 10 and name CA', 'chain A and resi 50 and name CA'):.2f} A")
cmd.orient()
cmd.png("output/distance.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Zoom into binding pocket

```python
cmd.load("data/complex.pdb", "complex")
cmd.show("cartoon", "polymer.protein")
cmd.color("gray", "polymer.protein")
cmd.select("pocket", "byres (polymer.protein within 5.0 of organic)")
cmd.show("sticks", "pocket")
cmd.color("cyan", "pocket")
cmd.zoom("pocket", buffer=3.0)
cmd.png("output/pocket_zoom.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Protein-ligand interaction

```python
cmd.load("data/complex.pdb", "complex")

# Isolate a single ligand to prevent zoomed-out views on symmetrical complexes
if cmd.count_atoms("organic") > 0:
    first_atom = cmd.get_model("organic").atom[0]
    cmd.select("target_ligand", f"organic and chain '{first_atom.chain}'")
else:
    raise RuntimeError("No ligand found.")

cmd.select("binding_site", "byres (polymer.protein within 4.0 of target_ligand)")

# Styled rendering with heteroatom coloring
cmd.show("cartoon", "polymer.protein")
cmd.set("cartoon_transparency", 0.4, "polymer.protein")
cmd.color("gray80", "polymer.protein")

cmd.show("sticks", "binding_site")
util.cbac("binding_site")
util.cnc("binding_site")
cmd.show("sticks", "target_ligand")
util.cbag("target_ligand")
util.cnc("target_ligand")
cmd.hide("sticks", "hydro")

# Show pocket waters
cmd.select("pocket_waters", "solvent within 4.0 of target_ligand")
cmd.show("spheres", "pocket_waters")
cmd.color("red", "pocket_waters")
cmd.set("sphere_scale", 0.15, "pocket_waters")

# Polar contacts (hydrogen bonds)
cmd.distance("polar_contacts", "target_ligand", "binding_site", cutoff=3.5, mode=2)
cmd.set("dash_color", "yellow")
cmd.set("dash_gap", 0.4)
cmd.set("dash_radius", 0.08)
cmd.hide("labels", "polar_contacts")

cmd.orient("target_ligand | binding_site")
cmd.zoom("target_ligand | binding_site", buffer=3.0)
cmd.png("output/ligand.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### In silico mutagenesis

```python
cmd.load("data/structure.cif", "protein")
cmd.show("cartoon")
cmd.wizard("mutagenesis")
cmd.get_wizard().set_mode("ALA")
cmd.get_wizard().do_select("chain A and resi 100")
cmd.get_wizard().apply()
cmd.set_wizard()
cmd.orient()
cmd.png("output/mutant.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Two-structure superposition with RMSD

PyMOL provides three structural alignment methods:

-   `align` — sequence-dependent; best when structures share >40% sequence
    identity
-   `super` — sequence-independent superposition; use when structures are
    structurally similar but have poor sequence identity
-   `cealign` — combinatorial extension; use when there is neither sequence nor
    strong structural similarity

The recipe below attempts `align` first and falls back to `cealign`
automatically.

```python
cmd.load("data/structure1.cif", "model1")
cmd.load("data/structure2.cif", "model2")

try:
    result = cmd.align("model2", "model1")
    if result[1] < 20:
        raise ValueError("Poor sequence alignment")
    print(f"Method: align (>40% sequence identity)")
    print(f"RMSD: {result[0]:.3f} A over {result[1]} atoms")
except Exception:
    result = cmd.cealign("model1", "model2")
    print(f"Method: cealign (low sequence identity fallback)")
    print(f"RMSD: {result['RMSD']:.3f} A over {result['alignment_length']} atoms")

cmd.show("cartoon", "all")
cmd.color("cyan", "model1")
cmd.color("salmon", "model2")
cmd.orient()
cmd.png("output/superposition.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

### Load and modify an existing session

```python
cmd.load("data/previous_session.pse")
cmd.color("marine", "chain A")
cmd.show("surface", "chain B")
cmd.orient()
cmd.png("output/modified.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
```

To run any of these recipes, place the code in a Python script with the required
header and boilerplate (see [SKILL.md](../SKILL.md)) and run it with:

```bash
uv run your_script.py
```
