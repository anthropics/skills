# PyMOL Quick Reference

## Mandatory Initialization Boilerplate

Every PyMOL script **must** start with this exact sequence. The order matters —
reversing the import and `finish_launching()` will crash.

```python
import pymol
pymol.pymol_argv = ["pymol", "-cq"]
pymol.finish_launching()
from pymol import cmd
```

-   `-c` = command-line mode (no GUI)
-   `-q` = quiet (suppress startup messages)

## Rendering Backend

PyMOL runs with **OSMesa** (software rendering). There is no GPU or X display.

-   Use `cmd.png(path, width, height, dpi)` for output.
-   `cmd.ray()` works but is slow — use it only when you need ray-traced
    quality.
-   Never use `cmd.draw()` (requires hardware OpenGL).
-   Always set `cmd.set("ray_opaque_background", 1)` if you want a white
    background instead of transparent.

## Selection Syntax

### Identifiers

Selector       | Example            | Selects
-------------- | ------------------ | ----------------------------------
`chain`        | `chain A`          | All atoms in chain A
`resi`         | `resi 100`         | Residue number 100
`resi` (range) | `resi 100-200`     | Residues 100 through 200
`resi` (list)  | `resi 100+102+150` | Specific residues
`resn`         | `resn ALA`         | All alanine residues
`name`         | `name CA`          | All C-alpha atoms
`ss`           | `ss h`             | Helices (h), sheets (s), loops (l)

### Structure types

Selector          | Selects
----------------- | ------------------------------------------
`polymer.protein` | All protein atoms
`organic`         | Organic ligands (non-polymer, non-solvent)
`solvent`         | Water molecules
`hetatm`          | Heteroatoms (ligands, ions, water)
`all`             | Everything

### Logical operators

Operator | Example                          | Meaning
-------- | -------------------------------- | ------------
`and`    | `chain A and resi 100`           | Intersection
`or`     | `resn ALA or resn GLY`           | Union
`not`    | `not solvent`                    | Negation
`()`     | `chain A and (not resi 100-110)` | Grouping

### Proximity selectors

Selector                  | Example
------------------------- | ---------------------------------------------
`within X of (selection)` | `polymer.protein within 4 of organic`
`byres (selection)`       | `byres (polymer.protein within 4 of organic)`
`around X`                | `resi 100 around 5`

### Named selections

```python
cmd.select("binding_site", "byres (polymer.protein within 4 of organic)")
cmd.select("alpha_carbons", "name CA and polymer.protein")
```

## File Paths

-   When running with `uv run`, files are accessed directly from the host
    filesystem.
-   Paths are relative to the directory where you run the command, or you can
    use absolute paths.
-   Ensure output directories exist before trying to write to them.

## Common Commands

### Loading structures

```python
cmd.load("data/structure.cif", "myprotein")
cmd.load("data/structure.pdb", "myprotein")
```

### Display modes

```python
cmd.show("cartoon", "polymer.protein")
cmd.show("sticks", "resi 100-110")
cmd.show("surface", "polymer.protein")
cmd.show("spheres", "resi 50")
cmd.hide("everything", "solvent")
```

### Coloring

```python
cmd.color("green", "ss h")
cmd.color("cyan", "chain A")
cmd.spectrum("b", "red_white_blue", "polymer.protein")
cmd.spectrum("count", "rainbow", "polymer.protein")
```

### Structural operations

```python
cmd.align("mobile", "target")
cmd.super("mobile", "target")
cmd.select("site", "resi 100-120 and chain A")
cmd.distance("dist1", "resi 100 and name CA", "resi 200 and name CA")
```

### Output

```python
cmd.png("output/image.png", width=1200, height=900, dpi=150)
cmd.save("output/modified.pdb", "myprotein")
```

### Cleanup (REQUIRED)

```python
cmd.quit()
```

## Common Pitfalls

1.  **`cmd.quit()` is mandatory** — without it, the PyMOL process hangs and the
    container will time out.
2.  **Selection case sensitivity** — `"chain a"` is NOT the same as `"chain A"`.
3.  **`cmd.fetch()` will fail** — there is no network inside the container. Use
    `cmd.load()` with pre-downloaded files.
4.  **`cmd.png()` before `cmd.quit()`** — ensure all rendering is done before
    quitting.
5.  **Paths are relative to current directory** — ensure you run the script from
    the correct directory or use absolute paths.
6.  **Container timeout** — the default timeout is **300 seconds** (5 minutes),
    which is sufficient for most rendering tasks. For long operations (e.g.,
    ray-tracing large complexes), increase with `--container_timeout=<seconds>`.
    Do not reduce below 60 seconds.
7.  **Distance objects are NOT selections** — `cmd.distance()` creates a
    measurement object, not an atom selection. Do NOT use `cmd.count_atoms()` on
    distance objects — it will error. Only use `cmd.count_atoms()` on valid atom
    selections (e.g., by residue name, chain, or proximity).
8.  **Selection names must be valid identifiers** — names passed to
    `cmd.select("name", ...)` must be alphanumeric and underscores only, start
    with a letter, and contain no spaces. `binding_site` is valid; `binding
    site` or `1_ligand` will crash PyMOL.
9.  **Multi-state structures (NMR)** — for NMR ensembles or multi-model files,
    restrict distance measurements, alignments, and rendering to `state=1` to
    prevent visual clutter and errors across all states simultaneously.
