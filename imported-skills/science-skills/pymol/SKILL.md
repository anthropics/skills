---
name: pymol
description: >
  Visualize, analyze, and render protein and molecular structures using PyMOL.
  Use when the user wants to create images of protein structures, perform
  structural alignments or superposition, measure distances or contacts,
  highlight binding sites or active site residues, color by B-factor/pLDDT,
  or analyze protein-ligand interactions. Do not use for docking,
  molecular dynamics, or sequence-only analysis.
---

# PyMOL

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/pymol_LICENSE.txt does not already exist
    in the workspace root directory then (1) prominently notify the user to
    check the license at https://www.pymol.org/, then (2) create the file
    recording the notification text and timestamp.

## Overview

All PyMOL commands run on the host via `uv` with OSMesa software rendering — no
GPU, display, or X server is needed. Structure files must be downloaded to the
host before running PyMOL.

**Do NOT use when:**

-   The user wants to run AlphaFold predictions.
-   The user wants docking or molecular dynamics simulations.
-   The user only has a sequence and no structure file — fetch the structure
    first. Check if any other installed skills can retrieve structures from the
    PDB or AlphaFold Database before proceeding.

## Setup (Agent Instructions)

Ensure that `uv` is installed on the host system. The PyMOL scripts use PEP 0723
headers to declare their dependencies, and `uv run` will automatically handle
installing them (including `pymol-open-source-whl`) when the script is executed.

## Core Rules

-   **Output paths must be absolute or relative to the user's project root.**
    Always run PyMOL scripts from the user's project directory.
-   **Software rendering only.** Use `cmd.png()` for output. Never use
    `cmd.draw()` or `cmd.ray()` with hardware acceleration — OSMesa does not
    support it. Set environment variable `PYOPENGL_PLATFORM=osmesa` for headless
    rendering.
-   **Always save a `.pse` session file** alongside any PNG output. This lets
    the user open the session in their local PyMOL for further inspection.
-   **Always call `cmd.quit()`** at the end of every PyMOL script. Omitting it
    causes the process to stop responding.
-   **Init boilerplate is mandatory.** Every PyMOL script must begin with the
    initialization sequence. `from pymol import cmd` must come after
    `finish_launching()`, not before.
-   See [references/PYMOL_REFERENCE.md](references/PYMOL_REFERENCE.md) for
    selection syntax, common commands, and gotchas.
-   **Pre-Flight File Check**: Before writing the PyMOL script or running it,
    you MUST verify that the requested structure file actually exists on the
    host machine.
-   **Verify Structure Load**: After loading a structure with `cmd.load()`,
    always verify it succeeded by checking `cmd.count_atoms("all")`. If the
    result is 0, print an error to stdout and call `cmd.quit()` immediately.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Quick Start

*   Ensure structure files are downloaded to a directory in the user's project.
*   Write a PyMOL Python script (e.g., `render.py`) with the required init
    boilerplate and PEP 0723 header.
*   Run it via `uv run`: `bash uv run render.py`

### Minimal example script (`render.py`)

```python
# /// script
# requires-python = ">=3.10, <3.13"
# dependencies = [
#     "pymol-open-source-whl",
# ]
# ///

import os
import sys

# Set environment variable for headless rendering
os.environ["PYOPENGL_PLATFORM"] = "osmesa"

import pymol # pytype: disable=import-error
pymol.pymol_argv = ["pymol", "-cq"]
pymol.finish_launching()

from pymol import cmd # pytype: disable=import-error

cmd.load("AF-P00520-F1-model_v4.cif", "structure")
cmd.show("cartoon")
cmd.color("green", "ss h")
cmd.color("yellow", "ss s")
cmd.color("gray", "ss l+''")
cmd.orient()
cmd.set("ray_opaque_background", 1)
cmd.png("output/render.png", width=1200, height=900, dpi=150)
cmd.save("output/session.pse")
cmd.quit()
```

## Common Recipes

See [references/RECIPES.md](references/RECIPES.md) for complete, copy-paste
ready recipes. Available recipes:

-   **Cartoon with secondary structure coloring** — basic helix/sheet/loop
    coloring
-   **B-factor (pLDDT) coloring** — continuous spectrum coloring by B-factor
-   **AlphaFold pLDDT coloring** — canonical threshold-based confidence colors
-   **Highlight specific residues** — show active site or key residues as sticks
-   **Surface rendering** — transparent surface over cartoon
-   **Electrostatic surface rendering** — vacuum electrostatics (qualitative)
-   **Multi-chain complex colors** — automatic per-chain coloring
-   **B-factor putty analysis** — tube width proportional to flexibility
-   **Cavity and pocket visualization** — surface cavity detection with ligand
    focus
-   **Multi-structure batch rendering** — render a directory of structures
-   **Measure distance between residues** — CA–CA distance with labels
-   **Zoom into binding pocket** — simple pocket focus
-   **Protein-ligand interaction** — ligand isolation, styled rendering, polar
    contacts
-   **Two-structure superposition with RMSD** — align/cealign with auto-fallback
-   **In silico mutagenesis** — mutate residues with the mutagenesis wizard
-   **Load and modify an existing session** — re-open a `.pse` file

## Interpreting Output

-   The `output/` directory contains PNG images and a `.pse` session file.
-   Any measurements or metrics (distances, RMSD, atom counts) are printed to
    stdout by the PyMOL script. Report these values to the user.
-   Present PNG images to the user and describe the visualization.
-   Tell the user they can open the `.pse` file in their local PyMOL to further
    explore, rotate, or modify the visualization.
-   If the user wants modifications, load the saved `.pse` in a new script and
    re-run.
-   Large sessions with surfaces can exceed the `--max_output_mb` limit (default
    500 MB). Increase it with `--max_output_mb=1000` if needed.
