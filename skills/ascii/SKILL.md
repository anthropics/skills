______________________________________________________________________

## name: ascii description: > Scan a codebase and generate ASCII architecture diagrams using Unicode box-drawing glyphs. Use when the user says /ascii, "diagram the codebase", "draw architecture", "map the system", "show data flow", "visualize the code", "network diagram", or any request to create text-based diagrams of code structure, workflows, or system architecture. Also triggers on: pasting code and asking to "draw this", understanding how modules connect, or requesting a visual overview. Do NOT use for: image generation, Mermaid/PlantUML output, or non-codebase diagramming (org charts, business processes without code)

# ASCII Architecture Diagrams

Scan a codebase, identify its architecture, and produce a set of aligned
ASCII diagrams using only Unicode box-drawing characters.

## Workflow

### 1. Scan the Codebase

Read these files first (skip any that do not exist):

- `CLAUDE.md`, `README.md`, `package.json`, `pyproject.toml`, `Cargo.toml`
- Key config files (`.env.example`, `docker-compose.yml`, CI configs)

Then launch up to 3 Explore agents in parallel:

| Agent       | Focus                                               |
| ----------- | --------------------------------------------------- |
| Structure   | Module structure, imports, exports, class hierarchy |
| Data        | Data flow, configuration, I/O, state management     |
| Integration | External APIs, tools, services, deployment targets  |

Each agent returns a concise summary (not raw file contents).

### 2. Identify Diagram Subjects

From the exploration results, decide which diagrams to produce:

**Always include:**

- High-level pipeline or workflow (how a request flows through the system)
- Module interconnection map (what calls what)
- File/directory layout tree

**Include if applicable:**

- Data flow diagram (inputs, transforms, outputs)
- Integration/dependency map (external services)
- State machine or lifecycle diagram
- API route map
- Deployment topology

Aim for 5-10 diagrams. Fewer for small projects, more for complex ones.

### 3. Read the Glyph Palette

Before drawing, load [reference/glyph-palette.md](./reference/glyph-palette.md)
for the character set, alignment rules, skeleton templates, and self-check
procedure.

### 4. Draw Each Diagram

For each diagram:

1. **Title**: ALL CAPS, followed by a line of `=` characters matching the
   title width
2. **Body**: Unicode box-drawing characters only. No emoji. No ASCII art.
   No images.
3. **Annotations**: Use `←` for inline annotations on the right side of
   a diagram. Use a `Key:` or legend section below the diagram if needed.
4. **Alignment**: Every vertical pipe in a column shares the same character
   offset. Every horizontal line is continuous. Every box closes properly.
5. **Width**: Keep lines under 80 characters when possible. Allow up to 100
   for wide diagrams. Never exceed 120.

### 5. Lint Every Diagram

Before saving, run the self-check procedure from `glyph-palette.md`:

- Every `│` in a column shares the same offset
- Every `─` run is continuous (no gaps)
- Every box (`┌─┐` / `└─┘`) closes properly
- Arrow direction matches data flow
- No trailing whitespace
- Title underline matches title width

Fix any violations before proceeding.

### 6. Save Output

Create the output directory and write files:

```text
~/Downloads/<project>_architecture/
├── 00_overview.txt           ← index of all diagrams
├── 01_<name>.txt             ← first diagram
├── 02_<name>.txt             ← second diagram
├── ...
└── NN_<name>.txt             ← last diagram
```

**Index file format** (`00_overview.txt`):

```text
     <project> — System Architecture Diagrams
     ==========================================

<One-paragraph project description.>

Files in this folder:
  01_pipeline_overview.txt      — <one-line description>
  02_module_map.txt             — <one-line description>
  ...
  NN_<name>.txt                 — <one-line description>

Generated <date> from <project> codebase analysis.
```

**Diagram file format** (each `NN_<name>.txt`):

```text
DIAGRAM TITLE IN ALL CAPS
==========================

  <diagram body using box-drawing characters>

  <optional key/legend section>
```

Report the file list to the user when done.

## Quality Standards

- **Characters**: Unicode box-drawing only
  (`─ │ ┌ ┐ └ ┘ ├ ┤ ┬ ┴ ┼ ═ ║ ╔ ╗ ╚ ╝ ▼ ▲ ► ◄ → ←`).
  Tree glyphs (`├── └──`) for file layouts. Standard alphanumeric for labels.
- **Alignment**: Monospaced. Column-locked verticals. Continuous horizontals.
  Closed boxes. Verified by self-check before save.
- **Readability**: 2-space indentation inside boxes. One blank line between
  major diagram sections. Consistent box widths in vertical chains.
- **Self-contained**: Each file has a title, the diagram, and any needed
  explanation. No cross-file references required to understand a diagram.
- **Naming**: Numbered files (`01_`, `02_`, ...) with lowercase snake_case
  descriptive names. Index is always `00_overview.txt`.
