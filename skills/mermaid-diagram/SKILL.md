---
name: mermaid-diagram
description: Create, validate, and render Mermaid diagrams (flowcharts, sequence, class, state, ER, Gantt, mindmaps, and more) from a description or rough notes. Includes a dependency-free syntax validator and an optional image renderer. Use when a user asks to "make a diagram", "draw a flowchart", "visualize this process/architecture/workflow", "create a sequence/ER/class diagram", or convert notes into a Mermaid chart.
---

# Mermaid Diagram

A toolkit for turning ideas, notes, or specifications into correct, renderable
[Mermaid](https://mermaid.js.org) diagrams. The emphasis is on **producing valid
syntax on the first try** — the included validator catches the mistakes that most
commonly break rendering, so you don't ship a diagram that fails to draw.

## When to Use This Skill

Use this skill when the user wants any kind of diagram-as-code, for example:
- "Draw a flowchart of the login process."
- "Turn these steps into a diagram."
- "Make a sequence diagram for this API call."
- "Visualize this database schema as an ER diagram."
- "Create a class diagram / state machine / Gantt chart / mindmap for X."

## Core Workflow

1. **Pick the diagram type** that matches the user's intent. If they don't say,
   infer it (see the decision guide below) and briefly state your choice.
2. **Write the Mermaid source** to a `.mmd` file.
3. **Validate it** before doing anything else:
   ```bash
   python3 scripts/validate.py diagram.mmd
   ```
   The validator has **no dependencies** and always runs. Fix every `ERROR`
   before continuing; review `WARNING`s.
4. **(Optional) Render to an image** if the user wants a picture, not just code:
   ```bash
   python3 scripts/render.py diagram.mmd -o diagram.png
   ```
5. **Deliver** the Mermaid code block to the user (it renders inline in most
   Markdown/chat surfaces), plus the rendered image if one was produced.

## Choosing the Diagram Type

| User is describing... | Use |
|---|---|
| A process, decision tree, or workflow | `flowchart` |
| Messages/calls exchanged between actors over time | `sequenceDiagram` |
| Object-oriented structure, classes, inheritance | `classDiagram` |
| States and transitions of a system | `stateDiagram-v2` |
| Database tables and relationships | `erDiagram` |
| Project schedule / timeline with durations | `gantt` |
| Hierarchical brainstorm of one central idea | `mindmap` |
| Proportions of a whole | `pie` |
| Git branch/merge history | `gitGraph` |

When unsure between a flowchart and a sequence diagram: use a **sequence diagram**
if the *order of interactions between distinct participants* is the point;
otherwise use a **flowchart**.

See `references/diagram-types.md` for the syntax of each type, and
`examples/` for complete, validated samples you can adapt.

## Authoring Rules That Prevent Broken Diagrams

These are the failures the validator is built to catch — avoid them up front:

- **Quote labels with special characters.** Any node label containing
  `()[]{}`, punctuation, or `<br>` must be wrapped in double quotes:
  `A["User (admin)"]` not `A[User (admin)]`.
- **Balance every bracket and quote.** Each `(`, `[`, `{`, and `"` needs its
  partner. This is the single most common parse error.
- **Close every block.** Every `subgraph` needs an `end`; every sequence
  `loop`/`alt`/`opt`/`par`/`critical`/`rect` needs an `end`.
- **Use spaces, not tabs**, for indentation.
- **Give nodes stable IDs.** Reference a node by its ID (`A`, `login`), define
  its label once: `login["Log in"]`, then reuse `login` elsewhere.
- **Pick a valid flowchart direction**: `TD`, `TB`, `BT`, `LR`, or `RL`.

## Scripts

### `scripts/validate.py` — syntax linter (no dependencies)
Static checks that run anywhere Python 3 is available. Detects unknown diagram
types, unbalanced brackets/quotes, unterminated strings, missing `end` blocks,
bad flowchart directions, and tab indentation.
```bash
python3 scripts/validate.py diagram.mmd        # human-readable report
python3 scripts/validate.py diagram.mmd --json  # machine-readable
cat diagram.mmd | python3 scripts/validate.py - # read from stdin
```
Exit code is `0` when there are no errors, `1` when there are.

### `scripts/render.py` — image renderer (optional)
Thin wrapper around the Mermaid CLI. Produces PNG/SVG/PDF.
```bash
python3 scripts/render.py diagram.mmd -o diagram.png -t dark -b transparent
```
If the CLI is missing it prints exact install instructions and exits without
crashing — rendering is optional, validation is not.

## Rendering Dependencies

Validation needs only Python 3 (standard library). Rendering to an image needs
the Mermaid CLI:
```bash
npm install -g @mermaid-js/mermaid-cli
# or, with no install:
npx -p @mermaid-js/mermaid-cli mmdc -i diagram.mmd -o diagram.png
```

## Guidelines

- Always validate before rendering or delivering.
- Keep diagrams readable: prefer several small, focused diagrams over one giant
  one. Group related nodes with `subgraph` in flowcharts.
- Echo the Mermaid source back to the user in a fenced ```mermaid block so it
  renders inline; attach an image only when explicitly useful.
- When converting unstructured notes, restate the structure you inferred (nodes,
  edges, actors) so the user can correct you, then produce the diagram.
