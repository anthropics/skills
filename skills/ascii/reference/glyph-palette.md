# Unicode Box-Drawing Glyph Palette

Read this file before drawing any diagram. It defines the character set,
alignment rules, and self-check procedure.

## Character Set

### Lines

| Glyph | Name              | Use                                |
| ----- | ----------------- | ---------------------------------- |
| `─`   | horizontal line   | Box sides, horizontal connectors   |
| `│`   | vertical line     | Box sides, vertical connectors     |
| `═`   | double horizontal | Title underlines, emphasis borders |
| `║`   | double vertical   | Emphasis borders                   |

### Corners (single)

| Glyph | Name         | Use       |
| ----- | ------------ | --------- |
| `┌`   | top-left     | Box start |
| `┐`   | top-right    | Box end   |
| `└`   | bottom-left  | Box start |
| `┘`   | bottom-right | Box end   |

### Corners (double)

| Glyph | Name                | Use          |
| ----- | ------------------- | ------------ |
| `╔`   | double top-left     | Emphasis box |
| `╗`   | double top-right    | Emphasis box |
| `╚`   | double bottom-left  | Emphasis box |
| `╝`   | double bottom-right | Emphasis box |

### Tees and crosses

| Glyph | Name       | Use                         |
| ----- | ---------- | --------------------------- |
| `├`   | left tee   | Branch from vertical line   |
| `┤`   | right tee  | Branch into vertical line   |
| `┬`   | top tee    | Branch down from horizontal |
| `┴`   | bottom tee | Branch up from horizontal   |
| `┼`   | cross      | Intersection                |

### Arrows

| Glyph | Name             | Use                            |
| ----- | ---------------- | ------------------------------ |
| `▼`   | down arrow       | Flow direction                 |
| `▲`   | up arrow         | Return flow                    |
| `►`   | right arrow      | Left-to-right flow             |
| `◄`   | left arrow       | Right-to-left flow             |
| `→`   | thin right arrow | Inline references, key legends |
| `←`   | thin left arrow  | Inline annotations             |

### Tree characters

| Glyph  | Name        | Use                         |
| ------ | ----------- | --------------------------- |
| `├──`  | branch      | Directory tree mid-entry    |
| `└──`  | last branch | Directory tree last entry   |
| `│`    | trunk       | Directory tree continuation |

### Table borders

| Glyph    | Name       | Use                    |
| -------- | ---------- | ---------------------- |
| `┌─┬─┐`  | top row    | Table header top       |
| `├─┼─┤`  | mid row    | Table header separator |
| `└─┴─┘`  | bottom row | Table footer           |

## Alignment Rules

1. **Column lock**: Every `│` in a vertical run shares the same character
   offset from line start. Count characters, not visual width.
2. **Row continuity**: Every `─` in a horizontal run is unbroken. No gaps,
   no spaces inside a line segment.
3. **Box closure**: Every `┌` has a matching `┐` on the same line. Every
   `└` has a matching `┘` on the same line. Vertical sides connect them.
4. **Arrow direction**: `▼` points toward the next processing step.
   `►` points toward the output or downstream system.
5. **Content padding**: One space between box edge and text content.
   `│ text here │` not `│text here│`.
6. **Consistent width**: All boxes in a vertical chain share the same width.
   Pad shorter labels with spaces.
7. **Monospaced assumption**: All output is viewed in a monospaced font.
   Every character occupies exactly one column.

## Self-Check Procedure

Run this checklist on every diagram before saving:

1. Pick each column that contains `│`. Verify every `│` in that column
   has the same character offset. Fix any that drift.
2. Trace each `─` run. Confirm it spans continuously from left boundary
   to right boundary with no gaps.
3. For each box: confirm `┌` and `┐` are on the same line, `└` and `┘`
   are on the same line, vertical `│` connects them at matching offsets.
4. Verify arrow glyphs match data-flow direction.
5. Strip trailing whitespace from every line.
6. Confirm the title line is followed by `=` characters of equal width.

## Diagram Type Skeletons

### Pipeline (vertical chain with gates)

```text
  ┌───────────────────────────────┐
  │  STEP 1: Description         │
  │                               │
  │  Detail line 1                │
  │  Detail line 2                │
  │                               │
  │  ═══════ HARD GATE ════════  │
  └───────────────┬───────────────┘
                  ▼
  ┌───────────────────────────────┐
  │  STEP 2: Description         │
  └───────────────────────────────┘
```

### Data flow (left-to-right with transforms)

```text
  source_a ──┐
  source_b ──┤     ┌────────────┐     ┌────────────┐
  source_c ──┼────►│ Transform  │────►│  Output    │
  source_d ──┤     └────────────┘     └────────────┘
  source_e ──┘
```

### Module map (boxes with labeled connections)

```text
  ┌──────────┐  request   ┌──────────┐  query   ┌──────────┐
  │ Client   │───────────►│ Server   │─────────►│ Database │
  └──────────┘            └──────────┘          └──────────┘
       ▲                       │
       │        response       │
       └───────────────────────┘
```

### File tree (indented with branch characters)

```text
  project/
  ├── src/
  │   ├── main.py          ← entry point
  │   ├── config.py        ← settings
  │   └── utils/
  │       ├── helpers.py
  │       └── constants.py
  ├── tests/
  │   └── test_main.py
  └── README.md
```

### Integration map (hub-and-spoke)

```text
  ┌──────┐┌──────┐┌──────┐
  │Svc A ││Svc B ││Svc C │
  └──┬───┘└──┬───┘└──┬───┘
     │       │       │
     ▼       ▼       ▼
  ┌──────────────────────┐
  │      Hub / Router    │
  └──────────────────────┘
```

### Table / matrix

```text
  ┌──────────┬──────────┬──────────┐
  │ Header A │ Header B │ Header C │
  ├──────────┼──────────┼──────────┤
  │ value    │ value    │ value    │
  │ value    │ value    │ value    │
  └──────────┴──────────┴──────────┘
```
