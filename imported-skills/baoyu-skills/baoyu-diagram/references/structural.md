# Structural Diagram Layout

Covers: class diagrams, ER diagrams, component diagrams, package diagrams, org charts.

## Class Diagram

### Class Box (3-compartment)

```svg
<g transform="translate(X, Y)">
  <!-- Mask -->
  <rect width="180" height="120" rx="6" fill="#0f172a"/>
  <!-- Box -->
  <rect width="180" height="120" rx="6" fill="rgba(8,51,68,0.4)" stroke="#22d3ee" stroke-width="1.5"/>
  <!-- Class name compartment -->
  <text x="90" y="24" fill="white" font-size="11" font-weight="700" text-anchor="middle">ClassName</text>
  <!-- Divider 1 -->
  <line x1="0" y1="35" x2="180" y2="35" stroke="#22d3ee" stroke-width="0.5" stroke-opacity="0.5"/>
  <!-- Attributes -->
  <text x="10" y="52" fill="#94a3b8" font-size="8">- id: int</text>
  <text x="10" y="64" fill="#94a3b8" font-size="8">- name: string</text>
  <!-- Divider 2 -->
  <line x1="0" y1="75" x2="180" y2="75" stroke="#22d3ee" stroke-width="0.5" stroke-opacity="0.5"/>
  <!-- Methods -->
  <text x="10" y="92" fill="#94a3b8" font-size="8">+ getName(): string</text>
  <text x="10" y="104" fill="#94a3b8" font-size="8">+ setName(s: string)</text>
</g>
```

For abstract classes, italicize the class name. For interfaces, add `«interface»` above the name in smaller font.

### Relationship Lines

| Relationship | Line Style | Arrow/End |
|-------------|------------|-----------|
| Inheritance | Solid | Empty triangle (▷) pointing to parent |
| Implementation | Dashed | Empty triangle pointing to interface |
| Composition | Solid | Filled diamond (◆) at owner end |
| Aggregation | Solid | Empty diamond (◇) at owner end |
| Dependency | Dashed | Open arrowhead at dependency target |
| Association | Solid | Open arrowhead or none |

**Markers:**

```svg
<!-- Inheritance triangle -->
<marker id="inherit" markerWidth="12" markerHeight="10" refX="12" refY="5" orient="auto">
  <polygon points="0 0, 12 5, 0 10" fill="#0f172a" stroke="#94a3b8" stroke-width="1.5"/>
</marker>

<!-- Composition diamond -->
<marker id="composition" markerWidth="12" markerHeight="8" refX="0" refY="4" orient="auto">
  <polygon points="0 4, 6 0, 12 4, 6 8" fill="#94a3b8"/>
</marker>

<!-- Aggregation diamond -->
<marker id="aggregation" markerWidth="12" markerHeight="8" refX="0" refY="4" orient="auto">
  <polygon points="0 4, 6 0, 12 4, 6 8" fill="#0f172a" stroke="#94a3b8" stroke-width="1.5"/>
</marker>
```

### Cardinality Labels

Place at each end of the relationship line, offset 5-8px from the box edge:

```svg
<text x="X" y="Y" fill="#94a3b8" font-size="8">1..*</text>
```

## ER Diagram

Similar to class diagrams but:
- Use 2-compartment boxes (entity name + attributes)
- Mark primary keys with `PK` prefix and bold
- Mark foreign keys with `FK` prefix
- Relationship lines use crow's foot notation:

```svg
<!-- One end (single line) -->
<line x1="X1" y1="Y" x2="X1+15" y2="Y" stroke="#94a3b8" stroke-width="1.5"/>
<!-- Many end (crow's foot) -->
<line x1="X2-15" y1="Y-6" x2="X2" y2="Y" stroke="#94a3b8" stroke-width="1.5"/>
<line x1="X2-15" y1="Y+6" x2="X2" y2="Y" stroke="#94a3b8" stroke-width="1.5"/>
<line x1="X2-15" y1="Y" x2="X2" y2="Y" stroke="#94a3b8" stroke-width="1.5"/>
```

## Org Chart

- Top-down tree layout
- Root at top center
- Each level evenly spaced (100-120px vertical gap)
- Siblings evenly distributed horizontally
- Connection lines: vertical from parent bottom center to horizontal bar, then vertical down to each child top center
- Use color to indicate departments or hierarchy levels

## Layout Tips

- Start by counting the widest level to determine total diagram width
- Center the tree horizontally in the viewBox
- For deep trees (5+ levels), consider horizontal layout instead
