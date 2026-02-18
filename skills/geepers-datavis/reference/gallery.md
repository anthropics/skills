# Visualization Gallery

Examples of available visualization templates and their data formats.

## 1. Radial Hierarchy Tree
**Template:** `radial-tree`
**Description:** Circular tree layout best for deep hierarchies (3+ levels).
**Data Format:** Hierarchical JSON (Flare format)
```json
{
  "name": "Root",
  "children": [
    {
      "name": "Branch A",
      "children": [
        {"name": "Leaf 1", "value": 100},
        {"name": "Leaf 2", "value": 200}
      ]
    }
  ]
}
```

## 2. Sankey Flow Diagram
**Template:** `sankey`
**Description:** Flow diagram for tracking volume transfers between states/nodes.
**Data Format:** Node-Link JSON
```json
{
  "nodes": [{"name": "Start"}, {"name": "End"}],
  "links": [{"source": 0, "target": 1, "value": 10}]
}
```

## 3. Multi-Dimensional Bubble Chart
**Template:** `bubble-chart`
**Description:** 3-variable scatter plot (x, y, radius).
**Data Format:** Grouped Array
```json
[
  {
    "label": "Group 1",
    "data": [{"x": 10, "y": 20, "r": 5}]
  }
]
```

## 4. Force-Directed Network
**Template:** `force-network`
**Description:** Interconnected graph for relationship mapping.
**Data Format:** Node-Link
```json
{
  "nodes": [{"id": "A", "group": 1}],
  "links": [{"source": "A", "target": "B", "value": 1}]
}
```

## 5. Geographic Map (Choropleth)
**Template:** `choropleth`
**Description:** US State map coloring by value.
**Data Format:** Key-Value Pairs
```json
[
  ["06", 85], // California FIPS code
  ["48", 72]  // Texas FIPS code
]
```
