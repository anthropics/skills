---
name: knowledge-graph-reasoning
description: Build, query, validate, and reason over knowledge graphs. Use this skill whenever the user wants to organize unstructured information into structured knowledge, build a knowledge graph from documents or research, query relationships between concepts, validate new facts against existing knowledge, detect contradictions, traverse entity relationships, or perform structured reasoning over interconnected data. Also use when the user mentions knowledge graphs, ontologies, entity-relationship modeling, fact validation, or structured knowledge bases.
---

# Knowledge Graph Reasoning

Build structured knowledge graphs from unstructured input, query them with traversal and inference, and validate new facts adversarially against existing knowledge. This skill turns Claude into a knowledge engineer that constructs, maintains, and reasons over graph-structured data.

## Core Workflow

Every KG task follows this pipeline:

1. **Extract** - Pull entities and relationships from unstructured input
2. **Structure** - Normalize into nodes + edges with typed relationships
3. **Validate** - Check new facts against existing graph (adversarial)
4. **Store** - Write to JSON-LD graph format
5. **Query** - Traverse, search, and infer from the graph

## 1. Building a Knowledge Graph

### Entity Extraction

When given unstructured text, documents, or research:

1. Identify **entities** (nouns, proper nouns, concepts, actors, systems)
2. Identify **relationships** between entities (verbs, prepositions, causal links)
3. Identify **properties** of entities (attributes, measurements, states)

For each entity, capture:
- `id`: Unique snake_case identifier
- `type`: Category (person, organization, concept, technology, event, location, process, metric)
- `label`: Human-readable name
- `properties`: Key-value pairs of attributes
- `confidence`: How certain this extraction is (0.0-1.0)
- `source`: Where this fact came from

For each relationship, capture:
- `source`: Source entity ID
- `target`: Target entity ID
- `type`: Relationship type (see Edge Types below)
- `weight`: Strength of relationship (0.0-1.0)
- `evidence`: The text that supports this relationship

### Edge Types

Use these 10 standardized relationship types:

| Type | Meaning | Example |
|------|---------|---------|
| `causes` | A leads to B | "Inflation causes price increases" |
| `requires` | A needs B | "Deployment requires testing" |
| `contradicts` | A conflicts with B | "Study A contradicts Study B" |
| `supports` | A provides evidence for B | "Data supports hypothesis" |
| `contains` | A includes B | "Framework contains modules" |
| `precedes` | A comes before B | "Design precedes implementation" |
| `similar_to` | A resembles B | "React similar to Vue" |
| `derived_from` | A was created from B | "Summary derived from report" |
| `influences` | A affects B indirectly | "Policy influences behavior" |
| `instance_of` | A is an example of B | "Python instance of language" |

### Graph Schema (JSON-LD)

Always output graphs in this format:

```json
{
  "@context": {
    "@vocab": "https://schema.org/",
    "kg": "https://knowledge-graph.dev/schema/"
  },
  "@id": "kg:graph_name",
  "kg:version": "1.0",
  "kg:created": "2026-04-08T00:00:00Z",
  "kg:node_count": 0,
  "kg:edge_count": 0,
  "kg:nodes": [],
  "kg:edges": []
}
```

Node format:
```json
{
  "@id": "kg:entity_id",
  "@type": "kg:Concept",
  "kg:label": "Entity Name",
  "kg:properties": {"key": "value"},
  "kg:confidence": 0.95,
  "kg:source": "document.pdf"
}
```

Edge format:
```json
{
  "kg:source": "kg:entity_a",
  "kg:target": "kg:entity_b",
  "kg:type": "causes",
  "kg:weight": 0.8,
  "kg:evidence": "According to the report..."
}
```

## 2. Querying a Knowledge Graph

### Traversal Patterns

When the user asks a question about the graph, use these query patterns:

**Direct lookup** - Find a specific entity and its properties:
> "What do we know about X?" -> Find node, return properties + all connected edges

**Neighbor search** - Find entities related to a target:
> "What is related to X?" -> Return all nodes within 1-2 hops

**Path finding** - Find how two entities connect:
> "How does X relate to Y?" -> Find shortest path(s) between two nodes

**Type filter** - Find entities by category:
> "List all technologies" -> Filter nodes by @type

**Subgraph extraction** - Pull a focused subset:
> "Everything about topic X" -> Extract connected component around X

### Search Strategy: Two-Engine Pattern

For large graphs, search in two passes:

1. **Specific search first** (threshold 0.95) - Look for exact or near-exact matches in entity labels and properties
2. **General search fallback** (threshold 0.85) - If specific search returns nothing, broaden to fuzzy matching across all text fields

This prevents irrelevant results from drowning out precise matches.

### Gap Re-retrieval

When reasoning over a graph and you encounter a gap (a question the current subgraph can't answer):

1. Don't discard the question
2. Formulate it as a new search query
3. Search the full graph again with the refined query
4. Incorporate any new results into your reasoning

## 3. Adversarial Validation

Before adding ANY new fact to an existing graph, validate it against what's already known. This is the most important part of maintaining graph integrity.

### Validation Pipeline

For each new fact (node or edge):

**Step 1: Antonym detection**
- Check if the new fact's claims are antonyms of existing facts
- Example: New fact says "X increases Y" but graph says "X decreases Y"
- If detected: Flag as contradiction, do NOT add

**Step 2: Negation detection**
- Check if the new fact directly negates an existing fact
- Example: New fact says "X does not cause Y" but graph has edge X->causes->Y
- If detected: Flag as contradiction, present both with sources

**Step 3: Consistency check**
- Does the new fact's entity types match existing type assignments?
- Do numerical values fall within reasonable ranges of existing data?
- Are temporal claims consistent with existing timeline?

**Step 4: Source credibility**
- Compare source authority of new fact vs existing facts
- More recent + more authoritative source wins ties
- Always preserve both facts with sources when genuinely uncertain

### Contradiction Resolution

When a contradiction is found:

```
CONTRADICTION DETECTED:
  Existing: [entity] --[relationship]--> [entity] (source: X, date: Y)
  New:      [entity] --[relationship]--> [entity] (source: A, date: B)
  
  Resolution options:
  1. Keep existing (new source less authoritative)
  2. Replace with new (newer, more authoritative source)  
  3. Keep both (genuine disagreement, flag for review)
  4. Merge (partial overlap, combine properties)
```

Always present contradictions to the user rather than silently resolving them.

## 4. Reasoning Over Graphs

### Structured Reasoning Pipeline

When asked to analyze or draw conclusions from a knowledge graph, follow this 6-step deterministic process:

1. **OBSERVE** - Gather all relevant nodes and edges from the graph. List what you see without interpretation.

2. **CLASSIFY** - Categorize the entities and relationships. What patterns emerge? What clusters exist?

3. **HYPOTHESIZE** - Based on the graph structure, form testable hypotheses. What does the topology suggest?

4. **VERIFY** - Check each hypothesis against the graph data. Does the evidence support it? Look for counter-evidence.

5. **REFINE** - Narrow down to hypotheses that survived verification. Combine partial results.

6. **DECOMPOSE** - If the problem is too complex, break it into sub-problems and repeat steps 1-5 on each.

### Inference Rules

Apply these graph-based inferences:

- **Transitivity**: If A causes B and B causes C, then A indirectly causes C
- **Contradiction propagation**: If A supports B and B contradicts C, then A indirectly contradicts C
- **Cluster detection**: Densely connected subgraphs suggest a coherent topic or domain
- **Hub identification**: Nodes with many edges are key concepts - prioritize them in explanations
- **Bridge detection**: Nodes connecting two otherwise separate clusters are critical insights

### Confidence Propagation

When inferring indirect relationships:
- Multiply confidence scores along the path
- Example: A->B (0.9) and B->C (0.8) = A->C indirect confidence: 0.72
- Discard inferences below 0.5 confidence
- Always label inferred relationships as `"inferred": true`

## 5. Graph Maintenance

### When to Split a Graph

If a graph exceeds ~200 nodes, split into domain-specific subgraphs:
- Extract densely connected components
- Create a lightweight "index graph" that links subgraphs
- Each subgraph should be self-contained for its domain

### Merging Graphs

When combining two graphs:
1. Identify shared entities (same label or high similarity)
2. Merge shared nodes, combining properties
3. Run adversarial validation on conflicting properties
4. Connect the graphs through shared nodes
5. Update edge weights based on combined evidence

### Graph Health Metrics

Report these when asked about graph quality:
- **Node count** and **edge count**
- **Density**: edges / (nodes * (nodes-1))
- **Orphan nodes**: Nodes with zero edges (should be 0)
- **Average connectivity**: Mean edges per node
- **Contradiction count**: Known unresolved contradictions

## Output Format

When presenting graph results to the user:

**For small results (< 10 entities):** Show as a readable list with relationships
```
Entity A
  --causes--> Entity B (confidence: 0.9)
  --requires--> Entity C (confidence: 0.85)
```

**For medium results (10-50 entities):** Show as a summary table + key relationships

**For large results (50+ entities):** Show top-level clusters with counts, let user drill down

## Do's and Don'ts

**Do:**
- Always validate new facts before adding to existing graphs
- Preserve source attribution on every node and edge
- Use the 10 standardized edge types
- Present contradictions to the user
- Split large graphs into domain-specific subgraphs
- Search specific first, then broaden

**Don't:**
- Don't add facts without validation against existing knowledge
- Don't create edges without evidence
- Don't silently resolve contradictions
- Don't use custom edge types when a standard one fits
- Don't store the entire graph in SKILL.md context - use files
- Don't treat all sources as equally authoritative
