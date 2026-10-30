# Knowledge Graph Schemas Reference

## Complete Node Schema

```json
{
  "@id": "kg:<unique_snake_case_id>",
  "@type": "kg:<EntityType>",
  "kg:label": "Human Readable Name",
  "kg:description": "Brief description of this entity",
  "kg:properties": {
    "key1": "value1",
    "key2": 42,
    "key3": true
  },
  "kg:confidence": 0.95,
  "kg:source": "origin document or URL",
  "kg:created": "ISO-8601 timestamp",
  "kg:updated": "ISO-8601 timestamp",
  "kg:tags": ["tag1", "tag2"],
  "kg:aliases": ["alternate name", "abbreviation"]
}
```

### Entity Types

| Type | Use For | Examples |
|------|---------|---------|
| `Person` | Named individuals | CEO, researcher, author |
| `Organization` | Companies, teams, agencies | Anthropic, US Army, MIT |
| `Concept` | Abstract ideas, theories | Machine learning, sovereignty |
| `Technology` | Tools, frameworks, systems | Rust, Kubernetes, CUDA |
| `Event` | Things that happened | Product launch, incident |
| `Location` | Physical or virtual places | Data center, AWS region |
| `Process` | Workflows, procedures | CI/CD pipeline, review process |
| `Metric` | Measurements, KPIs | Latency, accuracy, revenue |
| `Document` | Reports, papers, specs | Whitepaper, RFC, patent |
| `Component` | Parts of a larger system | API endpoint, module, layer |

## Complete Edge Schema

```json
{
  "@id": "kg:edge_<source>_<type>_<target>",
  "kg:source": "kg:<source_entity_id>",
  "kg:target": "kg:<target_entity_id>",
  "kg:type": "<relationship_type>",
  "kg:weight": 0.8,
  "kg:evidence": "The supporting text or citation",
  "kg:confidence": 0.9,
  "kg:source_doc": "Where this relationship was found",
  "kg:created": "ISO-8601 timestamp",
  "kg:bidirectional": false,
  "kg:inferred": false,
  "kg:inference_path": []
}
```

### Relationship Types - Detailed

| Type | Direction | Inverse | Transitive? |
|------|-----------|---------|-------------|
| `causes` | A -> B | `caused_by` | Yes |
| `requires` | A -> B | `required_by` | Yes |
| `contradicts` | A <-> B | `contradicts` | No |
| `supports` | A -> B | `supported_by` | No |
| `contains` | A -> B | `contained_in` | Yes |
| `precedes` | A -> B | `follows` | Yes |
| `similar_to` | A <-> B | `similar_to` | No |
| `derived_from` | A -> B | `derives` | No |
| `influences` | A -> B | `influenced_by` | Weak |
| `instance_of` | A -> B | `has_instance` | No |

### Transitivity Rules

When `transitive: yes`, if A->B and B->C, then A->C can be inferred:
- **Confidence decay**: Multiply confidences along the path (0.9 * 0.8 = 0.72)
- **Max chain length**: 3 hops (beyond this, confidence is too low)
- **Mark as inferred**: Always set `"inferred": true` with the `inference_path`

## Complete Graph Schema

```json
{
  "@context": {
    "@vocab": "https://schema.org/",
    "kg": "https://knowledge-graph.dev/schema/"
  },
  "@id": "kg:<graph_name>",
  "@type": "kg:KnowledgeGraph",
  "kg:version": "1.0",
  "kg:name": "Graph Display Name",
  "kg:description": "What this graph covers",
  "kg:domain": "primary domain (e.g., cybersecurity, finance)",
  "kg:created": "ISO-8601 timestamp",
  "kg:updated": "ISO-8601 timestamp",
  "kg:node_count": 0,
  "kg:edge_count": 0,
  "kg:sources": ["list of source documents"],
  "kg:nodes": [],
  "kg:edges": [],
  "kg:metadata": {
    "density": 0.0,
    "avg_connectivity": 0.0,
    "orphan_count": 0,
    "contradiction_count": 0,
    "cluster_count": 0
  }
}
```

## Subgraph / Index Graph Schema

When a graph is split into domain-specific subgraphs:

```json
{
  "@id": "kg:index",
  "@type": "kg:IndexGraph",
  "kg:subgraphs": [
    {
      "@id": "kg:subgraph_name",
      "kg:domain": "domain name",
      "kg:node_count": 42,
      "kg:edge_count": 67,
      "kg:key_entities": ["entity_a", "entity_b"],
      "kg:bridge_nodes": ["shared_entity_1"]
    }
  ],
  "kg:cross_references": [
    {
      "kg:source_graph": "kg:subgraph_a",
      "kg:target_graph": "kg:subgraph_b",
      "kg:shared_entities": ["entity_id"]
    }
  ]
}
```

## Validation Report Schema

Output of adversarial validation:

```json
{
  "validation_result": "accepted" | "contradiction" | "flagged",
  "new_fact": {
    "entity": "what was proposed",
    "claim": "what it asserts"
  },
  "checks": [
    {
      "check_type": "antonym" | "negation" | "consistency" | "source",
      "passed": true | false,
      "details": "Explanation of what was checked",
      "conflicting_fact": null | {"entity": "...", "claim": "..."}
    }
  ],
  "resolution": "accepted" | "rejected" | "needs_review",
  "recommendation": "Human-readable recommendation"
}
```
