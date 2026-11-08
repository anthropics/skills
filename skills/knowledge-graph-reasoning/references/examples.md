# Knowledge Graph Examples

## Example 1: Building a KG from a Research Summary

### Input
> "Transformer architectures, introduced by Vaswani et al. in 2017, revolutionized NLP. 
> They replaced RNNs by using self-attention mechanisms. BERT, built on transformers, 
> achieved state-of-the-art on 11 NLP benchmarks. GPT-3, also transformer-based, 
> demonstrated few-shot learning capabilities. However, transformers have quadratic 
> memory complexity, which limits context length."

### Extracted Graph

```json
{
  "@context": {"@vocab": "https://schema.org/", "kg": "https://knowledge-graph.dev/schema/"},
  "@id": "kg:transformer_research",
  "kg:version": "1.0",
  "kg:created": "2026-04-08T00:00:00Z",
  "kg:node_count": 7,
  "kg:edge_count": 8,
  "kg:nodes": [
    {"@id": "kg:transformer", "@type": "kg:Technology", "kg:label": "Transformer Architecture", "kg:properties": {"year": 2017, "authors": "Vaswani et al."}, "kg:confidence": 1.0},
    {"@id": "kg:self_attention", "@type": "kg:Concept", "kg:label": "Self-Attention Mechanism", "kg:confidence": 1.0},
    {"@id": "kg:rnn", "@type": "kg:Technology", "kg:label": "Recurrent Neural Network", "kg:confidence": 1.0},
    {"@id": "kg:bert", "@type": "kg:Technology", "kg:label": "BERT", "kg:properties": {"benchmarks_won": 11}, "kg:confidence": 1.0},
    {"@id": "kg:gpt3", "@type": "kg:Technology", "kg:label": "GPT-3", "kg:confidence": 1.0},
    {"@id": "kg:few_shot_learning", "@type": "kg:Concept", "kg:label": "Few-Shot Learning", "kg:confidence": 0.95},
    {"@id": "kg:quadratic_complexity", "@type": "kg:Metric", "kg:label": "Quadratic Memory Complexity", "kg:properties": {"impact": "limits context length"}, "kg:confidence": 1.0}
  ],
  "kg:edges": [
    {"kg:source": "kg:transformer", "kg:target": "kg:self_attention", "kg:type": "contains", "kg:weight": 1.0, "kg:evidence": "using self-attention mechanisms"},
    {"kg:source": "kg:transformer", "kg:target": "kg:rnn", "kg:type": "contradicts", "kg:weight": 0.8, "kg:evidence": "replaced RNNs"},
    {"kg:source": "kg:bert", "kg:target": "kg:transformer", "kg:type": "derived_from", "kg:weight": 1.0, "kg:evidence": "built on transformers"},
    {"kg:source": "kg:gpt3", "kg:target": "kg:transformer", "kg:type": "derived_from", "kg:weight": 1.0, "kg:evidence": "also transformer-based"},
    {"kg:source": "kg:gpt3", "kg:target": "kg:few_shot_learning", "kg:type": "supports", "kg:weight": 0.9, "kg:evidence": "demonstrated few-shot learning capabilities"},
    {"kg:source": "kg:quadratic_complexity", "kg:target": "kg:transformer", "kg:type": "influences", "kg:weight": 0.9, "kg:evidence": "limits context length"},
    {"kg:source": "kg:transformer", "kg:target": "kg:rnn", "kg:type": "precedes", "kg:weight": 0.7, "kg:evidence": "replaced RNNs", "kg:inferred": true},
    {"kg:source": "kg:bert", "kg:target": "kg:gpt3", "kg:type": "similar_to", "kg:weight": 0.7, "kg:evidence": "both transformer-based"}
  ]
}
```

### Readable Output

```
Transformer Architecture (2017, Vaswani et al.)
  --contains--> Self-Attention Mechanism (1.0)
  --contradicts--> RNN (0.8, "replaced RNNs")
  
BERT (11 benchmarks)
  --derived_from--> Transformer Architecture (1.0)
  --similar_to--> GPT-3 (0.7)

GPT-3
  --derived_from--> Transformer Architecture (1.0)
  --supports--> Few-Shot Learning (0.9)

Quadratic Memory Complexity
  --influences--> Transformer Architecture (0.9, "limits context length")
```

## Example 2: Adversarial Validation

### Existing Graph Fact
```
Transformer Architecture --contradicts--> RNN (0.8)
  Evidence: "Transformers replaced RNNs by using self-attention"
```

### New Fact Proposed
> "RNNs outperform transformers on small sequential datasets"

### Validation Result

```json
{
  "validation_result": "flagged",
  "new_fact": {
    "entity": "rnn",
    "claim": "outperforms transformers on small sequential datasets"
  },
  "checks": [
    {
      "check_type": "antonym",
      "passed": true,
      "details": "No direct antonym conflict. Existing fact says 'replaced' (architectural choice), new fact says 'outperforms' (performance metric). Different dimensions."
    },
    {
      "check_type": "negation",
      "passed": true,
      "details": "No direct negation. 'Replaced' does not mean 'worse in all cases'."
    },
    {
      "check_type": "consistency",
      "passed": true,
      "details": "Claim is scoped to 'small sequential datasets', which is a subset. Consistent with general replacement while having niche advantages."
    },
    {
      "check_type": "source",
      "passed": false,
      "details": "New fact has no cited source. Existing fact comes from Vaswani et al. Flag for source verification."
    }
  ],
  "resolution": "needs_review",
  "recommendation": "The claim is plausible (RNNs can outperform on small sequential tasks) but needs a source citation. Add with reduced confidence (0.7) and flag for verification, or request source from user."
}
```

## Example 3: Graph Query - Path Finding

### Question
> "How does self-attention relate to few-shot learning?"

### Traversal
```
Self-Attention --[contained_in]--> Transformer
Transformer <--[derived_from]-- GPT-3
GPT-3 --[supports]--> Few-Shot Learning
```

### Answer
```
Path found (3 hops):
  Self-Attention → (contained in) Transformer → (basis for) GPT-3 → (supports) Few-Shot Learning
  
  Path confidence: 1.0 * 1.0 * 0.9 = 0.90
  
  Interpretation: Self-attention is the core mechanism in transformers, 
  which enabled GPT-3, which demonstrated few-shot learning. The attention 
  mechanism's ability to capture long-range dependencies is a key enabler 
  of in-context learning.
```

## Example 4: Graph Health Report

```
Graph: transformer_research
  Nodes: 7 | Edges: 8
  Density: 0.19 (sparse - expected for a small domain graph)
  Orphan nodes: 0 (good)
  Avg connectivity: 2.3 edges/node
  Hub nodes: Transformer Architecture (5 edges) - central concept
  Bridge nodes: None (single cluster)
  Contradictions: 0
  Inferred edges: 1 (Transformer --precedes--> RNN)
  
  Health: GOOD - No orphans, no contradictions, clear hub structure
```
