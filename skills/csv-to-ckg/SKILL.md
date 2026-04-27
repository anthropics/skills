---
name: csv-to-ckg
description: Transform a CSV or structured data file into a Compact Knowledge Graph (CKG). Use when the user provides a CSV, spreadsheet, API data, or any structured dataset and wants to convert it to CKG format for LLM retrieval. Handles schema detection, dependency inference, taxonomy labeling, and .md context generation.
argument-hint: [path/to/file.csv or data description]
---

# CSV → CKG Transformation

You are transforming structured data into a Compact Knowledge Graph (CKG) — a DAG-based representation optimized for LLM retrieval at minimal token cost.

## Target Output Format

The CKG has two outputs:
1. **`learning-graph.csv`** — the machine-readable graph
2. **`ckg_context.md`** — the compressed markdown context sent to the LLM

### learning-graph.csv schema
```
ConceptID,ConceptLabel,Dependencies,TaxonomyID
1,ConceptName,2|5|7,CATEGORY
```
- `ConceptID`: integer, sequential
- `ConceptLabel`: clean noun phrase, no punctuation
- `Dependencies`: pipe-delimited IDs of prerequisite/parent concepts (empty if root)
- `TaxonomyID`: ALL_CAPS category label (FOUND=foundational, CORE=core, ADV=advanced, or domain-specific)

### ckg_context.md format (compressed markdown)
```markdown
# [Domain] Knowledge Graph
Concepts: N | Edges: E | Taxonomy: [categories]

## Taxonomy
- CATEGORY: ConceptA, ConceptB, ConceptC

## Dependencies
- ConceptA → ConceptB, ConceptC
- ConceptD → ConceptE

## Cross-references
- ConceptA ↔ ConceptD [relationship type]
```

## Transformation Steps

1. **Read the input file** — detect delimiter, headers, data types
2. **Identify concept column** — the primary entity/label column becomes ConceptLabel
3. **Infer dependencies** — look for:
   - Explicit parent/child columns
   - Foreign key relationships
   - Hierarchical fields (category > subcategory > item)
   - Temporal or logical ordering that implies prerequisites
4. **Assign TaxonomyIDs** — cluster concepts by type, domain area, or importance tier
5. **Assign ConceptIDs** — topological sort so dependencies always reference lower IDs
6. **Generate learning-graph.csv** — write the full CSV
7. **Generate ckg_context.md** — compressed markdown with taxonomy, dependency list, and cross-references
8. **Report stats** — N concepts, E edges, taxonomy breakdown, estimated token count for the context

## Key Rules

- Every concept must have a ConceptID even if it has no dependencies
- Dependencies must reference existing ConceptIDs only — no forward references in the CSV
- TaxonomyID should reflect domain logic, not just frequency (e.g. FOUND = things everything else depends on)
- The .md context must be human-readable AND LLM-parseable — no jargon abbreviations without expansion
- Target token count: under 600 tokens for the full context (check with rough word count ÷ 0.75)
- If the source data has more than 200 rows, ask the user whether to build a full graph or a representative sample

## After generating

Show the user:
1. The full `learning-graph.csv` content (or first 30 rows if large)
2. The full `ckg_context.md`
3. Token estimate and comparison: "This context is ~X tokens vs. ~Y tokens for a RAG chunk-based approach"
4. Suggested T1–T5 query types that would work well on this graph

If the source data is ambiguous about dependencies, state your assumptions explicitly and ask for confirmation before proceeding.
