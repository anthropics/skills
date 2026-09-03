---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-knowledge-base
name: firecrawl-knowledge-base
description: Build a knowledge base from web content with Firecrawl. Use for local reference docs, RAG-ready chunks, fine-tuning datasets, documentation mirrors, topic corpora, or LLM-ready markdown organized from web sources.
license: ISC
metadata:
  author: firecrawl
  version: "0.1.0"
  homepage: https://www.firecrawl.dev
  source: https://github.com/firecrawl/firecrawl-workflows
inputs:
  - name: FIRECRAWL_API_KEY
    description: Firecrawl API key for hosted Firecrawl requests.
    required: true
---

# Firecrawl Knowledge Base

Use this to turn URLs or topics into organized LLM-ready content.

## Onboarding Interview

Infer the source, goal, depth, and output location from context. If the source and goal are clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the source URL/topic, whether the output is reference/RAG/training/docs, or training format if training is requested.

## Firecrawl Collection Plan

Use Firecrawl map for documentation sites, search for topic-based corpora, scrape pages into markdown, and preserve code examples and tables.

For files, follow the Firecrawl download-style convention:

```text
.firecrawl/
  <hostname>/
    <path>/
      index.md
```

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners:

- one docs section per researcher
- official docs, tutorials, community discussions, and references by source type
- source scraping vs chunk generation vs manifest generation

## Output Modes

- Reference: markdown files, `index.md`, and `sources.json`.
- RAG: markdown files plus chunk files and `manifest.json`.
- Training: scraped source files plus `training-data.jsonl` and `training-metadata.json`.
- Docs mirror: complete markdown mirror with a table of contents.

## Final Deliverable

```markdown
# Knowledge Base: [Source]

## Summary
[What was collected and why]

## Output Structure
[Files/directories created]

## Coverage
[Sections, source types, counts]

## Usage Notes
[How to use in RAG, docs, training, or agent context]

## Sources
[URLs collected]

## Rerun Inputs
workflow: firecrawl-knowledge-base
source: [url/topic]
goal: [reference/rag/train/docs]
depth: [quick/thorough/exhaustive]
output_dir: [.firecrawl/]
```

## Quality Bar

- Preserve code examples and formatting.
- Remove boilerplate navigation where possible.
- Include source URLs in frontmatter or metadata.
