---
name: notemdpro
description: "NoteMD Pro skill pack for markdown knowledge workflows: linking, generation, research, translation, concept extraction, diagram generation, and syntax healing."
license: Complete terms in LICENSE.txt
---

# NoteMD Pro - Skill Router

## Overview

`notemdpro` is a portable skill library that mirrors modern NotEMD workflows for non-Obsidian runtimes.
Use this file as the top-level router to select the correct skill folder.

## Workflow Decision Tree

### Content + Knowledge Graph
- Add wiki-links to existing notes -> `skills/link-analyzer/SKILL.md`
- Generate long-form content from title/topic -> `skills/content-generator/SKILL.md`
- Extract core concepts from documents -> `skills/concept-extractor/SKILL.md`
- Process a selected excerpt instead of full file -> `skills/selection-processor/SKILL.md`

### Research + Translation
- Perform web research and summarize findings -> `skills/web-researcher/SKILL.md`
- Translate documents while preserving markdown -> `skills/text-translator/SKILL.md`

### Diagram Workflows
- Summarize document into Mermaid mindmap -> `skills/mermaid-summarizer/SKILL.md`
- Generate canonical diagram flow (NotEMD parity): `generate-diagram`
- Legacy compatibility alias (NotEMD parity): `generate-experimental-diagram` -> normalize to `generate-diagram`
- Preview command parity reference: `preview-diagram` (UI/runtime-specific in plugin; keep as conceptual action in skill docs)

### Syntax Healing
- Heal Mermaid syntax with regex-first pipeline -> `skills/mermaid-healer/SKILL.md`
- Heal LaTeX math formatting -> `skills/formula-healer/SKILL.md`

### Extraction + Batch
- Extract Q&A or targeted passages -> `skills/qa-extractor/SKILL.md`
- Run workflows over many files safely -> `skills/batch-processor/SKILL.md`

### Architecture + Engineering
- Understand system composition and call chains -> `skills/system-architecture/SKILL.md`
- Apply TDD workflow for new changes -> `skills/test-driven-development/SKILL.md`

## Skills Index

| Skill Folder | Purpose |
| --- | --- |
| `skills/link-analyzer` | Add/update `[[wiki-links]]` in markdown |
| `skills/content-generator` | Generate technical markdown from title/topic |
| `skills/web-researcher` | Web research + synthesis |
| `skills/text-translator` | Translate markdown content |
| `skills/concept-extractor` | Extract concept nodes for graph building |
| `skills/qa-extractor` | Extract answers from reference text |
| `skills/selection-processor` | Process selected text spans only |
| `skills/mermaid-summarizer` | Create Mermaid summary diagrams |
| `skills/mermaid-healer` | Repair Mermaid syntax |
| `skills/formula-healer` | Repair LaTeX syntax |
| `skills/batch-processor` | Batch execution patterns |
| `skills/system-architecture` | Runtime architecture map |
| `skills/test-driven-development` | TDD planning and execution |

## Prompt Variable Reference

| Variable | Typical Use |
| --- | --- |
| `{TITLE}` | Title-driven generation |
| `{LANGUAGE}` | Translation/target output language |
| `{TEXT}` | Raw content payload |
| `{REFERENCE_CONTENT}` | Reference corpus for extraction |
| `{USER_INPUT}` | Query/question payload |
| `{TOPIC}` | Research topic |
| `{SEARCH_RESULTS_CONTEXT}` | Search snippets/context |

## Notes

- Keep workflows file-system agnostic: avoid direct Obsidian API assumptions when running outside plugin runtime.
- For diagram command migration, prefer canonical action naming (`generate-diagram`, `preview-diagram`) and keep legacy alias compatibility where needed.
