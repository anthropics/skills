---
name: concept-extractor
description: "Use to exhaustively extract core knowledge concepts, scientific terms, and specialized vocabulary from a document to build a comprehensive wiki-linked knowledge graph."
---

# NoteMD Pro - Concept Extraction (Agentic Workflow)

## Overview

This skill transforms standard Markdown text into an interconnected Knowledge Graph by **exhaustively** extracting every relevant concept and generating atomic notes with proper backlinks.

## ⚠️ Critical Rule: Exhaustive Extraction

When executing this skill, **DO NOT STOP at 3 to 5 concepts**. You must thoroughly scan the entire document and extract **every single** core knowledge point, technical term, scientific principle, proper noun, and specialized vocabulary word. A comprehensive document (e.g., 1000 words) might yield 15-30 distinct concepts.

Your goal is to be as complete and reasonable as possible, ensuring the end-user's Knowledge Graph is densely populated and highly interconnected.

## Step-by-Step Agent Instructions

When the user asks you to extract concepts from a specific Markdown file (or text), follow these steps strictly:

### Step 1: Comprehensive Parsing

Read the entire target document thoroughly. Mentally (or in your scratchpad) list every concept following these criteria:

- **Scientific & Technical Terms:** e.g., "DNA Replication", "Ribosome", "Stellar Nucleosynthesis", "Isotope", "Spectroscopy", "Amino Acid".
- **Theories & Principles:** e.g., "Statistical Mechanics", "Conservation of Energy".
- **Proper Nouns & Tools:** e.g., "Tesseract OCR", "Python multiprocessing", "Markdown".
- **Abstract Concepts:** Limit abstract ideas unless they are central to the domain. Focus on specific noun-phrases.
- **Normalization:** Always normalize to the singular form (e.g., "Isotope" instead of "Isotopes") and capitalize Title Case (e.g., "DNA Replication").

### Step 2: Generate Atomic Concept Notes

For _every single concept_ you identified in Step 1, create a separate atomic note file in the target directory (often a `Concepts/` folder or the same folder as the source).

**Filename:** `[Concept Name].md`

**Content Format:**

```markdown
# [Concept Name]

Brief 1-2 sentence definition or summary of the concept (derive this from your internal knowledge base or the source text context).

## Linked From

- [[Name of the Original Source File]]
```

_(Note: Always append the exact name of the file you are extracting from to the `## Linked From` section, wrapped in `[[wiki-links]]`)_

### Step 3: Inject Wiki-Links into Source

After creating the atomic concept notes, you must run the `link-analyzer` skill (or do it manually if instructed) to go back into the original source file and wrap the occurrences of those concepts with Obsidian wiki-links: `[[Concept Name|original text]]`.

---

## Output Quality Checklist for the Agent

- [ ] Did I extract _all_ possible valid concepts, or did I stop early out of laziness? (Aim for exhaustive depth).
- [ ] Are the concepts normalized to singular, Title Case forms?
- [ ] Did I create an individual `.md` file for every extracted concept?
- [ ] Did I add the `## Linked From` backlink in every concept note?
