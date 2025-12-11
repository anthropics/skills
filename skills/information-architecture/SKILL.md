---
name: information-architecture
description: Expert knowledge from "Information Architecture for the Web and Beyond" by Louis Rosenfeld, Peter Morville, and Jorge Arango. Use when analyzing, evaluating, or improving information architecture for web applications, mobile apps, or digital products. Applies when users request IA audits, navigation redesigns, content organization strategies, search system improvements, or comprehensive IA assessments. Essential for creating findable and understandable information environments.
---

# Information Architecture for the Web and Beyond

This skill provides comprehensive knowledge from the authoritative "polar bear book" on information architecture, focused on making digital products findable and understandable.

## When to Use This Skill

Use this skill when:
- Analyzing existing information architecture of web apps or digital products
- Creating IA improvement plans or recommendations
- Designing navigation systems, organization schemes, or labeling systems
- Evaluating content findability and understandability
- Developing search strategies or metadata frameworks
- Creating IA documentation or strategy deliverables

## Book Structure

The reference book is organized into three parts covering 13 chapters:

**Part I: Introducing Information Architecture**
- Chapter 1: The Problems That Information Architecture Addresses
- Chapter 2: Defining Information Architecture
- Chapter 3: Design for Finding
- Chapter 4: Design for Understanding

**Part II: Basic Principles of Information Architecture**
- Chapter 5: The Anatomy of an Information Architecture
- Chapter 6: Organization Systems
- Chapter 7: Labeling Systems
- Chapter 8: Navigation Systems
- Chapter 9: Search Systems
- Chapter 10: Thesauri, Controlled Vocabularies, and Metadata

**Part III: Getting Information Architecture Done**
- Chapter 11: Research
- Chapter 12: Strategy
- Chapter 13: Design and Documentation

## How to Use the Reference Book

The complete text is available at `references/Information_Architecture_-_Louis_Rosenfeld.md` (Markdown with extracted figures in `references/assets/`).

### Recommended Approach for IA Analysis

1. **Start with fundamentals** - Read Chapters 1-2 to understand core IA principles
2. **Identify specific issues** - Based on the project, target relevant chapters:
   - Navigation problems → Chapter 8
   - Content organization → Chapter 6
   - Labeling/terminology → Chapter 7
   - Search functionality → Chapter 9
   - Metadata strategy → Chapter 10
3. **Apply methodology** - Use Chapters 11-13 for research, strategy, and documentation approaches

### Search Patterns for Common IA Tasks

Use these ripgrep patterns to quickly find relevant content in the reference book:

**For navigation design:**
```bash
rg -i -n "navigation|browsing|wayfinding" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**For organization schemes:**
```bash
rg -i -n "organization scheme|taxonomy|categorization|hierarchy" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**For labeling systems:**
```bash
rg -i -n "label|terminology|naming" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**For search systems:**
```bash
rg -i -n "search|query|indexing|retrieval" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**For metadata and vocabularies:**
```bash
rg -i -n "metadata|controlled vocabulary|thesaur|ontology" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**For research methods:**
```bash
rg -i -n "research|user testing|card sorting|interview" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**For strategy and documentation:**
```bash
rg -i -n "strategy|wireframe|blueprint|deliverable" references/Information_Architecture_-_Louis_Rosenfeld.md
```

**With context (show surrounding lines):**
```bash
rg -i -n -C 3 "your search term" references/Information_Architecture_-_Louis_Rosenfeld.md
```

## Key Concepts to Apply

When analyzing a web application's IA:

1. **Findability** - Can users locate information effectively?
2. **Understandability** - Do users comprehend the organization and meaning?
3. **Cross-channel coherence** - Is the experience consistent across devices/contexts?
4. **Systems thinking** - How do components interact as an ecosystem?
5. **User needs** - Does the IA support information-seeking behaviors?

## Producing IA Improvement Plans

When creating improvement recommendations:

1. **Assess current state** - Document existing IA structures and identify issues
2. **Apply IA principles** - Reference specific chapters and concepts from the book
3. **Prioritize recommendations** - Focus on high-impact improvements
4. **Provide concrete examples** - Show before/after or specific redesign suggestions
5. **Consider implementation** - Reference Chapter 13 for documentation approaches

## Core IA Components to Evaluate

For any web application analysis, evaluate these systems:

- **Organization systems** (Chapter 6) - How content is grouped and structured
- **Labeling systems** (Chapter 7) - How content is represented and named
- **Navigation systems** (Chapter 8) - How users browse and understand location
- **Search systems** (Chapter 9) - How users search and retrieve information
- **Metadata & vocabularies** (Chapter 10) - How content is tagged and described

## Reading the Reference Book

To access specific content from the book:

```bash
# View a specific line range (e.g., Chapter 6 on Organization Systems starts ~line 2307)
view references/Information_Architecture_-_Louis_Rosenfeld.md --view_range [start_line, end_line]

# Search for specific concepts with ripgrep (faster and better output than grep)
rg -i -n -C 5 "concept keyword" references/Information_Architecture_-_Louis_Rosenfeld.md

# Search with preview context
rg -i "concept" references/Information_Architecture_-_Louis_Rosenfeld.md -C 10
```

## Important Notes

- The book uses web-focused examples but principles apply to all digital products
- Cross-channel design considerations are covered throughout (mobile, apps, IoT)
- Examples may reference older technologies, but underlying principles remain current
- Focus on semantic structures and user needs rather than specific UI patterns
