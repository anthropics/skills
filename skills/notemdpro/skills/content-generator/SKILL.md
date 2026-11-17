---
name: content-generator
description: "Use when a note has only a title and needs comprehensive AI-generated content, optionally enriched with web research context"
---

# NoteMD Pro - Generate Content from Title

## Overview

This feature generates comprehensive content for a note based solely on its title. It can optionally perform web research first, then generates detailed documentation including explanations, tables, equations (LaTeX), and Mermaid diagrams.

## When to Use

- **Create new notes**: Generate detailed content from a title
- **Expand outlines**: Turn brief titles into full documents
- **Research summaries**: Get comprehensive overviews with web context
- **Technical docs**: Generate scientific/technical documentation

## Function Call Chain

```
generateContentForTitle (fileUtils.ts)
├── getProviderForTask('generateTitle', settings)
├── _performResearch(app, settings, title, reporter)  [IF enabled]
│   ├── SearchManager.getProvider
│   ├── provider.search(query)
│   └── fetchContentFromUrl(url)
├── call[Provider]API(prompt, title + researchContext)
├── cleanupLatexDelimiters(content)
├── refineMermaidBlocks(content)  ← AUTO-FIX
└── fixMermaidSyntaxInFile(outputPath, reporter)  ← AUTO-RUN AFTER LLM
    └── checkMermaidErrors(content)
```

## Key Functions (from fileUtils.ts)

### generateContentForTitle

Generates content for a note based on its title using LLM.

```typescript
export async function generateContentForTitle(
  settings: NotemdSettings,
  inputPath: string,
  progressReporter: ProgressReporter,
);
```

### batchGenerateContentForTitles

Batch generates content for all markdown files in a folder.

```typescript
export async function batchGenerateContentForTitles(
  settings: NotemdSettings,
  folderPath: string,
  progressReporter: ProgressReporter,
);
// Flow:
// 1. Get all .md files in folder
// 2. Create "complete" output folder
// 3. Process files (serial or parallel based on settings)
// 4. Move processed files to complete folder
```

### fixMermaidSyntaxInFile

Fixes Mermaid syntax in a file (auto-run after generation).

```typescript
export async function fixMermaidSyntaxInFile(
  filePath: string,
  reporter: ProgressReporter,
): Promise<boolean>;
```

## Settings

### Research Settings

| Setting                           | Description                           |
| --------------------------------- | ------------------------------------- |
| `enableResearchInGenerateContent` | Enable web research before generation |
| `searchProvider`                  | 'tavily' or 'duckduckgo'              |
| `tavilyApiKey`                    | API key for Tavily                    |
| `maxResearchContentTokens`        | Max tokens for research context       |
| `tavilyMaxResults`                | Number of Tavily results              |
| `ddgMaxResults`                   | Number of DuckDuckGo results          |

### Contextual Context (Macro Settings)

| Setting                 | Description                                                             |
| ----------------------- | ----------------------------------------------------------------------- |
| `enableFocusedLearning` | Inject macro user domain preferences globally                           |
| `focusedLearningDomain` | The specific domain context (e.g., "Computer Graphics", "Biochemistry") |

### Output Settings

| Setting                              | Description                                |
| ------------------------------------ | ------------------------------------------ |
| `useCustomGenerateTitleOutputFolder` | Use custom output folder                   |
| `generateTitleOutputFolderName`      | Custom folder name (default: "\_complete") |

### Language Settings

| Setting                         | Description                   |
| ------------------------------- | ----------------------------- |
| `language`                      | Target language code          |
| `useDifferentLanguagesForTasks` | Per-task language selection   |
| `generateTitleLanguage`         | Language for title generation |

## Prompt Template (generateTitle)

From `promptUtils.ts`:

````
Create comprehensive technical documentation about "{TITLE}" with a focus on
scientific and mathematical rigor.
{RESEARCH_CONTEXT_SECTION}

Include:
1. Detailed explanation of core concepts with their mathematical foundations.
   Start with a Level 2 Header (## {TITLE}).
2. Key technical specifications with precise values and units (use tables).
3. Common use cases with quantitative performance metrics.
4. Implementation considerations with algorithmic complexity analysis.
5. Performance characteristics with statistical measures.
6. Related technologies with comparative mathematical models.
7. Mathematical equations in LaTeX format (using $$...$$ for display and
   $...$ for inline) with detailed explanations.
8. Mermaid.js diagram code blocks using the format ```mermaid ... ```
   IMPORTANT: without brackets "()" or "{}" for Mermaid diagrams.
   Enclosed node names with spaces/special characters in square brackets [ and ].
   Avoids special LaTeX syntax and Added quotes around subgraph titles.
   "subgraph" and "end" cannot appear on the same line!
9. Use bullet points for lists longer than 3 items.
10. Include references to academic papers with DOI where applicable.
11. Preserve all mathematical formulas and scientific principles.
12. Define all variables and parameters used in equations.

Format directly for Obsidian markdown. Do NOT wrap the entire response in
a markdown code block. Start directly with the Level 2 Header.
````

## Auto-Fix After Generation

After LLM generates content, the following fixes are automatically applied:

1. **cleanupLatexDelimiters**:
   - Converts `\( \) ` to `$`
   - Removes extra whitespace in math expressions
   - Protects display math `$$...$$`

2. **refineMermaidBlocks**:
   - Fixes unquoted labels
   - Closes unclosed blocks
   - Applies 20+ fix patterns

3. **fixMermaidSyntaxInFile** (auto-run):
   - Validates Mermaid syntax using `mermaid.parse`
   - Applies deep debug fixes if errors found
   - Logs validation results

See [notemd-mermaid-fix](../mermaid-fix/SKILL.md) for full Mermaid fixing code.

## Error Handling

### Common Errors

1. **No research context**
   - Warning: "Research for 'title' returned no results"
   - Solution: Check API keys, network connection

2. **Mermaid syntax errors**
   - Warning: "Mermaid errors found after generation"
   - Solution: Auto-fix applied, check logs

3. **Content too long**
   - Error: Max tokens exceeded
   - Solution: Reduce research context or chunk size
