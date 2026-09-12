---
name: link-analyzer
description: "Use when markdown notes need automatic wiki-link insertion for core concepts to build an interconnected knowledge graph"
---

# NoteMD Pro - Add Wiki-Links

## Overview

This feature processes markdown files to add wiki-links (`[[concept]]`) between related concepts using an LLM. It analyzes the content and identifies core knowledge points, then adds appropriate backlinks.

## When to Use

- **Organize notes**: Connect related concepts in your vault
- **Build knowledge graph**: Create interconnected notes for better navigation
- **Enhance linking**: Automatically add links that might be missed manually

## Function Call Chain

```
processFile (fileUtils.ts)
├── read_file(inputPath)
├── splitContent(content, settings)
├── getProviderForTask('addLinks', settings)
├── call[Provider]API(prompt, chunk)
├── createConceptNotes(settings, concepts, filename)
│   ├── normalizeNameForFilePath(concept)
│   └── write_file(notePath, content)
├── handleDuplicates(content, settings)
├── cleanupLatexDelimiters(content)
├── refineMermaidBlocks(content)  ← AUTO-FIX
└── saveOrMoveProcessedFile(settings, inputPath, content)
    └── write_file(outputPath, content)
```

## Key Functions (from fileUtils.ts)

### processFile

Processes a single file: reads content, calls LLM, adds links, applies fixes, and saves.

```typescript
export async function processFile(
  settings: NotemdSettings,
  inputPath: string,
  progressReporter: ProgressReporter,
  currentProcessingFileBasename: { value: string | null },
);
```

### splitContent

Splits content into chunks based on word count for LLM processing.

```typescript
export function splitContent(
  content: string,
  settings: NotemdSettings,
): string[];
// Returns: Array of content chunks
```

### saveOrMoveProcessedFile

Handles saving or moving the processed file based on settings.

```typescript
async function saveOrMoveProcessedFile(
  settings: NotemdSettings,
  inputPath: string,
  processedContent: string,
  progressReporter: ProgressReporter,
);
```

## Settings

### Core Settings

| Setting                     | Description                         |
| --------------------------- | ----------------------------------- |
| `chunkWordCount`            | Words per chunk (default: 2000)     |
| `maxTokens`                 | Max tokens for LLM response         |
| `moveOriginalFileOnProcess` | Move original file after processing |

### Output Settings

| Setting                        | Description                      |
| ------------------------------ | -------------------------------- |
| `useCustomProcessedFileFolder` | Use custom output folder         |
| `processedFileFolder`          | Custom output folder path        |
| `useCustomAddLinksSuffix`      | Use custom filename suffix       |
| `addLinksCustomSuffix`         | Custom suffix (e.g., "\_linked") |

### Mermaid/LaTeX Settings

| Setting                       | Description                         |
| ----------------------------- | ----------------------------------- |
| `removeCodeFencesOnAddLinks`  | Remove code fences after processing |
| `autoMermaidFixAfterGenerate` | Auto-fix Mermaid syntax             |

### Duplicate Detection

| Setting                    | Description                     |
| -------------------------- | ------------------------------- |
| `enableDuplicateDetection` | Enable duplicate word detection |

## Prompt Template (addLinks)

From `promptUtils.ts`:

```
Completely decompose and structure the knowledge points in this markdown document,
outputting them in markdown format supported by Obsidian. Core knowledge points
should be labelled with Obsidian's backlink format [[]]. Do not output anything
other than the original text and the requested "Obsidian's backlink format [[]]".

Rules:
1. Only add Obsidian backlinks [[like this]] to core concepts. Do not modify the
   original text content or formatting otherwise.
2. Skip conventional names (common products, company names, dates, times, individual
   names) unless they represent a core technical or scientific concept within the
   text's context.
3. Output the *entire* original content of the chunk, preserving all formatting
   (headers, lists, code blocks, etc.), with only the added backlinks.
4. Handle duplicate concepts carefully:
   a. If both singular and plural forms of a word/concept appear (e.g., "model" and
      "models"), only add the backlink to the *first occurrence* of the *singular* form.
   b. If a single-word concept also appears as part of a multi-word concept, only
      add the backlink to the multi-word concept.
   c. Do not add duplicate backlinks for the exact same concept within this chunk.
5. Ignore any "References", "Bibliography", or similar sections.
```

## Error Handling

### Common Errors

1. **No valid LLM provider**
   - Error: "No valid LLM provider configured for 'Add Links' task"
   - Solution: Configure a provider in settings

2. **API rate limiting**
   - Error: Rate limit exceeded
   - Solution: Adjust `apiCallInterval` in settings

3. **File permission errors**
   - Error: Cannot modify/create file
   - Solution: Check folder permissions

### Cancellation

- User can cancel processing via progress reporter
- Already processed chunks are preserved
- Progress saved in log

## Auto-fix Integration

After LLM processing, the following fixes are automatically applied:

1. **cleanupLatexDelimiters**: Fix LaTeX math delimiters
2. **refineMermaidBlocks**: Fix Mermaid diagram syntax
3. **Boxed content removal**: Remove `\boxed{` wrappers

See [notemd-mermaid-fix](../mermaid-fix/SKILL.md) for full Mermaid fixing code.
