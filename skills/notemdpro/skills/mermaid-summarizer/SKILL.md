---
name: mermaid-summarizer
description: "Use when summarizing a document into a visual Mermaid mindmap diagram for study aids or knowledge mapping"
---

# NoteMD Pro - Summarize as Mermaid Diagram

## Overview

This feature converts markdown document content into a Mermaid mindmap diagram. It uses LLM to analyze the document structure and generate a hierarchical mindmap with summaries and key sentences.

## When to Use

- **Visual summaries**: Create visual mindmaps of documents
- **Outline generation**: Generate hierarchical structure
- **Study aids**: Create visual study guides
- **Knowledge mapping**: Map relationships between ideas

## Function Call Chain

```
summarizeToMermaidCommand (main.ts)
├── read_file(inputPath)
├── getProviderAndModelForTask('summarizeToMermaid')
├── getPromptForTask('summarizeToMermaid')
├── call[Provider]API(prompt, content)
├── saveMermaidSummaryFile(settings, inputPath, mermaidContent)
│   ├── mkdir_p(outputFolderPath)
│   └── write_file(outputPath, content)
└── [Optional] Translate output
```

## Key Functions

### summarizeToMermaidCommand (main.ts)

Main command handler for summarization.

### saveMermaidSummaryFile (fileUtils.ts)

Saves the generated mermaid content to a file.

```typescript
export async function saveMermaidSummaryFile(
  settings: NotemdSettings,
  inputPath: string,
  mermaidContent: string,
  progressReporter: ProgressReporter,
): Promise<string>;
```

## Settings

### Provider Settings

| Setting                      | Description                    |
| ---------------------------- | ------------------------------ |
| `summarizeToMermaidProvider` | LLM provider for summarization |
| `summarizeToMermaidModel`    | Model for summarization        |
| `summarizeToMermaidLanguage` | Language for output            |

### Contextual Context (Macro Settings)

| Setting                 | Description                                                 |
| ----------------------- | ----------------------------------------------------------- |
| `enableFocusedLearning` | Inject macro user domain preferences globally               |
| `focusedLearningDomain` | The specific domain context (e.g., "Software Architecture") |

### Output Settings

| Setting                               | Description                       |
| ------------------------------------- | --------------------------------- |
| `useCustomSummarizeToMermaidSuffix`   | Use custom filename suffix        |
| `summarizeToMermaidCustomSuffix`      | Custom suffix (default: "\_summ") |
| `useCustomSummarizeToMermaidSavePath` | Use custom save path              |
| `summarizeToMermaidSavePath`          | Custom save path                  |

### Translation

| Setting                             | Description              |
| ----------------------------------- | ------------------------ |
| `translateSummarizeToMermaidOutput` | Translate mermaid output |
| `disableAutoTranslation`            | Disable auto-translation |

## Prompt Template (summarizeToMermaid)

Full prompt from `promptUtils.ts`:

````
You are an AI assistant specializing in text analysis and data visualization.
Your sole task is to act as a processor that converts the user-provided
document into a single, comprehensive Mermaid diagram.

The most important point is: Delete all parentheses.
Parentheses are not allowed in Mermaid diagrams.

Primary Instructions:
- Analyze and Summarize: Read the entire provided document to understand
  its structure and identify its primary sections and key ideas.
- Generate Mermaid Diagram Only: Your entire output must be a single
  Mermaid code block. Do not include any titles, explanations,
  greetings, or any text whatsoever outside of the mermaid ... block.

Critical Syntax Rules for Obsidian Compatibility:
1. Diagram Type: The diagram must begin with the mindmap keyword on the first line.
2. Hierarchy via Indentation: The structure of the mind map is defined
   only by indentation. Use a consistent four (4) spaces for each level.
3. Root Node: The first node after the mindmap declaration should be
   the root, with its text enclosed in double parentheses: root(("Title")).
4. No List Markers: Never use hyphens (-), double hyphens (--),
   asterisks (*), or any other characters to denote list items.
5. Character Replacement: Replace --> with "to" or "implies" to avoid conflicts.

Content and Structure Rules:
- Hierarchical Structure: Mirror the document structure
- Root: Document's title as root node
- Section Branches: Each major section as primary branch
- Section Summary: Maximum 5 summary points per section (max 300 words each)
- Key Sentences: Critical verbatim sentences from each section

Example Output Format:
```mermaid
mindmap
    Article Title
        Section 1: Title of the First Section
            Summary Point 1 for Section 1
            Summary Point 2 for Section 1
            Key Sentences
                Critical sentence from section 1.
                Another critical sentence.
        Section 2: Title of the Second Section
            Summary Point 1 for Section 2
            Key Sentences
                Critical sentence from section 2.
````

````

## Output Example

Input: A document about Machine Learning
Output:
```mermaid
mindmap
    Machine Learning
        Introduction to ML
            Definition and types of machine learning
            Supervised vs unsupervised learning
            Key Sentences
                Machine learning is a subset of artificial intelligence.
        Neural Networks
            Structure of neurons
            Activation functions
            Key Sentences
                Neural networks are inspired by biological neurons.
        Applications
            Computer vision
            Natural language processing
            Key Sentences
                ML powers many modern applications.
````

## Integration with Auto-fix

After generating mermaid, the output can be auto-fixed using:

- `refineMermaidBlocks()` - Fix syntax errors
- `checkMermaidErrors()` - Validate syntax

See [notemd-mermaid-fix](../mermaid-fix/SKILL.md) for details.

## Error Handling

### Common Errors

1. **Parentheses in content**
   - Issue: LLM includes parentheses in mermaid
   - Solution: Prompt instructs to remove all parentheses

2. **Invalid syntax**
   - Issue: Mermaid syntax errors in output
   - Solution: Auto-fix applied, check validation

3. **Large documents**
   - Issue: Content too long for single call
   - Solution: Use chunking (if implemented)
