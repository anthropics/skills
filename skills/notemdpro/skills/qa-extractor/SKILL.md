---
name: qa-extractor
description: "Use when extracting verbatim answers to specific questions from a long document, with optional translation of extracted text"
---

# NoteMD Pro - Text Extraction (Q&A)

## Overview

This feature extracts specific answers from markdown files based on user-configured questions. It uses LLM to analyze the content and provide precise answers to each question.

## When to Use

- **Q&A extraction**: Get specific answers from long documents
- **Data mining**: Extract structured information from unstructured text
- **Survey analysis**: Parse responses to multiple questions
- **Research**: Pull key findings from papers

## Function Call Chain

```
extractOriginalText (extractOriginalText.ts)
├── read_file(inputPath)
├── settings.extractQuestions (split by newlines)
├── getProviderAndModelForTask('extractOriginalText')
├── IF mergedMode
│   └── callLLM with all questions combined
├── ELSE (individual mode)
│   └── for each question
│       └── callLLM with single question
├── Format results
└── save to output file
    ├── mkdir_p(outputFolderPath)
    └── write_file(outputPath, content)
```

## Key Function (from extractOriginalText.ts)

### extractOriginalText

Extracts answers to configured questions from a file.

```typescript
export async function extractOriginalText(
  plugin: NotemdPlugin,
  inputPath: string,
  reporter: ProgressReporter,
): Promise<void>;
// Outputs: File with Q&A extracted
```

## Settings

### Question Configuration

| Setting                         | Description                           |
| ------------------------------- | ------------------------------------- |
| `extractQuestions`              | Questions to ask (one per line)       |
| `extractOriginalTextMergedMode` | Process all questions in one LLM call |

### Provider Settings

| Setting                       | Description                 |
| ----------------------------- | --------------------------- |
| `extractOriginalTextProvider` | LLM provider for extraction |
| `extractOriginalTextModel`    | Model for extraction        |
| `extractOriginalTextLanguage` | Language for output         |

### Contextual Context (Macro Settings)

| Setting                 | Description                                           |
| ----------------------- | ----------------------------------------------------- |
| `enableFocusedLearning` | Inject macro user domain preferences globally         |
| `focusedLearningDomain` | The specific domain context (e.g., "Quantum Physics") |

### Output Settings

| Setting                              | Description            |
| ------------------------------------ | ---------------------- |
| `extractOriginalTextUseCustomOutput` | Use custom output path |
| `extractOriginalTextCustomPath`      | Custom output folder   |
| `extractOriginalTextCustomSuffix`    | Custom filename suffix |

### Translation

| Setting                              | Description              |
| ------------------------------------ | ------------------------ |
| `translateExtractOriginalTextOutput` | Translate extracted text |

## Prompt Templates (extractOriginalText)

### Individual Mode

```
You are a strict Data Extraction and Verification Agent.
Your task is to extract the answer to the user's question from the provided reference content.

Reference Content:
{REFERENCE_CONTENT}

User Question:
{USER_INPUT}

Instructions:
1. Answer ONLY based on the reference content provided
2. If the answer is not found, state "Answer not found in the provided text"
3. Be precise and concise
4. Include relevant context if necessary
```

### Merged Mode

```
You are a strict Data Extraction and Verification Agent.
Your task is to extract answers to ALL questions from the provided reference content.

Reference Content:
{REFERENCE_CONTENT}

Questions:
{USER_INPUT}

Instructions:
1. Answer EACH question based ONLY on the reference content
2. Format each answer as: "Q: [question] A: [answer]"
3. If the answer is not found for a question, state "Answer not found"
4. Be precise and concise
```

## Output Format

### Individual Mode Output

```
Q: [Question 1]
A: [Answer 1]

Q: [Question 2]
A: [Answer 2]
```

### Merged Mode Output

```
1. [Question 1]
[Answer 1]

2. [Question 2]
[Answer 2]
```

## Processing Modes

### Individual Mode (Default)

- Processes each question separately
- More accurate for complex questions
- Higher API usage

### Merged Mode

- Combines all questions in one call
- Faster processing
- Less accurate for complex questions

## Error Handling

### Common Errors

1. **No questions configured**
   - Error: "No questions configured in settings for extraction"
   - Solution: Add questions in plugin settings

2. **Empty file**
   - Error: Cannot extract from empty file
   - Solution: Check source file content

3. **API errors**
   - Error: LLM API failure
   - Solution: Check API key, network, retry

### Best Practices

1. **Specific questions**: Use clear, specific questions
2. **Limit questions**: 5-10 questions per file works best
3. **Check output**: Always verify extracted answers
