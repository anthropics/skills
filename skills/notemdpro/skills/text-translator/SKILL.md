---
name: text-translator
description: "Use when translating markdown notes to a different language while preserving formatting, images, and special elements"
---

# NoteMD Pro - Translation

## Overview

This feature translates markdown notes to different languages using LLM. It supports single file translation, batch folder translation, and preserves markdown formatting and special elements like images.

## When to Use

- **Multi-language vault**: Create translated versions of notes
- **Language learning**: Translate content for study
- **International collaboration**: Share notes across languages
- **Content localization**: Adapt content for different audiences

## Function Call Chain

```
translateFile (translate.ts)
├── read_file(inputPath)
├── splitContent(content, settings)
├── getProviderForTask('translate', settings)
├── callLLM(provider, prompt, chunk)
│   └── Translated chunk
├── join translated chunks
├── save translated file
│   └── write_file(outputPath, content)
└── open file (if enabled)

batchTranslateFolder
├── filter .md files in folder
├── createConcurrentProcessor
├── processFile for each file
└── ProgressModal reporting
```

## Key Functions (from translate.ts)

### translateFile

Translates a single file to target language.

```typescript
export async function translateFile(
  settings: NotemdSettings,
  inputPath: string,
  targetLanguage: string,
  progressReporter: ProgressReporter,
  openFile?: boolean,
  signal?: AbortSignal,
): Promise<string | null>;
// Returns: Path to translated file
```

### batchTranslateFolder

Translates all markdown files in a folder.

```typescript
export async function batchTranslateFolder(
  settings: NotemdSettings,
  folderPath: string,
  targetLanguage: string,
): Promise<void>;
```

## Settings

### Translation Settings

| Setting             | Description                  |
| ------------------- | ---------------------------- |
| `translateProvider` | LLM provider for translation |
| `translateModel`    | Model for translation        |

### Output Settings

| Setting                        | Description                          |
| ------------------------------ | ------------------------------------ |
| `useCustomTranslationSuffix`   | Use custom filename suffix           |
| `translationCustomSuffix`      | Custom suffix (e.g., "\_es", "\_fr") |
| `useCustomTranslationSavePath` | Use custom save path                 |
| `translationSavePath`          | Custom save path                     |

### Language Settings

| Setting              | Description                 |
| -------------------- | --------------------------- |
| `language`           | Default language code       |
| `availableLanguages` | List of supported languages |

## Prompt Template (translate)

From `promptUtils.ts`:

```
Translate the following text to {LANGUAGE}.
Only output the translated text.
Do not include the original text.
Note: For special image formats, please retain them as they are,
for example: ![](images/3c6d56a5dd52751121cefd4868e7b3a3ceb929b566eb63fc931a335d85a0095e.jpg)

Text to translate:
{TEXT}
```

## Supported Languages

The plugin supports multiple languages including:

- English (en)
- Spanish (es)
- French (fr)
- German (de)
- Chinese (zh)
- Japanese (ja)
- Korean (ko)
- And more...

## Output File Naming

| Setting        | Example Input               | Output                 |
| -------------- | --------------------------- | ---------------------- |
| Default suffix | `note.md`                   | `note_es.md`           |
| Custom suffix  | `note.md`                   | `note.es.md`           |
| Custom path    | `note.md` + `translations/` | `translations/note.md` |

## Error Handling

### Common Errors

1. **No provider configured**
   - Error: "No provider configured for translation"
   - Solution: Configure translate provider in settings

2. **Empty file**
   - Warning: "File is empty"
   - Solution: Check source file content

3. **Translation timeout**
   - Error: "Translation cancelled"
   - Solution: Reduce chunk size, check network

### Cancellation

- Users can cancel translation via AbortSignal
- Already translated chunks are preserved
- Partial results not saved on cancellation
