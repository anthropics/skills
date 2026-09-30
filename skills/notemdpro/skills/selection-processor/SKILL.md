---
name: selection-processor
description: "Use when processing only a selected portion of text rather than a full file, to save tokens and enable targeted AI operations"
---

# NoteMD Pro - Selection-Based Processing

## Overview

This skill enables processing of selected text portions within files, rather than forcing full-file rewrites. This saves tokens, reduces processing time, and allows targeted AI operations on specific sections.

## When to Use

- **Partial content generation**: Generate content for just a section
- **Selective linking**: Add links to specific paragraphs
- **Targeted translation**: Translate selected portions
- **Efficient processing**: Save tokens by processing only what's needed

## Function Call Chain

```
Process Selection
├── Get selected text from editor
├── Get surrounding context (optional)
├── Process selected content (LLM)
├── Replace or append selected content
└── Update file
```

## Selection Processing Patterns

### 1. Get Selected Text
```typescript
// From Obsidian editor
const editor = view.editor;
const selection = editor.getSelection();

// From VS Code
const selection = editor.selection;
const text = editor.document.getText(selection);
```

### 2. Process with Context
For better results, include surrounding context:
```typescript
// Get context before and after selection
const lineNum = editor.getCursor().line;
const beforeLines = editor.getRange({line: 0, ch: 0}, {line: lineNum, ch: 0});
const afterLines = editor.getRange({line: lineNum, ch: 0}, {line: maxLine, ch: 0});
const fullContext = beforeLines + selection + afterLines;
```

### 3. Replace Selection
```typescript
// Replace selected text with processed result
editor.replaceSelection(processedContent);

// Or append after selection
editor.replaceRange('\n\n' + processedContent, {line: lineNum + 1, ch: 0});
```

## Use Cases

### Wiki-Link from Selection
```typescript
// Selected: "Machine learning is a subset of AI"
// Process: Add links to key concepts
// Result: "Machine learning is a subset of [[AI]]"
async function addLinksToSelection(app: App, editor: Editor) {
    const selection = editor.getSelection();
    const prompt = getSystemPrompt('addLinks');
    const result = await callLLM(prompt, selection);
    editor.replaceSelection(result);
}
```

### Generate from Selection
```typescript
// Selected: "Neural Networks"
// Process: Generate expanded content
// Result: Full explanation of neural networks
async function generateFromSelection(app: App, editor: Editor) {
    const selection = editor.getSelection();
    const prompt = getSystemPrompt('generateTitle', {TITLE: selection});
    const result = await callLLM(prompt, '');
    editor.replaceSelection(result);
}
```

### Translate Selection
```typescript
// Selected: Some text in English
// Process: Translate to target language
// Result: Translated text
async function translateSelection(app: App, editor: Editor, targetLang: string) {
    const selection = editor.getSelection();
    const prompt = getSystemPrompt('translate', {LANGUAGE: targetLang, TEXT: selection});
    const result = await callLLM(prompt, '');
    editor.replaceSelection(result);
}
```

## Settings

### Selection Processing
| Setting | Description |
|---------|-------------|
| `includeContextLines` | Number of context lines to include |
| `replaceSelection` | Replace or append processed content |
| `preserveFormatting` | Preserve original formatting |

### Context Options
| Setting | Description |
|---------|-------------|
| `contextBefore` | Lines before selection |
| `contextAfter` | Lines after selection |
| `includeHeadings` | Include parent headings |

## Error Handling

### Common Errors

1. **Empty selection**
   - Error: No text selected
   - Solution: Check selection length before processing

2. **Selection too large**
   - Error: Exceeds token limits
   - Solution: Split into chunks or use full file mode

3. **Invalid cursor position**
   - Error: Cannot determine insertion point
   - Solution: Check editor state before operations

## Platform-Agnostic Approach

### Web/Node.js
```javascript
// Get selection from DOM
const selection = window.getSelection().toString();

// Process with file system
const content = fs.readFileSync(filepath, 'utf-8');
// Find and replace range
```

### CLI (Standard Input/Output)
```bash
# Pipe selected content to script
echo "$SELECTED_TEXT" | notemd-process --operation=links

# Output replaces stdin
```

## Best Practices

1. **Always validate selection**: Check if selection is non-empty
2. **Provide context**: Include surrounding text for better results
3. **Preserve formatting**: Maintain markdown structure
4. **Preview before replace**: Show preview for user confirmation
5. **Undo support**: Ensure easy rollback if needed
