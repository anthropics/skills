---
name: mermaid-healer
description: "Use when mermaid diagrams have syntax errors like broken arrows, unquoted labels, or malformed subgraphs that cause render failures"
---

# NoteMD Pro - Mermaid Diagram Fixing

## Overview

This skill fixes Mermaid diagram syntax errors in markdown files. It includes comprehensive fixing logic for 20+ common Mermaid syntax issues including unquoted labels, malformed arrows, nested brackets, and more.

## When to Use

- **Fix broken diagrams**: Repair Mermaid syntax errors in notes
- **Auto-fix after generation**: Automatically fix diagrams after LLM content generation
- **Batch repair**: Fix multiple files at once

## Function Call Chain

````
refineMermaidBlocks (mermaidProcessor.ts)
├── split content by lines
├── detect ```mermaid blocks
├── apply fix rules in order:
│   ├── fixSmartQuotes
│   ├── fixMermaidPipes
│   ├── fixMermaidNotes
│   ├── fixNotesToNodes
│   ├── fixMalformedArrows
│   ├── fixInvalidArrows
│   ├── mergeDoubleLabels
│   ├── fixMissingBrackets
│   ├── fixInlineSubgraphs
│   ├── fixMermaidComments
│   ├── fixDoubleSlashComments
│   ├── fixUnquotedNodeLabels
│   ├── fixIntermediateNodes
│   ├── fixDoubledID
│   ├── fixExcessiveBrackets
│   ├── fixSemicolonPositioning
│   ├── fixConcatenatedLabels
│   ├── fixUnquotedLabelsWithSemicolons
│   ├── enhancedNoteAndSemicolonCleanup
│   ├── fixReverseArrows
│   ├── fixSubgraphDirection
│   ├── fixDuplicateLabels
│   ├── fixNestedMermaidQuotes
│   ├── fixQuotedLabelsAfterSemicolon
│   ├── fixDoubleDashToArrow
│   ├── fixTargetedNotes
│   ├── fixDoubleArrowLabels
│   ├── fixUnquotedEdgeLabels
│   ├── fixShapeMismatch
│   ├── fixPlaceholderArtifacts
│   └── fixBlankArrows
├── close unclosed blocks
└── checkMermaidErrors (if errors found, apply deepDebugMermaid)

cleanupLatexDelimiters (mermaidProcessor.ts)
├── protect escaped dollars
├── convert \( \) to $
├── trim whitespace in math
└── restore escaped dollars
````

## Code File

The full TypeScript code is available in: `mermaidProcessor.ts`

This file contains all the fix functions:

- `refineMermaidBlocks()` - Main entry point
- `checkMermaidErrors()` - Validate syntax
- `cleanupLatexDelimiters()` - Fix LaTeX
- `deepDebugMermaid()` - Apply all fix passes
- 20+ individual fix functions

## Auto-Fix Integration

### After Generate (generate SKILL.md)

After LLM generates content, these functions are automatically called:

1. `cleanupLatexDelimiters(content)`
2. `refineMermaidBlocks(content)`
3. `fixMermaidSyntaxInFile(app, file, reporter)` - Validates and reports errors

### Manual Fix

Call `refineMermaidBlocks(content)` on any markdown content to fix Mermaid syntax.

## Fix Patterns

### 1. Unquoted Labels with Nested Brackets

```
Input:  Investment[Corporate Investment "[企业投资]"]
Output: Investment["Corporate Investment [企业投资]"]
```

### 2. Broken Edge Labels

```
Input:  CapRate --["Inverse Relationship["--> PropValue
Output: CapRate -- "Inverse Relationship" --> PropValue
```

### 3. Arrow Fixes

```
Input:  A --|> B
Output: A --> B
```

### 4. Comment Conversion

```
Input:  A --> B; % Comment
Output: A -- "Comment" --> B;
```

### 5. Note Transformations

```
Input:  note right of A: Text
Output: A -- "Text" --> (as label)
```

### 6. Excessive Brackets

```
Input:  A["Text"]]]
Output: A["Text"]
```

## Usage Example

```typescript
import {
  refineMermaidBlocks,
  cleanupLatexDelimiters,
} from "./mermaidProcessor";

// Fix Mermaid in content
const content = `...
\`\`\`mermaid
graph LR
A[Node --> B]
\`\`\`
...`;

const fixed = await refineMermaidBlocks(content);
const cleaned = cleanupLatexDelimiters(fixed);
```

## Error Detection

The `checkMermaidErrors()` function uses `mermaid.parse()` to validate syntax:

```typescript
const errorCount = await checkMermaidErrors(content);
// Returns: number of errors found
```

If errors remain after basic fixes, `deepDebugMermaid()` is applied.

## 🚀 Primary Engine: 37+ Heuristic Regex Fixers

> [!IMPORTANT] Proven Regex Supremacy
> Based on empirical field testing, **the AI Agent must prioritize the 37 manual heuristic regex fixers** (like `fixMissingBrackets`, `fixReverseArrows`) over directly asking the LLM to fix the diagram. Current Large Reasoning Models often struggle to repair structural Mermaid hallucinations directly. The regex pipeline has been proven to be the most robust method for correcting diagram flows in production.

### Workflow

```
LLM-Heal-Mermaid
├── Extract mermaid blocks from content
├── Try mermaid.parse() to validate
├── IF errors found
│   ├── Extract specific error messages
│   ├── Feed errors back to LLM with prompt
│   └── Ask for precise correction
├── Replace original block with LLM-fixed version
└── Validate again
```

### Implementation

````typescript
import mermaid from "mermaid";

async function llmHealMermaid(
  content: string,
  llmCall: Function,
): Promise<string> {
  // Extract mermaid blocks
  const blockRegex = /```mermaid\n([\s\S]*?)```/g;

  let fixedContent = content;
  let match;

  while ((match = blockRegex.exec(content)) !== null) {
    const block = match[1];

    // Try to parse
    try {
      await mermaid.parse(block);
    } catch (error) {
      // Get specific error
      const errorMsg = error.message;
      console.log(`Mermaid error: ${errorMsg}`);

      // Ask LLM to fix
      const fixPrompt = `Fix the following Mermaid diagram syntax. 
Error: ${errorMsg}
Diagram:
${block}

Rules:
1. Use proper bracket syntax: nodeId["Label"]
2. Use proper arrow syntax: -->
3. Quote labels with special characters
4. Close all blocks properly

Fixed diagram:`;

      const fixed = await llmCall(fixPrompt);

      // Replace in content
      fixedContent = fixedContent.replace(block, fixed);
    }
  }

  return fixedContent;
}
````

### LLM Fix Prompt Template

```
Fix the following Mermaid diagram syntax error.

Error message from Mermaid parser:
{ERROR_MESSAGE}

Current broken diagram:
{BROKEN_DIAGRAM}

Please fix the syntax and return only the corrected Mermaid code.
Do not include any explanations or markdown code blocks.
```

### Advantages

1. **Handles edge cases**: LLM can understand complex errors
2. **Adaptive**: Improves with better prompts
3. **Less maintenance**: No need for 37+ regex patterns
4. **Context-aware**: Understands diagram semantics

### Two-Stage Approach (Regex First, LLM as Last Resort)

Recommended: Always execute the complete battery of regex fixers first. Only escalate to the LLM if `mermaid.parse()` still fails after the regex cascade.

```typescript
async function healMermaid(
  content: string,
  llmCall: Function,
): Promise<string> {
  // Stage 1: Exhaustive Regex Heuristics (Primary Engine)
  let fixed = refineMermaidBlocks(content);

  // Stage 2: Strict Validation
  const errors = await checkMermaidErrors(fixed);

  // Stage 3: LLM Fallback (Use only when heuristics fail)
  if (errors > 0) {
    console.log(
      `Found ${errors} residual errors after regex cascade, falling back to LLM...`,
    );
    fixed = await llmHealMermaid(fixed, llmCall);
  }

  return fixed;
}
```

### When LLM Fallback is Necessary

- **Complex nested structures**: Subgraphs with multiple levels
- **Custom shapes**: Non-standard node definitions
- **Edge cases**: Rare syntax combinations
- **Semantic errors**: Valid syntax but wrong diagram logic
