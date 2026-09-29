---
name: model-audit
description: Print the complete AI model routing table for your product. Every AI call, what model it actually uses, and the cost per call. Use when touching AI models, changing providers, or reviewing API costs.
license: Apache-2.0
---


Audit every AI model call in the codebase and output a complete routing table.

## Steps

### 1. Find the model config
Search for where models are configured. Common patterns:
```bash
grep -r "gpt-4\|claude\|gemini\|anthropic\|openai" --include="*.py" --include="*.ts" --include="*.js" -l
grep -r "MODEL\|model_config\|AI_MODEL\|LLM" --include="*.py" --include="*.ts" -l
```
Read those files. Understand the alias → actual model name mapping.
Example: an alias `"fast"` might map to `"gpt-4o-mini"`, an alias `"quality"` to `"claude-opus-4-6"`.

### 2. Find every AI call in the codebase
Search for API call patterns:
```bash
grep -rn "\.chat\.completions\.create\|anthropic\.messages\|genai\.\|\.generate\|embeddings\.create" --include="*.py" --include="*.ts" --include="*.js"
```
Also search for your specific client/wrapper function names found in step 1.

For each call, note:
- Which feature/endpoint triggers it
- Which model alias or model name is passed
- Roughly what it does (generation, embedding, classification, etc.)

### 3. Cross-reference alias → actual model name
Using the config from step 1, resolve every alias to the real model name being sent to the API.

### 4. Look for unused model configs
Any model configured but never called from a user-facing feature? Flag it.

### 5. Output the routing table

```
AI MODEL ROUTING — [your product name]
════════════════════════════════════════════════════════════════
FEATURE                    ALIAS/KEY       ACTUAL MODEL
────────────────────────────────────────────────────────────────
[feature name]             [alias]         [real model name]
[feature name]             [alias]         [real model name]
...
════════════════════════════════════════════════════════════════

UNUSED CONFIG (defined but never called from frontend):
  [alias] → [model name]

FLAGS:
  ⚠️  [anything unexpected, deprecated models, mismatches]
```

### 6. Flag problems
- Any alias pointing to a model that's been deprecated or renamed
- Any feature using an expensive model where a cheaper one would work
- Any hardcoded model names scattered around the codebase instead of going through the central config (these are the ones that don't get updated when you change models)
- Inconsistency: same task using different models in different places

### 7. If the user asks for recommendations
Suggest where swapping to a cheaper/faster model would have low risk (simple tasks, high volume, latency-sensitive) and where quality matters more (user-facing generation, complex reasoning).
