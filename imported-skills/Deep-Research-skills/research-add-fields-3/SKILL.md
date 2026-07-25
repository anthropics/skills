---
name: research-add-fields
user-invocable: true
description: Add field definitions to existing research outline.
allowed-tools: Bash, Read, Write, Glob, WebSearch, Task, AskUserQuestion
---

# Research Add Fields - Supplement Research Fields

## Trigger
`/research-add-fields`

## Workflow

### Step 1: Auto-locate Fields File
Find `*/fields.yaml` file in current working directory, auto-read existing fields definitions.

### Step 2: Get Supplement Source
Ask user to choose:
- **A. User direct input**: User provides field names and descriptions
- **B. Web Search**: Launch agent to search common fields in this domain

### Step 3: Display and Confirm
- Display suggested new fields list
- User confirms which fields to add
- User specifies field category and detail_level

### Step 4: Save Update
Append confirmed fields to fields.yaml, save file.

## Output
Updated `{topic}/fields.yaml` file (in-place modification, requires user confirmation)
