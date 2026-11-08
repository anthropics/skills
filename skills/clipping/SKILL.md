---
name: clipping
description: Clip web content to Obsidian vault.
version: 0.1.0
license: MIT
---

# Web Clipper

Capture content, file in Obsidian. Use `hermes-clip`.

## Usage

```bash
hermes-clip --url "URL" --title "TITLE" --content "MARKDOWN" --folder "SUBFOLDER" [--tags "TAGS"] [--mode "unique|merge|overwrite"]
```

## Logic

1. **Extract:** 
   - Navigate URL.
   - Read first 4k chars for categorization.
   - Extract full Markdown.
   - Identify topic, author, themes.

2. **Search Vault:**
   - Check `VAULT_STRUCTURE.md` index first.
   - Search notes (`grep -rl "source: [URL]"`).
   - If exists AND mode is `unique` → stop. Report path.
   - If exists AND mode is `merge` → Proceed to extract and append.
   - New topic → Set folder, use `mode="unique"`.

3. **Categorize:**
   - Logical folder tree (e.g. `Reference/Coding/React`).
   - Tags from content.

4. **Run:**
   - Call `hermes-clip`.
   - Report `path` + `uri`.

## Reasoning
"Clip React Hooks. Found 'React' folder, no 'Hooks' note. Create 'Reference/Coding/React/Hooks.md'. Tags #react #javascript."
