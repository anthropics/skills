---
name: first-time-setup
description: First-time setup flow for baoyu-danger-x-to-markdown preferences
---

# First-Time Setup

## Overview

When no EXTEND.md is found, guide user through preference setup.

**BLOCKING OPERATION**: This setup MUST complete before ANY other workflow steps. Do NOT:
- Start converting tweets or articles
- Ask about URLs or output paths
- Proceed to any conversion

ONLY ask the questions in this setup flow, save EXTEND.md, then continue.

## Setup Flow

```
No EXTEND.md found
        |
        v
+---------------------+
| AskUserQuestion     |
| (all questions)     |
+---------------------+
        |
        v
+---------------------+
| Create EXTEND.md    |
+---------------------+
        |
        v
    Continue conversion
```

## Questions

**Language**: Use user's input language or saved language preference.

Use AskUserQuestion with ALL questions in ONE call:

### Question 1: Download Media

```yaml
header: "Media"
question: "How to handle images and videos in tweets?"
options:
  - label: "Ask each time (Recommended)"
    description: "After saving markdown, ask whether to download media"
  - label: "Always download"
    description: "Always download media to local imgs/ and videos/ directories"
  - label: "Never download"
    description: "Keep original remote URLs in markdown"
```

### Question 2: Default Output Directory

```yaml
header: "Output"
question: "Default output directory?"
options:
  - label: "x-to-markdown (Recommended)"
    description: "Save to ./x-to-markdown/{username}/{tweet-id}.md"
```

Note: User will likely choose "Other" to type a custom path.

### Question 3: Save Location

```yaml
header: "Save"
question: "Where to save preferences?"
options:
  - label: "User (Recommended)"
    description: "~/.baoyu-skills/ (all projects)"
  - label: "Project"
    description: ".baoyu-skills/ (this project only)"
```

## Save Locations

| Choice | Path | Scope |
|--------|------|-------|
| User | `~/.baoyu-skills/baoyu-danger-x-to-markdown/EXTEND.md` | All projects |
| Project | `.baoyu-skills/baoyu-danger-x-to-markdown/EXTEND.md` | Current project |

## After Setup

1. Create directory if needed
2. Write EXTEND.md
3. Confirm: "Preferences saved to [path]"
4. Continue with conversion using saved preferences

## EXTEND.md Template

```md
download_media: [ask/1/0]
default_output_dir: [path or empty]
```

## Modifying Preferences Later

Users can edit EXTEND.md directly or delete it to trigger setup again.
