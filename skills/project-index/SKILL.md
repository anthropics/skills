---
name: project-index
description: >
  Maintains a live, visual index of all conversations, artifacts, and key
  questions within a Claude project. Use this skill whenever the user asks to
  "update the index", "actualiza el índice", "show project summary", "what
  conversations do we have", "create a project index", "resumen del proyecto",
  or any similar request to get an overview of project activity. Also trigger
  when a user enters a conversation designated as the project index and greets
  Claude or says they want to review what's been done. Always use this skill
  proactively when the conversation title contains words like "índice", "index",
  "resumen", or "summary" and the user asks what has been worked on.
compatibility:
  tools:
    - recent_chats
    - conversation_search
    - visualize:show_widget
    - visualize:read_me
---

# Project Index Skill

Generates and updates a visual, interactive index of all conversations in the
current Claude project. The index includes: conversation titles with direct
links, dates, artifact inventory, and the key questions answered in each
conversation.

---

## When this skill activates

- User says "actualiza el índice", "update the index", or similar
- User is in the designated index conversation and asks for an overview
- User asks "what have we worked on", "show me the project summary", etc.
- A new conversation is starting and the user wants to orient themselves

---

## Step 1 — Fetch all project conversations

Use `recent_chats` to retrieve the full conversation history. Start with n=20.
If the project is large, paginate using the `before` parameter.

For each conversation, note:
- `uri` → used to build the direct URL: `https://claude.ai/chat/{uri}`
- `updated_at` → for sorting and date display
- Content snippets → to extract title, artifacts, and key questions

---

## Step 2 — Extract structured data per conversation

For each conversation, identify:

**Title** — use the explicit title if available, otherwise infer from the first
user message or dominant topic.

**Date** — format as `DD mmm YYYY` from `updated_at`.

**Artifacts** — scan for tool calls or outputs that produced files or widgets:
- `present_files` calls → Word (.docx), PDF, Excel (.xlsx), PowerPoint (.pptx)
- `visualize:show_widget` calls → interactive HTML widgets or diagrams
- `create_file` calls → any other generated file
- Note artifact type with an emoji: 📄 Word, 🗂 Widget/diagram, 🗺 HTML map,
  📊 Excel, 📑 PDF, 💻 Code file

**Key questions
