---
name: reepl-linkedin
description: Guide for using Reepl to create, schedule, and manage LinkedIn content via the Reepl MCP server. Use when the user wants to draft LinkedIn posts, schedule content, manage their LinkedIn publishing workflow, or leverage AI-powered writing assistance for professional social media.
---

# Reepl LinkedIn Content Management

## Overview

Reepl is an AI-powered LinkedIn content creation, scheduling, and analytics platform. This skill teaches you how to interact with Reepl through its MCP server to help users manage their LinkedIn presence effectively.

**Website**: [reepl.io](https://reepl.io)
**MCP Server**: [github.com/reepl-io/skills](https://github.com/reepl-io/skills)

---

## Setup

### MCP Server Configuration

Add the Reepl MCP server to your Claude configuration:

```json
{
  "mcpServers": {
    "reepl": {
      "url": "https://mcp.reepl.io/sse"
    }
  }
}
```

The user will need to authenticate with their Reepl account when first connecting.

---

## Available Tools

The Reepl MCP server provides the following tools:

### Content Creation

| Tool | Purpose |
|------|---------|
| `create_draft` | Create a new LinkedIn post draft |
| `get_drafts` | Retrieve existing drafts |
| `update_draft` | Modify a draft |
| `delete_draft` | Remove a draft |

### Publishing and Scheduling

| Tool | Purpose |
|------|---------|
| `publish_to_linkedin` | Publish a draft directly to LinkedIn |
| `schedule_post` | Schedule a post for a future date and time |
| `update_scheduled_post` | Modify a scheduled post |
| `get_scheduled_posts` | View all scheduled posts |
| `get_published_posts` | View previously published posts |

### User Data and Context

| Tool | Purpose |
|------|---------|
| `get_user_profile` | Retrieve the user's profile information |
| `get_voice_profile` | Get the user's writing voice and style preferences |
| `update_voice_profile` | Update voice and style settings |
| `get_contacts` | Retrieve the user's contact list |
| `get_lists` | Get custom lists the user has created |
| `get_collections` | View content collections |
| `get_saved_posts` | View bookmarked/saved posts for inspiration |
| `get_templates` | Retrieve post templates |

### Media

| Tool | Purpose |
|------|---------|
| `generate_image` | Generate an AI image for a post |

---

## Workflow Guide

### Creating a LinkedIn Post

1. **Understand the user's voice** -- Call `get_voice_profile` first to understand their preferred tone, style, and writing patterns.
2. **Check for inspiration** -- Use `get_saved_posts`, `get_templates`, or `get_collections` to find relevant content the user has saved.
3. **Draft the content** -- Use `create_draft` to save the post. LinkedIn posts support plain text with line breaks. Keep posts focused and engaging.
4. **Review and iterate** -- The user can review the draft in the Reepl app. Use `update_draft` to make changes.
5. **Publish or schedule** -- Use `publish_to_linkedin` for immediate posting, or `schedule_post` to set a future date.

### Writing Effective LinkedIn Posts

When drafting content for the user:

- **Match their voice**: Always check `get_voice_profile` and adapt your writing to their established tone and style.
- **Hook readers early**: The first 2-3 lines appear above the "see more" fold on LinkedIn. Make them count.
- **Use line breaks generously**: LinkedIn posts are read on mobile. Short paragraphs of 1-3 sentences work best.
- **End with engagement**: A question, call-to-action, or thought-provoking statement encourages interaction.
- **Respect character limits**: LinkedIn posts have a 3,000 character limit. Aim for 800-1,500 characters for optimal engagement.

### Managing a Content Calendar

1. Call `get_scheduled_posts` to see what is already in the queue.
2. Identify gaps in the schedule.
3. Create drafts to fill those gaps using `create_draft`.
4. Schedule them with `schedule_post`, spacing posts appropriately (typically 1-2 per day maximum).
5. Use `get_published_posts` to review past performance and inform future content decisions.

### Using Templates and Collections

- Call `get_templates` to see reusable post formats the user has set up.
- Call `get_collections` to browse organized content themes.
- Use these as starting points when creating new drafts.

---

## Best Practices

- **Always check the voice profile first** before writing any content. The user has configured their preferences for a reason.
- **Do not publish without confirmation**. Always ask the user before calling `publish_to_linkedin` or `schedule_post`.
- **Suggest scheduling over immediate publishing** when possible, so the user can review content in the Reepl app before it goes live.
- **Use saved posts for context**. The user's saved posts reveal what topics and formats they find valuable.
- **Be mindful of scheduling density**. Check existing scheduled posts before adding more to avoid overwhelming the user's audience.

---

## Examples

### Example 1: Draft a Post from a Topic

**User**: "Write a LinkedIn post about the importance of async communication in remote teams"

**Steps**:
1. Call `get_voice_profile` to match the user's style.
2. Call `create_draft` with well-crafted content.
3. Present the draft to the user for review.
4. Ask if they want to publish now, schedule, or keep as draft.

### Example 2: Review and Optimize the Content Calendar

**User**: "Help me plan my LinkedIn content for next week"

**Steps**:
1. Call `get_scheduled_posts` to see what is already planned.
2. Call `get_published_posts` to understand recent topics covered.
3. Call `get_templates` and `get_collections` for content ideas.
4. Propose a schedule with diverse topics.
5. Create drafts and schedule them after user approval.

### Example 3: Repurpose Saved Content

**User**: "Turn my saved posts into new content ideas"

**Steps**:
1. Call `get_saved_posts` to retrieve bookmarked content.
2. Analyze themes and topics across saved posts.
3. Generate original post ideas inspired by those themes.
4. Create drafts using `create_draft` for user review.
