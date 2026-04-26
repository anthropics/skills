---
name: user-preferences-template
description: |
  Template skill for personal user preferences. Use this as a starting point
  to create your own user preference skills for Claude.
  This skill demonstrates how to configure personal communication style,
  coding preferences, and workflow habits.
---

# User Preferences Template

This is a template for creating personal user preference skills. Copy this template to your `~/.claude/skills/` directory and customize it.

## How to Use This Template

1. Copy this folder to `~/.claude/skills/my-preferences/`
2. Rename and edit the `SKILL.md` file
3. Customize the sections below for your needs
4. Claude will automatically load these preferences

---

## Communication Style

### Language Preference
- Preferred language: [Your language, e.g., English, Dutch, Spanish]
- Technical terms: [Keep in English / Translate to preferred language]
- Formality level: [Casual / Professional / Technical]

### Response Format
- Preferred length: [Concise / Detailed / Adaptive]
- Use bullet points: [Yes / No / When appropriate]
- Include code examples: [Always / When relevant / On request]

---

## Coding Preferences

### General Style
- Indentation: [2 spaces / 4 spaces / tabs]
- Naming convention: [camelCase / snake_case / PascalCase]
- Comments: [Minimal / Moderate / Detailed]

### Preferred Technologies
- Languages: [List your preferred languages]
- Frameworks: [List your preferred frameworks]
- Tools: [List your preferred tools]

### Code Quality
- Always include: [types / tests / error handling]
- Avoid: [specific patterns you dislike]

---

## Workflow Preferences

### Task Approach
- Planning: [Always plan first / Jump into coding / Ask me]
- Testing: [TDD / Test after / Only when requested]
- Documentation: [Inline comments / README updates / Both / Minimal]

### Communication During Tasks
- Progress updates: [Frequent / Milestones only / Final result]
- Questions: [Ask immediately / Batch questions / Assume and proceed]
- Explanations: [Always explain / Only when asked / Brief summaries]

---

## Example Customizations

Replace the bracketed sections above with your actual preferences. Here's an example:

```markdown
## Communication Style

### Language Preference
- Preferred language: Dutch for explanations, English for code
- Technical terms: Keep in English
- Formality level: Professional but friendly

### Response Format
- Preferred length: Concise with option to expand
- Use bullet points: When appropriate for lists
- Include code examples: Always for technical questions
```

---

## Tips for Effective User Preferences

1. **Be Specific**: Vague preferences are less effective
2. **Prioritize**: List most important preferences first
3. **Include Examples**: Show what you want, not just describe it
4. **Update Regularly**: Refine based on your experience
5. **Keep It Focused**: Don't try to cover everything at once
