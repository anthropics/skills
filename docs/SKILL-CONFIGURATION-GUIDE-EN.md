# Skills Configuration Guide

This guide describes how to configure and integrate skills in Claude. You'll learn about project skills, user preferences, and the different integration methods.

---

## Table of Contents

1. [Skills Overview](#skills-overview)
2. [Project Skills vs User Preferences](#project-skills-vs-user-preferences)
3. [Installing Skills in Claude Code](#installing-skills-in-claude-code)
4. [Configuring Skills in Claude.ai](#configuring-skills-in-claudeai)
5. [Skills via the API](#skills-via-the-api)
6. [Creating Custom Skills](#creating-custom-skills)
7. [Best Practices](#best-practices)

---

## Skills Overview

Skills are folders containing instructions, scripts, and resources that Claude loads dynamically to improve performance on specialized tasks. They teach Claude how to complete specific tasks in a repeatable way.

### Skill Structure

```
my-skill/
├── SKILL.md           # Required: Instructions and metadata
├── scripts/           # Optional: Executable code
├── references/        # Optional: Reference documentation
├── assets/            # Optional: Templates, fonts, etc.
└── LICENSE.txt        # Optional: License information
```

### Minimal SKILL.md

```markdown
---
name: my-skill-name
description: A clear description of what this skill does and when to use it
---

# My Skill Name

[Instructions that Claude follows when this skill is active]
```

---

## Project Skills vs User Preferences

### Project Skills

Project skills are configured **specifically for a project**. They are visible to everyone working on the project.

**When to use:**
- Team-specific workflows
- Project-specific style guides
- Shared coding conventions
- Brand guidelines for the project

**Location:** In the project folder, e.g., `.claude/skills/`

**Example project structure:**
```
my-project/
├── .claude/
│   └── skills/
│       ├── project-coding-style/
│       │   └── SKILL.md
│       └── team-workflow/
│           └── SKILL.md
├── src/
└── package.json
```

### User Preferences (Personal Skills)

User preference skills are **personal skills** that apply only to you, regardless of which project you're using.

**When to use:**
- Personal writing style
- Favorite coding conventions
- Personal workflows
- Language preferences

**Location:** In your home directory, e.g., `~/.claude/skills/`

**Example structure:**
```
~/.claude/
└── skills/
    ├── my-writing-style/
    │   └── SKILL.md
    └── communication-preferences/
        └── SKILL.md
```

### Priority

When both types of skills exist:
1. **Project skills** take priority for project-specific tasks
2. **User preferences** are used for general preferences
3. In case of conflicts, the most specific skill is used

---

## Installing Skills in Claude Code

### Method 1: Via Plugin Marketplace

```bash
# Add the Anthropic skills marketplace
/plugin marketplace add anthropics/skills

# Install specific skill sets
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

### Method 2: Direct Installation from Repository

```bash
# Add a skills repository as marketplace
/plugin marketplace add WouterArtsRecruitin/skills

# View available plugins
/plugin list

# Install desired skills
/plugin install <skill-name>
```

### Method 3: Local Skills

1. Create a `.claude/skills/` folder in your project
2. Add skill folders with `SKILL.md` files
3. Claude detects these automatically

**Example:**
```bash
mkdir -p .claude/skills/my-skill
cat > .claude/skills/my-skill/SKILL.md << 'EOF'
---
name: my-skill
description: Description of my skill
---

# Instructions
...
EOF
```

### Using Skills in Claude Code

After installation, you can activate skills by mentioning them:

```
"Use the PDF skill to extract form fields from document.pdf"

"Apply the brand-guidelines skill to this document"

"Create a presentation with the pptx skill"
```

---

## Configuring Skills in Claude.ai

### Step 1: Access Settings

1. Go to Claude.ai
2. Click on your profile icon
3. Select "Settings"
4. Navigate to "Skills" or "Capabilities"

### Step 2: Upload Skills

**For Project Skills:**
1. Open a project in Claude
2. Go to Project Settings
3. Upload your skill folder or SKILL.md file
4. The skill is now available for that project

**For User Preferences:**
1. Go to Account Settings
2. Navigate to "My Skills" or "Preferences"
3. Upload your personal skills
4. These are now available in all projects

### Step 3: Manage Skills

- **Enable/Disable:** Toggle skills on/off per project
- **Set Priority:** Determine which skills take precedence
- **Remove:** Delete skills you no longer need

---

## Skills via the API

### Adding Skills to API Requests

```python
import anthropic

client = anthropic.Anthropic()

# Load skill content
with open("my-skill/SKILL.md", "r") as f:
    skill_content = f.read()

response = client.messages.create(
    model="claude-sonnet-4-20250514",
    max_tokens=1024,
    system=f"""
    You have the following skill available:

    {skill_content}

    Use this skill when relevant.
    """,
    messages=[
        {"role": "user", "content": "Your question here"}
    ]
)
```

### Combining Multiple Skills

```python
skills = []
skill_paths = ["skills/pdf/SKILL.md", "skills/docx/SKILL.md"]

for path in skill_paths:
    with open(path, "r") as f:
        skills.append(f.read())

combined_skills = "\n\n---\n\n".join(skills)

response = client.messages.create(
    model="claude-sonnet-4-20250514",
    max_tokens=1024,
    system=f"Available skills:\n\n{combined_skills}",
    messages=[...]
)
```

---

## Creating Custom Skills

### Step 1: Define the Goal

Answer these questions:
- What problem does this skill solve?
- When should Claude use this skill?
- What specific instructions are needed?

### Step 2: Create the Basic Structure

```bash
mkdir my-new-skill
touch my-new-skill/SKILL.md
```

### Step 3: Write SKILL.md

```markdown
---
name: my-new-skill
description: |
  Use this skill when the user wants to perform [specific task].
  Trigger words: [keyword1], [keyword2], [keyword3]
---

# My New Skill

## Purpose
[Describe what this skill does]

## Instructions
1. [Step 1]
2. [Step 2]
3. [Step 3]

## Examples

### Example 1: [Scenario]
[Input and expected output]

### Example 2: [Scenario]
[Input and expected output]

## Guidelines
- [Guideline 1]
- [Guideline 2]
- [Guideline 3]

## Limitations
- [What this skill does NOT do]
```

### Step 4: Add Optional Resources

**Scripts** (for deterministic tasks):
```bash
mkdir my-new-skill/scripts
# Add Python/Bash scripts
```

**References** (for detailed documentation):
```bash
mkdir my-new-skill/references
# Add .md files with in-depth info
```

**Assets** (for templates and resources):
```bash
mkdir my-new-skill/assets
# Add templates, fonts, etc.
```

### Step 5: Test the Skill

1. Install locally in Claude Code
2. Test with various prompts
3. Refine instructions based on results

---

## Best Practices

### 1. Keep It Concise

Claude is already smart. Focus on:
- Specific procedures
- Exceptions to standard behavior
- Domain-specific knowledge

**Avoid:**
- General instructions Claude already knows
- Redundant explanations
- Too much context

### 2. Clear Triggers

Use descriptive `description` fields:

```yaml
# Good
description: |
  Use this skill for creating PowerPoint presentations.
  Trigger words: presentation, slides, pptx, deck, slideshow

# Less good
description: A skill for documents
```

### 3. Structure for Scalability

```
skill/
├── SKILL.md              # Essential, compact
├── references/           # Details on-demand
│   ├── advanced.md
│   └── troubleshooting.md
└── scripts/              # Reliable execution
    └── helper.py
```

### 4. Version Control

- Use Git for skill development
- Tag releases for stability
- Document changes in CHANGELOG

### 5. Test Thoroughly

- Test with edge cases
- Validate output quality
- Check for conflicts with other skills

---

## FAQ

### How many skills can I use at once?

There's no hard limit, but consider:
- Context window size
- Potential conflicts between skills
- Performance impact

### Can I share skills with my team?

Yes, in several ways:
- Via Git repository (like this one)
- As Project skills in shared projects
- Via the Claude.ai interface

### Do skills work offline?

Skills themselves work offline, but:
- Claude Code requires an internet connection
- Some skill scripts may have external dependencies

### How do I debug a skill that isn't working?

1. Check the `name` and `description` in frontmatter
2. Explicitly ask Claude to use the skill
3. Simplify the instructions
4. Check for syntax errors in YAML frontmatter

---

## Useful Links

- [Agent Skills Specification](https://agentskills.io/specification)
- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [Creating custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide)

---

## Contributing

Want to contribute to this skills repository?

1. Fork the repository
2. Create a new branch
3. Add your skill or improve existing ones
4. Create a Pull Request

For questions or suggestions, open an issue on GitHub.
