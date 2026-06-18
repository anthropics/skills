---
name: plugin
description: "Help users manage Claude Code plugins and skills via the /plugin command. TRIGGER when: user asks about installing skills, /plugin commands, adding a marketplace, browsing or uninstalling plugins, or creating a marketplace-compatible repository. DO NOT TRIGGER when: user is asking about browser extensions, VS Code extensions, or non-Claude plugins."
---

# Claude Code Plugin & Marketplace System

This skill helps you install, manage, and create Claude Code plugins — bundles of skills that can be shared via GitHub repositories and a marketplace system.

## What Are Plugins?

In Claude Code, a **plugin** is a named bundle of one or more skills packaged for easy installation from a GitHub repository. A **marketplace** is a GitHub repository that defines which plugins it offers via a `.claude-plugin/marketplace.json` file.

## Core Commands

### Add a Marketplace Source

Register a GitHub repository as a marketplace:

```
/plugin marketplace add <owner>/<repo>
```

Example — add Anthropic's official skills marketplace:
```
/plugin marketplace add anthropics/skills
```

### Browse & Install Interactively

After adding a marketplace, browse and install through an interactive menu:

1. `/plugin marketplace add anthropics/skills`
2. Select `Browse and install plugins`
3. Select a marketplace (e.g., `anthropic-agent-skills`)
4. Select a plugin bundle (e.g., `document-skills` or `example-skills`)
5. Select `Install now`

### Install Directly

Install a specific plugin bundle without browsing:

```
/plugin install <plugin-name>@<marketplace-name>
```

Examples:
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
/plugin install claude-api@anthropic-agent-skills
```

### Uninstall a Plugin

```
/plugin uninstall <plugin-name>
```

### List Installed Plugins

```
/plugin list
```

## Using Installed Skills

Once a plugin is installed, its skills are available automatically. Just describe what you want:

- "Use the PDF skill to extract form fields from report.pdf"
- "Create an Excel spreadsheet with the sales data"
- "Build an MCP server for my API"

Claude will detect the relevant skill from your description.

## Creating a Marketplace Repository

To share your own skills as an installable plugin, add a `.claude-plugin/marketplace.json` to your GitHub repository.

### marketplace.json Structure

```json
{
  "name": "my-marketplace-name",
  "owner": {
    "name": "Your Name",
    "email": "you@example.com"
  },
  "metadata": {
    "description": "A short description of this marketplace",
    "version": "1.0.0"
  },
  "plugins": [
    {
      "name": "my-plugin",
      "description": "What this plugin bundle does",
      "source": "./",
      "strict": false,
      "skills": [
        "./skills/my-skill-one",
        "./skills/my-skill-two"
      ]
    }
  ]
}
```

### Key Fields

| Field | Description |
|---|---|
| `name` | Unique marketplace identifier (used in `@marketplace-name`) |
| `plugins[].name` | Plugin bundle name (used in `/plugin install <name>@...`) |
| `plugins[].skills` | Array of paths to skill folders (each must contain a `SKILL.md`) |
| `plugins[].strict` | If `true`, only skills in this bundle are active when installed |

### Skill Folder Structure

Each skill path must point to a folder with at minimum:

```
skills/
  my-skill/
    SKILL.md       ← Required: YAML frontmatter + instructions
    LICENSE.txt    ← Optional but recommended
    scripts/       ← Optional supporting scripts
    templates/     ← Optional templates
```

`SKILL.md` frontmatter:
```yaml
---
name: my-skill-name
description: What the skill does and when to trigger it
---
```

## Example: Anthropic's Skills Repository

The `anthropics/skills` repository is the official reference implementation. It offers three plugin bundles:

| Bundle | Contents |
|---|---|
| `document-skills` | xlsx, docx, pptx, pdf |
| `example-skills` | algorithmic-art, brand-guidelines, canvas-design, skill-creator, mcp-builder, and more |
| `claude-api` | Claude API & SDK documentation for Python, TypeScript, Java, Go, Ruby, PHP |

Install all at once:
```
/plugin marketplace add anthropics/skills
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
/plugin install claude-api@anthropic-agent-skills
```

## Troubleshooting

- **"Unknown marketplace"** — Run `/plugin marketplace add <owner>/<repo>` first
- **Skill not triggering** — Describe the task more explicitly (e.g., "use the PDF skill to...")
- **Permission issues** — Make sure the GitHub repository is public or you have access
- **After install, skill still unavailable** — Restart Claude Code to reload skills

## Further Reading

- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Agent Skills specification](https://agentskills.io/specification)
