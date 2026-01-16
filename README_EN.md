# Teaching AI Skills Marketplace

A free skills marketplace providing various practical AI skill collections that can be used in Claude Code.

> **Note:** This repository merges Anthropic's example skills and Agent Skills collections, providing various practical AI skills that can be used in Claude Code, Claude.ai, and the API. For information about the Agent Skills standard, see [agentskills.io](http://agentskills.io).

## What are Skills?

Skills are folders of instructions, scripts, and resources that Claude loads dynamically to improve performance on specialized tasks. Skills teach Claude how to complete specific tasks in a repeatable way, whether that's creating documents with your company's brand guidelines, analyzing data using your organization's specific workflows, or automating personal tasks.

### More Information

- [What are skills?](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Equipping agents for the real world with Agent Skills](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)
- [Agent Skills specification](https://agentskills.io/)

## About This Repository

This repository contains skills that demonstrate what's possible with Claude's skills system. These skills range from creative applications (art, music, design) to technical tasks (testing web apps, MCP server generation) to enterprise workflows (communications, branding, etc.), as well as teaching and education scenarios.

Each skill is self-contained in its own folder with a `SKILL.md` file containing the instructions and metadata that Claude uses. You can browse through these skills to get inspiration for your own skills or to understand different patterns and approaches.

Many skills in this repo are open source (Apache 2.0). We've also included the document creation & editing skills that power [Claude's document capabilities](https://www.anthropic.com/news/create-files) under the hood in the [`skills/docx`](./skills/docx), [`skills/pdf`](./skills/pdf), [`skills/pptx`](./skills/pptx), and [`skills/xlsx`](./skills/xlsx) subfolders. These are source-available, not open source, but we wanted to share these with developers as a reference for more complex skills that are actively used in a production AI application.

### Disclaimer

**These skills are provided for demonstration and educational purposes only.** While some of these capabilities may be available in Claude, the implementations and behaviors you receive from Claude may differ from what is shown in these skills. These skills are meant to illustrate patterns and possibilities. Always test skills thoroughly in your own environment before relying on them for critical tasks.

## How to Use

### Using in Claude Code

#### 1. Register Marketplace

Run the following command in Claude Code to register this repository as a Claude Code plugin marketplace:

```
/plugin marketplace add teaching-ai/skills
```

> **Note**: Replace `teaching-ai/skills` with your actual GitHub repository path (format: `username/repository-name`)

#### 2. Install Plugins

There are two ways to install plugins:

**Method 1: Install via UI**

1. Select `Browse and install plugins`
2. Select `teaching-ai-skills`
3. Select the plugin you want to install (see available plugins list below)
4. Select `Install now`

**Method 2: Install via Command**

Install plugins directly using commands:

```
/plugin install teaching-skills@teaching-ai-skills
/plugin install document-skills@teaching-ai-skills
/plugin install markdown-skills@teaching-ai-skills
/plugin install development-skills@teaching-ai-skills
/plugin install design-skills@teaching-ai-skills
/plugin install social-skills@teaching-ai-skills
/plugin install utility-skills@teaching-ai-skills
```

#### 3. Use Skills

After installing plugins, you can use skills by simply mentioning them. Claude will automatically determine when to use a skill based on its description.

### Using in Claude.ai

These example skills are all already available to paid plans in Claude.ai.

To use any skill from this repository or upload custom skills, follow the instructions in [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b).

### Using in Claude API

You can use Anthropic's pre-built skills, and upload custom skills, via the Claude API. See the [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill) for more.

### Using on Other Platforms

These skills can also be used on other AI platforms such as Cursor, Trae, Qoder, CodeBuddy, etc. For detailed instructions, please refer to the [Cross-Platform Usage Guide](./PLATFORM_GUIDE.md).

## Available Plugins and Skills

The skills in this repository are organized into 7 plugin categories, containing a total of 23 skills:

### 1. teaching-skills (Teaching Skills Collection)

Teaching and education-related skills collection, including course design, learning assessment, and teaching resource generation.

#### course-designer (Course Design Skill)

Helps design and plan course content, including course outlines, learning objectives, teaching plans, and assessment schemes.

**Usage Examples:**
- "Use the course design skill to help me design a Python programming course"
- "Design an 8-week machine learning introductory course"
- "Create a course outline for web development"

#### learning-assessor (Learning Assessment Skill)

Helps create learning assessment tools, including quiz questions, assessment criteria, scoring rubrics, and learning analytics.

**Usage Examples:**
- "Use the learning assessment skill to create a set of quiz questions for my course"
- "Design a rubric to assess student learning outcomes"
- "Generate a learning analytics report"

#### teaching-resource-generator (Teaching Resource Generator Skill)

Helps generate various teaching resources, including courseware, exercises, teaching cases, and study guides.

**Usage Examples:**
- "Use the teaching resource generator skill to create courseware for my course"
- "Generate some exercises about data structures"
- "Create a teaching case for explaining design patterns"

### 2. document-skills (Document Processing Skills Collection)

Document processing skills collection, supporting creation, editing, and processing of office documents including Excel, Word, PowerPoint, and PDF.

#### docx (Word Document Processing)

Create, edit, and process Microsoft Word documents.

**Usage Examples:**
- "Use the DOCX skill to create a new Word document"
- "Extract text from this Word document"
- "Format this document with headings and styles"

#### pptx (PowerPoint Presentation Processing)

Create, edit, and process Microsoft PowerPoint presentations.

**Usage Examples:**
- "Use the PPTX skill to create a presentation"
- "Add slides to this PowerPoint file"
- "Apply a theme to this presentation"

#### pdf (PDF Document Processing)

Process PDF documents, including text extraction, form filling, merging, and splitting.

**Usage Examples:**
- "Use the PDF skill to extract the form fields from `path/to/some-file.pdf`"
- "Fill out this PDF form"
- "Merge multiple PDF files"

#### xlsx (Excel Spreadsheet Processing)

Create, edit, and process Microsoft Excel spreadsheets.

**Usage Examples:**
- "Use the XLSX skill to create a spreadsheet"
- "Analyze data in this Excel file"
- "Generate charts from this spreadsheet"

#### doc-coauthoring (Document Co-authoring)

Supports multi-user collaborative document editing.

**Usage Examples:**
- "Use the doc-coauthoring skill to prepare this document for collaboration"
- "Add comments and suggestions to this document"

### 3. markdown-skills (Markdown Skills Collection)

Markdown-related skills collection, including Mermaid diagram creation.

#### mermaid (Mermaid Diagram Creation)

Create various types of Mermaid diagrams, including flowcharts, sequence diagrams, class diagrams, state diagrams, Gantt charts, and more.

**Usage Examples:**
- "Use Mermaid to create a flowchart"
- "Draw a C4 diagram for system architecture"
- "Generate a Gantt chart for project timeline"
- "Create a user journey diagram"

**Supported Diagram Types:**
- Flowcharts
- Sequence diagrams
- Class diagrams
- State diagrams
- Entity relationship diagrams (ER diagrams)
- User journey diagrams
- Gantt charts
- Pie charts
- Quadrant charts
- Git graphs
- C4 architecture diagrams
- Mindmaps
- Timelines
- Sankey diagrams
- And many other diagram types

### 4. development-skills (Development Skills Collection)

Development skills collection, including code generation, test writing, documentation building, MCP builder, web development, frontend design, and more.

#### code-generator (Code Generation Skill)

Helps generate high-quality code, supporting multiple programming languages, following best practices and design patterns.

**Usage Examples:**
- "Use the code generation skill to generate a user authentication Python class"
- "Create a RESTful API implementation in Node.js"
- "Generate a Java class following SOLID principles"

#### test-writer (Test Writing Skill)

Helps write unit tests, integration tests, and end-to-end tests.

**Usage Examples:**
- "Write unit tests for this function"
- "Create integration tests to verify API endpoints"
- "Generate end-to-end test cases"

#### documentation-builder (Documentation Builder Skill)

Helps generate technical documentation, including API documentation, user manuals, development guides, and README files.

**Usage Examples:**
- "Use the documentation builder skill to generate API documentation for my project"
- "Create a user manual"
- "Write a development environment setup guide"

#### mcp-builder (MCP Builder)

Helps create and configure Model Context Protocol (MCP) servers.

**Usage Examples:**
- "Use the MCP builder to create a new MCP server"
- "Configure tools and resources for an MCP server"
- "Generate code templates for an MCP server"

#### webapp-testing (Web Application Testing)

Helps test web applications, including functional testing and performance testing.

**Usage Examples:**
- "Test the functionality of this web application"
- "Check the response time of this website"
- "Verify cross-browser compatibility of this application"

#### frontend-design (Frontend Design)

Create high-quality frontend interfaces, avoiding generic AI aesthetics, generating code with unique design sense.

**Usage Examples:**
- "Use the frontend design skill to create a login page"
- "Design a modern dashboard interface"
- "Create a responsive product showcase page"

#### web-artifacts-builder (Web Artifacts Builder)

Create complex multi-component HTML artifacts using modern frontend technologies (React, Tailwind CSS, shadcn/ui).

**Usage Examples:**
- "Use the web artifacts builder to create an interactive data visualization tool"
- "Build a single-page application with state management"
- "Create a complex interface using shadcn/ui components"

#### theme-factory (Theme Factory)

Apply theme styles to artifacts, including 10 preset themes that can be applied to slides, documents, reports, HTML landing pages, and more.

**Usage Examples:**
- "Apply the Ocean Depths theme to this presentation"
- "Style this document with the Modern Minimalist theme"
- "Apply the Golden Hour theme to this webpage"

### 5. design-skills (Design Skills Collection)

Design and creative skills collection, including algorithmic art, brand guidelines, and canvas design.

#### algorithmic-art (Algorithmic Art)

Create algorithmic art using p5.js with seeded randomness and interactive parameter exploration.

**Usage Examples:**
- "Use the algorithmic art skill to create a generative artwork"
- "Generate a visualization based on particle systems"
- "Create a flow field effect artwork"

#### brand-guidelines (Brand Guidelines)

Apply Anthropic's official brand colors and typography to any artifact.

**Usage Examples:**
- "Use the brand guidelines skill to apply brand styles to this document"
- "Apply brand colors to this presentation"
- "Format this document using brand fonts"

#### canvas-design (Canvas Design)

Create high-quality designs and visualizations on HTML Canvas.

**Usage Examples:**
- "Use the canvas design skill to create a data visualization chart"
- "Draw an interactive graphic on Canvas"
- "Create a Canvas animation effect"

### 6. social-skills (Social Skills Collection)

Social and collaboration skills collection, including internal communications and Slack GIF creation.

#### internal-comms (Internal Communications)

Helps write various internal communication documents, including status reports, leadership updates, 3P updates, company newsletters, FAQs, and more.

**Usage Examples:**
- "Use the internal communications skill to write a project status report"
- "Create a company newsletter"
- "Write an FAQ document"

#### slack-gif-creator (Slack GIF Creator)

Create GIF animations for use in Slack.

**Usage Examples:**
- "Use the Slack GIF creator to create a welcome animation"
- "Generate a GIF for Slack messages"
- "Create a notification animation GIF"

### 7. utility-skills (Utility Skills Collection)

Utility and practical skills collection, including skill creator.

#### skill-creator (Skill Creator)

Guides how to create effective skills to extend Claude's capabilities.

**Usage Examples:**
- "Use the skill creator to help me create a new skill"
- "How to design the structure of a skill"
- "What are the best practices for creating a skill"

## Project Structure

```
.
├── .claude-plugin/
│   └── marketplace.json          # Marketplace configuration file
├── skills/                        # Skills directory
│   ├── teaching-skills/          # Teaching skills
│   │   ├── course-designer/
│   │   ├── learning-assessor/
│   │   └── teaching-resource-generator/
│   ├── document-skills/          # Document processing skills
│   │   ├── docx/
│   │   ├── pptx/
│   │   ├── pdf/
│   │   ├── xlsx/
│   │   └── doc-coauthoring/
│   ├── markdown-skills/          # Markdown skills
│   │   └── mermaid/
│   ├── development-skills/       # Development skills
│   │   ├── code-generator/
│   │   ├── test-writer/
│   │   ├── documentation-builder/
│   │   ├── mcp-builder/
│   │   ├── webapp-testing/
│   │   ├── frontend-design/
│   │   ├── web-artifacts-builder/
│   │   └── theme-factory/
│   ├── design-skills/            # Design skills
│   │   ├── algorithmic-art/
│   │   ├── brand-guidelines/
│   │   └── canvas-design/
│   ├── social-skills/            # Social skills
│   │   ├── internal-comms/
│   │   └── slack-gif-creator/
│   └── utility-skills/           # Utility skills
│       └── skill-creator/
├── spec/                          # Agent Skills specification
├── template/                      # Skill template
└── README.md                      # This file
```

## How to Create a New Skill

### Creating a Basic Skill

Skills are simple to create - just a folder with a `SKILL.md` file containing YAML frontmatter and instructions. You can use the **template-skill** in this repository as a starting point:

```markdown
---
name: my-skill-name
description: A clear description of what this skill does and when to use it
---

# My Skill Name

[Add your instructions here that Claude will follow when this skill is active]

## Examples
- Example usage 1
- Example usage 2

## Guidelines
- Guideline 1
- Guideline 2
```

The frontmatter requires only two fields:
- `name` - A unique identifier for your skill (lowercase, hyphens for spaces)
- `description` - A complete description of what the skill does and when to use it

The markdown content below contains the instructions, examples, and guidelines that Claude will follow. For more details, see [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills).

### Skill Structure

Each skill contains:
- `SKILL.md` - Instructions for the agent (required)
- `scripts/` - Helper scripts for automation (optional)
- `references/` - Supporting documentation (optional)
- `assets/` - Resource files (optional)

### Steps to Add a New Skill

#### 1. Create Skill Directory

Create a new skill directory under the `skills/` directory:

```bash
mkdir -p skills/your-skill-name
```

#### 2. Create SKILL.md File

Each skill must contain a `SKILL.md` file with the format shown above.

#### 3. Update marketplace.json

Add the new skill to the appropriate plugin in `.claude-plugin/marketplace.json`:

```json
{
  "plugins": [
    {
      "name": "your-plugin-name",
      "description": "Plugin description",
      "source": "./",
      "strict": false,
      "skills": [
        "./skills/your-skill-name"
      ]
    }
  ]
}
```

#### 4. Commit to GitHub

Commit and push changes to the GitHub repository:

```bash
git add .
git commit -m "Add new skill: your-skill-name"
git push
```

## Marketplace Configuration File

The `.claude-plugin/marketplace.json` file defines the marketplace metadata and available plugins:

```json
{
  "name": "marketplace-name",        // Marketplace name
  "owner": {                         // Owner information
    "name": "Owner Name",
    "email": "owner@example.com"
  },
  "metadata": {                      // Metadata
    "description": "Marketplace description",
    "version": "1.0.0"
  },
  "plugins": [                       // Plugin list
    {
      "name": "plugin-name",         // Plugin name
      "description": "Plugin description",
      "source": "./",                // Source code path
      "strict": false,               // Strict mode
      "skills": [                    // Skills list
        "./skills/skill1",
        "./skills/skill2"
      ]
    }
  ]
}
```

## How It Works

1. **Marketplace Registration**: When you run `/plugin marketplace add teaching-ai/skills`, Claude Code will:
   - Fetch the `.claude-plugin/marketplace.json` file from the GitHub repository
   - Parse the marketplace configuration
   - Add the marketplace to the available list

2. **Plugin Installation**: When you install a plugin, Claude Code will:
   - Download all skills defined in the plugin
   - Store skills locally
   - Make skills available to Claude

3. **Skill Usage**: When you use a skill, Claude will:
   - Determine whether to use the skill based on its description
   - Load the skill's `SKILL.md` file
   - Execute tasks according to the skill instructions

## Best Practices

### Skill Design

- **Clear Description**: The `description` field should clearly state when to use the skill
- **Concise Content**: Keep `SKILL.md` concise, avoid unnecessary verbosity (recommended under 500 lines)
- **Structured Organization**: Use clear sections and structure
- **Practical Examples**: Provide practical, usable examples
- **Progressive Disclosure**: Put detailed reference materials in separate files and load them as needed

### Marketplace Organization

- **Logical Grouping**: Organize related skills into the same plugin
- **Clear Naming**: Use clear, descriptive names
- **Version Management**: Maintain version numbers in `metadata`

## License

Many skills in this repository are licensed under Apache 2.0. Document processing skills (docx, pdf, pptx, xlsx) are source-available but not open source. See LICENSE files in each skill directory for details.

## Contributing

Contributions of new skills are welcome! Please follow these steps:

1. Fork this repository
2. Create new skills or improve existing skills
3. Submit a Pull Request

## Partner Skills

Skills are a great way to teach Claude how to get better at using specific pieces of software. As we see awesome example skills from partners, we may highlight some of them here:

- **Notion** - [Notion Skills for Claude](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)

## Reference Resources

- [Agent Skills specification](https://agentskills.io/)
- [Claude Skills documentation](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [How to create custom skills](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [Equipping agents for the real world with Agent Skills](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)
- [Anthropic Skills examples](https://github.com/anthropics/skills)
- [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill)

## Contact

For questions or suggestions, please contact us via GitHub Issues.
