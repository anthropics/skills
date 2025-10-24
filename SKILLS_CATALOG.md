# Skills Catalog

A comprehensive catalog of all available skills organized by category, with detailed descriptions, use cases, and complexity levels.

## Quick Reference

| Category | Skills Count | Best For |
|----------|--------------|----------|
| [Creative & Design](#creative--design) | 4 | Visual content, art, animations, theming |
| [Development & Technical](#development--technical) | 6 | Code quality, testing, API integration, documentation |
| [Enterprise & Communication](#enterprise--communication) | 2 | Business communications, branding |
| [Document Processing](#document-processing) | 4 | Creating/editing Office documents, PDFs |
| [Meta Skills](#meta-skills) | 2 | Learning to create skills, templates |

**Total Skills:** 18 (13 example + 3 new + 4 document skills)

---

## Creative & Design

### algorithmic-art
**Purpose:** Generate beautiful, code-based art using p5.js with mathematical patterns and animations

**Key Features:**
- Seeded randomness for reproducible results
- Flow fields and particle systems
- Noise-based animations
- Geometric patterns

**Use Cases:**
- Creating unique visual art
- Generating branded visuals
- Learning generative art techniques
- Creating animated backgrounds

**Complexity:** Medium
**Bundled Resources:** Templates for common patterns
**License:** Apache-2.0

**When to trigger:** User wants to create generative art, algorithmic visuals, or p5.js sketches

---

### canvas-design
**Purpose:** Create professional visual art in PNG and PDF formats using design philosophy principles

**Key Features:**
- Two-step design process (rough draft → refinement)
- Support for various design styles
- PNG and PDF output
- Design philosophy guidance

**Use Cases:**
- Creating posters and graphics
- Design mockups
- Visual presentations
- Marketing materials

**Complexity:** Medium
**Bundled Resources:** Design guidelines
**License:** Apache-2.0

**When to trigger:** User wants to create visual designs, posters, or graphics

---

### slack-gif-creator
**Purpose:** Create animated GIFs specifically optimized for Slack's dimension and file size requirements

**Key Features:**
- Automatic size optimization for Slack
- Multiple animation templates (wiggle, morph, fade, etc.)
- Color palette management
- Typography and visual effects
- Easing functions for smooth animations

**Use Cases:**
- Slack emoji and reactions
- Team celebration animations
- Visual communication in chat
- Fun workplace content

**Complexity:** High
**Bundled Resources:**
- Core animation engine (`core/`)
- Animation templates (`templates/`)
- Python dependencies (`requirements.txt`)

**License:** Apache-2.0

**When to trigger:** User wants to create animated GIFs for Slack

---

### theme-factory
**Purpose:** Apply professional visual themes to artifacts with 10 preset styles or custom theme generation

**Key Features:**
- 10 pre-defined professional themes
- Custom theme generation
- Consistent color palettes
- Typography systems
- Theme showcase reference

**Use Cases:**
- Branding consistency
- Rapid prototyping with different looks
- Creating themed documents
- Design system exploration

**Complexity:** Low
**Bundled Resources:**
- Theme definitions (`themes/`)
- Theme showcase PDF

**License:** Apache-2.0

**When to trigger:** User wants to style artifacts with themes or apply consistent design

---

## Development & Technical

### artifacts-builder
**Purpose:** Build complex, interactive HTML artifacts using React, Tailwind CSS, and shadcn/ui components

**Key Features:**
- React component integration
- Tailwind CSS styling
- shadcn/ui component library
- Interactive UI elements
- Responsive design

**Use Cases:**
- Creating interactive demos
- Building UI prototypes
- Generating web components
- Educational examples

**Complexity:** High
**Bundled Resources:** Scripts and component templates
**License:** Apache-2.0

**When to trigger:** User wants to build React artifacts with Tailwind and shadcn/ui

---

### mcp-builder
**Purpose:** Comprehensive guide for creating high-quality Model Context Protocol (MCP) servers

**Key Features:**
- MCP server structure guidance
- Best practices for tool design
- Validation and testing patterns
- Resource management
- Error handling strategies

**Use Cases:**
- Creating new MCP servers
- Integrating external APIs
- Building Claude extensions
- Service integration

**Complexity:** High
**Bundled Resources:**
- Creation scripts (`scripts/`)
- Reference documentation (`reference/`)
- Example implementations

**License:** Apache-2.0

**When to trigger:** User wants to create or improve MCP servers

---

### webapp-testing
**Purpose:** Test local web applications using Playwright for automated UI testing and verification

**Key Features:**
- Playwright integration
- UI element verification
- Screenshot capture
- Console log monitoring
- Static and dynamic site testing

**Use Cases:**
- Automated UI testing
- Visual regression testing
- Debug web applications
- Verify UI functionality

**Complexity:** Medium
**Bundled Resources:**
- Helper scripts (`scripts/`)
- Example test files (`examples/`)

**License:** Apache-2.0

**When to trigger:** User wants to test web applications with Playwright

---

### code-reviewer ⭐ NEW
**Purpose:** Perform systematic code reviews checking for bugs, security, performance, and code quality

**Key Features:**
- Systematic review process
- Security vulnerability detection
- Performance analysis
- Code quality assessment
- Prioritized findings (Critical/High/Medium/Low)
- Constructive feedback with examples

**Use Cases:**
- Pre-commit code reviews
- Learning from code analysis
- Security audits
- Performance optimization identification
- Maintaining code quality standards

**Complexity:** Medium
**Bundled Resources:** None (instruction-based)
**License:** Apache-2.0

**When to trigger:** User requests code review, wants to check code quality, or asks to analyze/review code

---

### api-documentation-writer ⭐ NEW
**Purpose:** Generate comprehensive, developer-friendly API documentation with examples and clear explanations

**Key Features:**
- REST, GraphQL, and gRPC support
- Complete endpoint documentation
- Code examples in multiple languages
- Authentication documentation
- Error handling guides
- OpenAPI/Swagger spec generation

**Use Cases:**
- Creating API reference documentation
- Generating OpenAPI specifications
- Documenting new APIs
- Updating existing API docs
- Creating developer portals

**Complexity:** Medium
**Bundled Resources:** None (instruction-based)
**License:** Apache-2.0

**When to trigger:** User wants to document APIs, create API docs, or generate OpenAPI specs

---

### test-generator ⭐ NEW
**Purpose:** Generate comprehensive test suites including unit tests, integration tests, and edge cases

**Key Features:**
- Multi-framework support (Jest, pytest, JUnit, etc.)
- Unit and integration test generation
- Edge case coverage
- Mocking and fixture setup
- Component and API testing
- Test quality guidelines

**Use Cases:**
- Adding tests to untested code
- TDD scaffolding
- Improving test coverage
- Learning testing patterns
- Generating test boilerplate

**Complexity:** Medium
**Bundled Resources:** None (instruction-based)
**License:** Apache-2.0

**When to trigger:** User wants to generate tests, add test coverage, or create test suites

---

## Enterprise & Communication

### brand-guidelines
**Purpose:** Apply Anthropic's official brand colors, typography, and visual guidelines to artifacts

**Key Features:**
- Official Anthropic brand colors
- Typography specifications
- Logo usage guidelines
- Visual identity standards

**Use Cases:**
- Creating branded content
- Consistent corporate materials
- Following brand standards
- Company presentations

**Complexity:** Low
**Bundled Resources:** None (guidelines in SKILL.md)
**License:** Apache-2.0

**When to trigger:** User wants to apply Anthropic branding or follow brand guidelines

---

### internal-comms
**Purpose:** Write effective internal communications like status reports, newsletters, FAQs, and announcements

**Key Features:**
- Multiple communication formats
- Professional writing patterns
- Structure templates
- Tone and style guidance

**Use Cases:**
- Status reports
- Team newsletters
- FAQ documentation
- Internal announcements
- Policy updates

**Complexity:** Low
**Bundled Resources:** Example communications (`examples/`)
**License:** Apache-2.0

**When to trigger:** User wants to write internal communications or company updates

---

## Document Processing

The document skills are source-available (not open source) snapshots of production skills used in Claude. They demonstrate advanced patterns for working with complex file formats.

**Important:** These are point-in-time snapshots for reference. Actively maintained versions ship with Claude.

### docx
**Purpose:** Create, edit, and analyze Word documents with full formatting support

**Key Features:**
- Create new Word documents
- Edit existing documents
- Preserve formatting and styles
- Track changes and comments
- Text extraction and analysis
- Table and image support

**Use Cases:**
- Generating reports
- Creating formatted documents
- Editing Word files
- Extracting document content
- Document automation

**Complexity:** Very High
**Bundled Resources:** Complex scripts, schemas, validation tools
**License:** Source-available (proprietary)

---

### pdf
**Purpose:** Comprehensive PDF manipulation toolkit for creating, editing, and analyzing PDFs

**Key Features:**
- Extract text and tables
- Create new PDFs
- Merge and split documents
- Form field handling
- Annotation support
- Image extraction

**Use Cases:**
- PDF generation
- Document merging
- Data extraction from PDFs
- Form processing
- Report generation

**Complexity:** Very High
**Bundled Resources:** Complex scripts, reference docs
**License:** Source-available (proprietary)

---

### pptx
**Purpose:** Create, edit, and analyze PowerPoint presentations with layouts and charts

**Key Features:**
- Create presentations from scratch
- Edit existing slides
- Template support
- Chart generation
- Layout management
- Automated slide generation

**Use Cases:**
- Presentation generation
- Report decks
- Data visualization in slides
- Template-based presentations
- Bulk slide updates

**Complexity:** Very High
**Bundled Resources:** Complex scripts, schemas, templates
**License:** Source-available (proprietary)

---

### xlsx
**Purpose:** Create, edit, and analyze Excel spreadsheets with formulas and formatting

**Key Features:**
- Create spreadsheets
- Edit cells and ranges
- Formula support
- Data formatting
- Chart generation
- Data analysis

**Use Cases:**
- Report generation
- Data analysis
- Financial models
- Automated data entry
- Spreadsheet templating

**Complexity:** Very High
**Bundled Resources:** Complex scripts, schemas, validation
**License:** Source-available (proprietary)

---

## Meta Skills

### skill-creator
**Purpose:** Comprehensive guide for creating effective Claude skills with best practices

**Key Features:**
- Skill creation methodology
- Structure and organization guidance
- Progressive disclosure patterns
- Bundled resource best practices
- Validation and testing approaches

**Use Cases:**
- Learning to create skills
- Understanding skill patterns
- Planning new skills
- Improving existing skills
- Skill architecture decisions

**Complexity:** Low (to use), High (to master)
**Bundled Resources:**
- Initialization script (`scripts/init_skill.py`)
- Packaging script (`scripts/package_skill.py`)
- Quick validation (`scripts/quick_validate.py`)

**License:** Apache-2.0

**When to trigger:** User wants to create a new skill or learn about skill development

---

### template-skill
**Purpose:** Minimal template for starting new skills with proper structure

**Key Features:**
- Basic SKILL.md structure
- Required frontmatter
- Example instruction format
- Clean starting point

**Use Cases:**
- Quick skill scaffolding
- Learning skill structure
- Starting point for development

**Complexity:** Very Low
**Bundled Resources:** None
**License:** Apache-2.0

**When to trigger:** User wants a basic skill template to start from

---

## Skill Selection Guide

### By Complexity

**Beginner (Low Complexity):**
- brand-guidelines
- internal-comms
- theme-factory
- template-skill

**Intermediate (Medium Complexity):**
- algorithmic-art
- canvas-design
- webapp-testing
- code-reviewer ⭐
- api-documentation-writer ⭐
- test-generator ⭐

**Advanced (High Complexity):**
- artifacts-builder
- mcp-builder
- slack-gif-creator

**Expert (Very High Complexity):**
- All document skills (docx, pdf, pptx, xlsx)

### By Use Case

**Code Quality & Development:**
- code-reviewer ⭐
- test-generator ⭐
- webapp-testing
- mcp-builder

**Documentation:**
- api-documentation-writer ⭐
- internal-comms

**Creative Work:**
- algorithmic-art
- canvas-design
- slack-gif-creator
- theme-factory

**Business & Enterprise:**
- brand-guidelines
- internal-comms
- All document skills

**Learning & Development:**
- skill-creator
- template-skill

### By Resource Requirements

**No External Dependencies:**
- Most instruction-based skills
- brand-guidelines
- code-reviewer ⭐
- api-documentation-writer ⭐
- test-generator ⭐
- internal-comms

**Python Dependencies:**
- slack-gif-creator
- Most document skills

**Node.js Dependencies:**
- artifacts-builder
- webapp-testing (Playwright)

**Multiple Dependencies:**
- Document skills (complex toolchains)

---

## Getting Started

### For First-Time Users

Start with these approachable skills:
1. **brand-guidelines** - Simple, clear example of instruction-based skills
2. **theme-factory** - Shows how bundled resources work
3. **code-reviewer** ⭐ - Practical, immediately useful
4. **internal-comms** - Good example of structured output

### For Developers

Try these technical skills:
1. **test-generator** ⭐ - Improve code quality
2. **code-reviewer** ⭐ - Learn review best practices
3. **api-documentation-writer** ⭐ - Generate docs
4. **webapp-testing** - Automated testing
5. **mcp-builder** - Extend Claude's capabilities

### For Skill Creators

Study these for patterns:
1. **skill-creator** - Meta-guidance on skill creation
2. **template-skill** - Minimal starting point
3. **code-reviewer** ⭐ - Well-structured instruction-based skill
4. **slack-gif-creator** - Complex bundled resources example
5. **mcp-builder** - Reference documentation patterns

---

## Installation

### Claude Code
```bash
# Add marketplace
/plugin marketplace add anthropics/skills

# Install example skills (including new ones)
/plugin install example-skills@anthropic-agent-skills

# Install document skills
/plugin install document-skills@anthropic-agent-skills
```

### Claude.ai
These skills are available to paid plans. Upload custom skills via the skills menu.

### Claude API
Use the Skills API to upload and use custom skills. See [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill).

---

## Additional Resources

- **[CONTRIBUTING.md](CONTRIBUTING.md)** - How to contribute new skills
- **[SKILL_DEVELOPMENT_GUIDE.md](SKILL_DEVELOPMENT_GUIDE.md)** - Comprehensive development guide
- **[agent_skills_spec.md](agent_skills_spec.md)** - Official specification
- **[README.md](README.md)** - Repository overview

### Validation Tools

- **scripts/validate_skill.py** - Comprehensive skill validation
- **skill-creator/scripts/quick_validate.py** - Quick validation

---

## Legend

- ⭐ **NEW** - Recently added skills
- **Complexity** - Relative difficulty: Low → Medium → High → Very High
- **Bundled Resources** - Additional files beyond SKILL.md
- **License** - Apache-2.0 (open source) or Source-available (reference only)

---

**Last Updated:** October 2025
**Total Skills:** 18 (16 open source, 4 source-available, 3 new additions)
