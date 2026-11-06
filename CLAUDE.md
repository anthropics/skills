# Claude.md - Repository Guide for AI Assistants

## Overview

This is **Anthropic's Skills Repository**, containing demonstration and reference implementations of Claude skills, a dynamic system that teaches Claude how to complete specialized tasks in repeatable ways.

**Key Facts:**
- Repository: `karansandhu00613-ai/senior-manager`
- Purpose: Educational and reference implementations of Claude skills
- Disclaimer: Implementations and behaviors may differ from production Claude. Always test thoroughly.
- License: Mix of Apache 2.0, Proprietary (document skills), and individual skill licenses

---

## Repository Structure

```
.
├── skills/                      # Skill implementations (21 directories)
│   ├── Document Skills (Production-ready)
│   │   ├── docx/               # Word document creation, editing, analysis
│   │   ├── pdf/                # PDF manipulation and extraction
│   │   ├── pptx/               # PowerPoint presentation generation
│   │   └── xlsx/               # Excel spreadsheet operations
│   │
│   ├── Creative & Design
│   │   ├── algorithmic-art/     # Generative art using p5.js
│   │   ├── canvas-design/       # Visual design and poster creation
│   │   ├── brand-guidelines/    # Anthropic brand styling
│   │   ├── frontend-design/     # Responsive UI/app design
│   │   ├── slack-gif-creator/   # Animated GIF creation for Slack
│   │   ├── theme-factory/       # Theme and color system generation
│   │   └── web-artifacts-builder/  # Interactive web component creation
│   │
│   ├── Development & Technical
│   │   ├── mcp-builder/         # MCP (Model Context Protocol) server development
│   │   ├── skill-creator/       # Create, test, and optimize skills
│   │   └── webapp-testing/      # Web app testing and automation
│   │
│   ├── Enterprise & Communication
│   │   ├── internal-comms/      # Internal company communications
│   │   ├── doc-coauthoring/     # Structured documentation workflows
│   │   ├── chief-of-staff/      # Executive support and decision-making
│   │   ├── business-opportunity-finder/  # Identify business opportunities
│   │   ├── venture-builder/     # Multi-agent venture execution
│   │   └── sell-your-skill/     # Marketplace skill promotion
│   │
│   └── API & Reference
│       └── claude-api/          # Claude API/SDK documentation reference
│
├── spec/                        # Agent Skills specification (points to agentskills.io)
├── template/                    # Skill template for creating new skills
├── .claude-plugin/
│   └── marketplace.json         # Plugin marketplace configuration
├── .github/workflows/           # CI/CD workflows
│   ├── codeql.yml              # Code quality analysis
│   └── generator-generic-ossf-slsa3-publish.yml  # SLSA provenance
├── README.md                    # Public repository documentation
├── CLAUDE.md                    # This file
├── ANTHROPIC_AUTH_CONFIG.md     # Anthropic authentication setup
├── OPENAI_AUTH_CONFIG.md        # OpenAI authentication setup
├── TESTING_EXAMPLES.md          # Comprehensive testing examples
├── TEST_COVERAGE_ANALYSIS.md    # Test coverage documentation
└── THIRD_PARTY_NOTICES.md       # Third-party licensing and attribution
```

---

## Skill Anatomy

Every skill follows a consistent structure:

### Minimal Skill
```
skill-name/
└── SKILL.md
```

### Complete Skill
```
skill-name/
├── SKILL.md                    # Required: YAML frontmatter + markdown instructions
├── references/                 # Optional: Reference documentation
│   ├── example.md
│   └── best_practices.md
├── scripts/                    # Optional: Executable code for deterministic tasks
│   ├── transform.js
│   └── validate.py
└── assets/                     # Optional: Templates, icons, fonts
    ├── template.docx
    └── style.css
```

### SKILL.md Frontmatter

Required fields:
```yaml
---
name: skill-identifier           # Unique identifier (lowercase, hyphens for spaces)
description: |                   # Complete description of what skill does
  What this skill does.
  When to use it (include triggers to ensure usage).
  Make descriptions slightly "pushy" to combat underutilization.
---
```

Optional fields:
```yaml
license: "Apache 2.0"            # or "Proprietary" or custom terms
compatibility: "Requires Node.js 18+" # If applicable
```

### Skill Size Guidelines

- **SKILL.md body**: Keep under 500 lines; use clear hierarchy
- **Reference files**: Unlimited; organize with TOC for >300 lines
- **Loading strategy**: Metadata always loaded (~100 words), body on trigger, references as needed

---

## Skill Categories & Purpose

### Document Skills (Proprietary - production-ready)
- **docx**, **pdf**, **pptx**, **xlsx**: Power Claude's native document capabilities
- More complex reference implementations with gotchas documented
- Include helper scripts (merge_runs.py, accept_changes.py, etc.)
- Production dependencies: pandoc, LibreOffice, Poppler

### Example Skills (Apache 2.0 - educational reference)
- Demonstrate patterns and possibilities across domains
- Not guaranteed to match production behavior
- Reference implementations for developers
- Actively used in Claude API and Claude.ai

### Specialized Business Skills (Recent additions)
- **chief-of-staff**: Executive decision-making with hard approval gating
- **business-opportunity-finder**: Business opportunity identification
- **venture-builder**: Multi-agent venture execution framework
- **sell-your-skill**: Marketplace promotion playbooks

---

## Plugin Marketplace

Configured in `.claude-plugin/marketplace.json`:

### Plugin Collections
1. **document-skills**: docx, pdf, pptx, xlsx
   - Professional document processing suite
2. **example-skills**: 16 creative, development, enterprise, and communication skills
   - Algorithmic art, brand guidelines, business opportunity finder, canvas design, chief-of-staff, doc-coauthoring, frontend design, internal communications, MCP building, sell-your-skill, skill creator, Slack GIF creator, theme factory, venture builder, web artifacts builder, web app testing
3. **claude-api**: Claude API/SDK reference documentation

### Installation (Claude Code)
```bash
# Add marketplace
/plugin marketplace add anthropics/skills

# Install specific plugin
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

---

## Development Workflow

### Branch Structure
- **main**: Production/release branch
- **claude/*** branches: Feature development (created by AI assistants)

### Making Changes

1. **Create feature branch** (already created):
   ```bash
   git checkout -b claude/feature-name
   # or already on: claude/claude-md-docs-8de5cj
   ```

2. **Edit skills**:
   - Modify SKILL.md for instructions/content changes
   - Add/update reference files in `references/`
   - Add/update scripts in `scripts/`
   - Update marketplace.json if adding new skills

3. **Commit changes**:
   ```bash
   git add <specific files>
   git commit -m "Clear, descriptive commit message"
   ```

4. **Push to feature branch**:
   ```bash
   git push -u origin claude/feature-name
   ```

5. **Create Pull Request**:
   - Describe changes clearly
   - Reference skill names and what was modified
   - No template (create from scratch or use standard format)

### Pull Request Best Practices
- One feature per PR (e.g., one new skill, one documentation update)
- Test skills thoroughly before submission
- Include test cases/examples if adding complex functionality
- Request reviews from domain experts for new domains

---

## Skill Creation Process

### Steps for Creating New Skills

1. **Capture Intent**
   - What should Claude be able to do?
   - When should it trigger? (user phrases/contexts)
   - What's the expected output format?

2. **Interview & Research**
   - Ask about edge cases, input/output formats
   - Check dependencies and prerequisites
   - Look for similar skills or reference patterns

3. **Write SKILL.md**
   - Create skill directory: `skills/skill-name/`
   - Write SKILL.md with clear metadata and instructions
   - Make descriptions "pushy" - include trigger contexts explicitly
   - Keep under 500 lines; use hierarchy and references

4. **Create Test Cases** (if objective output)
   - Write 2-3 realistic test prompts
   - Save to `evals/evals.json`
   - Run evaluations with test prompts
   - Draft assertions while tests run

5. **Iterate Based on Feedback**
   - Run evals, collect results
   - Refine based on user feedback
   - Repeat until satisfied
   - Optimize description for better triggering

6. **Add Reference Files** (if needed)
   - Place detailed docs in `references/`
   - Add scripts in `scripts/` for deterministic tasks
   - Include assets in `assets/` if needed

---

## Skill Writing Guidelines

### Structure
- **Progressive disclosure**: Metadata → SKILL.md body → bundled resources
- **Organization**: Use clear hierarchy; relate file structure to skill domains
- **Clarity**: Explain "why" rather than imperative "must"
- **Examples**: Include realistic input/output examples

### Writing Style
- Use imperative form in instructions
- Explain the theory behind guidelines
- Keep examples concrete and realistic
- Avoid narrow examples; write general patterns

### Trigger Optimization
- Include context words in description
- "Pushy" descriptions combat underutilization
- Example: "Use this skill whenever user mentions dashboards, data viz, metrics, or company data"

### Naming Conventions
- Skill names: lowercase with hyphens (`skill-name`)
- Directory names: match skill name exactly
- File names: CamelCase for scripts/references

---

## Key Files & Their Purposes

### Configuration
- **.claude-plugin/marketplace.json**: Plugin collections and skill paths
- **README.md**: Public-facing repository documentation

### Documentation
- **ANTHROPIC_AUTH_CONFIG.md**: Anthropic API authentication setup
- **OPENAI_AUTH_CONFIG.md**: OpenAI API authentication setup
- **TESTING_EXAMPLES.md**: Comprehensive testing and evaluation patterns
- **TEST_COVERAGE_ANALYSIS.md**: Test coverage reporting and metrics
- **THIRD_PARTY_NOTICES.md**: Attribution and licensing for third-party dependencies

### CI/CD
- **.github/workflows/codeql.yml**: Code quality and security analysis
- **.github/workflows/generator-generic-ossf-slsa3-publish.yml**: SLSA provenance generation

---

## Special Patterns & Techniques

### Document Skills (docx/pdf/pptx/xlsx)

#### DOCX Gotchas
- Page size defaults to A4; use `{ width: 12240, height: 15840 }` DXA for US Letter
- Tables need `columnWidths` AND cell `width` in DXA units
- Use `ShadingType.CLEAR` for table shading, never `SOLID`
- Use `numbering` config for lists, never literal `•`
- `ImageRun` requires `type:` field (e.g., `"png"`)
- TOC: headings must use built-in `HeadingLevel.*` or set `outlineLevel`
- No `\n` in text; use separate `Paragraph` elements

#### DOCX Workflow
- **Create**: Write `docx` (npm) script
- **Edit**: unzip → edit XML → zip
- **Read**: `pandoc -t markdown file.docx`
- **Validate**: `python scripts/office/validate.py`

### MCP Builder Pattern
The `mcp-builder` skill outlines a 4-phase development process:

1. **Research & Planning**: Study MCP protocol, framework docs, API
2. **Implementation**: Project setup, infrastructure, tool implementation
3. **Review & Test**: Code quality, testing with MCP Inspector
4. **Evaluation**: Create 10 complex test questions with verifiable answers

---

## Code Quality Standards

### Testing
- Test skills thoroughly before PR submission
- Include test cases for objective outputs (code generation, transforms)
- Subjective outputs (writing, design) may use qualitative feedback
- Use evaluations for complex skills; benchmark performance

### Documentation
- Clear trigger descriptions in skill metadata
- Reference files for complex topics (>300 lines)
- Include examples in reference docs
- Update tests when adding features

### Security
- No malware or exploit code
- Skills shouldn't surprise users in intent
- Respect system boundaries and authorization
- Safe fallbacks for external APIs

---

## Continuous Integration

### Workflows
- **CodeQL**: Automatic code quality and security analysis
- **SLSA**: Generate provenance information for builds

### Pre-Commit Checks
- Skills should be syntactically valid
- References should be findable from SKILL.md
- No broken file paths in documentation

---

## Common Tasks

### Adding a New Skill
1. Create `skills/skill-name/` directory
2. Write `SKILL.md` with frontmatter and instructions
3. Add to `.claude-plugin/marketplace.json` in appropriate plugin
4. Create test cases if applicable
5. Commit, push to feature branch, create PR

### Updating an Existing Skill
1. Edit `skills/skill-name/SKILL.md`
2. Update reference files as needed
3. Update test cases if behavior changed
4. Commit with clear message about what changed
5. Push and create PR if significant changes

### Adding Documentation
1. Create or edit `.md` files in root or skill `references/`
2. Link from relevant SKILL.md files
3. Follow existing documentation patterns
4. Test links and examples

### Publishing to Production
1. Merge PR to main branch
2. GitHub Actions run CI/CD checks
3. Marketplace automatically picks up changes
4. Update version in marketplace.json if major release

---

## Testing & Evaluation

### Test Types
- **Qualitative**: Run skill on sample prompts, review outputs
- **Quantitative**: Create 10+ eval questions with expected answers
- **Performance**: Benchmark against metrics (accuracy, latency, cost)

### Running Tests
Save test prompts to `evals/evals.json`:
```json
{
  "skill_name": "example-skill",
  "evals": [
    {
      "prompt": "Test prompt 1",
      "expected_contains": ["output fragment"],
      "expected_exact": null
    }
  ]
}
```

Run evaluations while drafting assertions. Review results and iterate.

---

## Repository Statistics

### Current State (as of August 2026)
- **21 skills** across categories
- **3 plugin collections** in marketplace
- **2 CI/CD workflows** for quality and security
- **Recent additions**: Business skills, auth configs, security analysis

### Recent Work
- Registered business-focused skills in marketplace plugin
- Added enterprise skills: chief-of-staff, business-opportunity-finder, venture-builder, sell-your-skill
- Implemented CI/CD workflows: CodeQL analysis and SLSA provenance generation
- Added comprehensive authentication documentation (Anthropic, OpenAI)
- Completed test coverage analysis and examples documentation

---

## Quick Reference: Key Paths

| Item | Path |
|------|------|
| All skills | `./skills/` |
| Skill template | `./template/SKILL.md` |
| Marketplace config | `./.claude-plugin/marketplace.json` |
| Spec (external) | https://agentskills.io/specification |
| Document skills | `./skills/{docx,pdf,pptx,xlsx}/` |
| MCP guide | `./skills/mcp-builder/` |
| Skill creator | `./skills/skill-creator/` |

---

## Resources for AI Assistants

### For Skill Development
1. Read this CLAUDE.md file first
2. Study existing skills in relevant category
3. Review `./skills/skill-creator/SKILL.md` for deep guidance
4. Check `./template/SKILL.md` for minimal structure
5. Refer to `TESTING_EXAMPLES.md` for evaluation patterns

### For Marketplace Integration
1. Understand plugin structure in `.claude-plugin/marketplace.json`
2. Know which plugin collection your skill belongs to
3. Update marketplace.json when adding new skills
4. Test installation via `/plugin install` in Claude Code

### For PR & Commits
1. Keep commits focused (one feature per commit)
2. Write clear, descriptive messages
3. Reference skill names in commit messages
4. Test changes locally before pushing
5. Create PR with clear description of changes

### External References
- **Agent Skills Spec**: https://agentskills.io/specification
- **Claude Skills Support**: https://support.claude.com/
- **How to Create Custom Skills**: https://support.claude.com/en/articles/12512198-creating-custom-skills
- **Using Skills in Claude**: https://support.claude.com/en/articles/12512180-using-skills-in-claude

---

## Notes for Collaborators

- **Test thoroughly**: Implementations may differ from production Claude
- **No surprises**: Skills must match their description; no hidden behavior
- **Community focused**: These are educational and demonstration resources
- **Iterative improvement**: Skills can be updated based on feedback
- **Attribution**: Maintain proper licensing and contributor attribution

---

**Last Updated**: August 7, 2026  
**Branch**: claude/claude-md-docs-8de5cj  
**Scope**: All skills, core repository structure, development workflows, marketplace plugin configuration
