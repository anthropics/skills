# Shell Tools for macOS - Claude Skill

A comprehensive Claude skill for leveraging 20 modern CLI tools optimized for Claude Code workflows on macOS.

## Overview

This skill provides expertise in using modern command-line tools for efficient project work:

**Core search & analysis (8):**
- fd, ripgrep, ast-grep, jq, yq, tokei, sd, shellcheck

**Git & collaboration (2):**
- gh, git-delta

**Development tools (5):**
- httpie, watchexec, hyperfine, difftastic, fzf

**Project automation (5):**
- mise, just, pre-commit, direnv (optional), sops/age (optional)

## What's Included

```
shell-tools-osx/
├── SKILL.md                          # Main skill (lean, workflow-focused)
├── INSTALL.md                        # Installation instructions
├── README.md                         # This file
├── scripts/                          # Executable helper scripts
│   ├── search-and-preview.sh        # Interactive file search
│   ├── code-search-replace.sh       # Guided AST refactoring
│   ├── project-setup.sh             # Bootstrap project configs
│   └── analyze-codebase.sh          # Quick codebase analysis
├── references/                       # Detailed documentation
│   └── commands.md                  # Comprehensive command reference (20 tools)
└── assets/                          # Template configs
    ├── .mise.toml
    ├── justfile                     # Updated with new tools
    ├── .pre-commit-config.yaml      # Includes shellcheck
    ├── .envrc                       # (optional)
    └── .sops.yaml                   # (optional)
```

## Design Principles

This skill follows Claude skill best practices:

### Progressive Disclosure

1. **Metadata** (~100 words): Name and description always in context
2. **SKILL.md** (<5k words): Loaded when skill triggers - lean, workflow-focused
3. **Bundled Resources** (unlimited): Loaded as needed by Claude

### Bundled Resources Strategy

**Scripts (`scripts/`)** - Executable code for:
- Deterministic reliability (same output every time)
- Token efficiency (execute without loading into context)
- Tasks that would be repeatedly rewritten

**References (`references/`)** - Documentation for:
- Detailed command syntax and options
- Advanced workflows
- Information Claude should reference while working
- Large reference material (searchable with `rg`)

**Assets (`assets/`)** - Files for output:
- Config file templates
- Files that get copied or modified for projects
- Not intended to be loaded into context

### Writing Style

- **Imperative/infinitive form** throughout (verb-first instructions)
- Objective, instructional language
- No second person ("you")
- Focus on copy-pasteable commands
- Dry-run/preview before destructive operations

## Improvements Made

This improved version includes:

1. **Reorganized SKILL.md**
   - Rewritten in imperative form per skill-creator guidelines
   - Lean, workflow-focused content (moved detailed reference to `references/`)
   - Clear "When to Use This Skill" section
   - Better structured with essential workflows up front

2. **Comprehensive Command Reference**
   - `references/commands.md` with detailed syntax, options, examples
   - Organized by tool category
   - Includes common workflows and integration examples
   - Searchable without loading entire file into context

3. **Helper Scripts**
   - `search-and-preview.sh` - Interactive file search with fzf + preview
   - `code-search-replace.sh` - Guided AST-aware refactoring workflow
   - `project-setup.sh` - Bootstrap projects with all config templates
   - `analyze-codebase.sh` - Quick codebase analysis with tokei, rg, shellcheck

4. **Template Configs**
   - Production-ready examples for all 5 high-leverage tools
   - Well-commented with common patterns
   - Ready to copy and customize

5. **Improved Description**
   - More concise and focused
   - Clear trigger conditions
   - Lists all tools for discoverability

## Installation

See [INSTALL.md](INSTALL.md) for complete installation instructions.

**Quick start:**
```bash
# Package the skill
zip -r shell-tools-osx.zip . -x "*.git*" -x "*.DS_Store"

# Install essential CLI tools (macOS)
brew install fd ripgrep ast-grep jq yq gh shellcheck tokei sd git-delta httpie \
             mise just pre-commit watchexec hyperfine difftastic

# Install optional tools
brew install fzf direnv sops age
```

## Usage Examples

**In Claude conversations:**

- "Search this codebase for all instances of `fetchUser`"
- "Refactor all console.log statements to use logger.debug"
- "Analyze this codebase and give me statistics"
- "Update docker-compose.yml to use Node 20"
- "Create a GitHub PR for my changes"
- "Help me set up a justfile for this project"
- "Validate all shell scripts in this repo"
- "Benchmark the test suite"

**Direct CLI usage:**

```bash
# Quick codebase analysis
./scripts/analyze-codebase.sh

# Interactive file search with preview
./scripts/search-and-preview.sh

# Guided code refactoring
./scripts/code-search-replace.sh ts 'console.log($X)' 'logger.debug($X)'

# Bootstrap new project
./scripts/project-setup.sh /path/to/project
```

## Skill Development

This skill was improved using the `skill-creator` skill, following Anthropic's skill development best practices:

1. **Understanding** - Analyzed concrete usage examples
2. **Planning** - Identified reusable scripts, references, and assets
3. **Implementation** - Created bundled resources and rewrote SKILL.md
4. **Documentation** - Updated all supporting files

### Key Decisions

- **Moved detailed reference to `references/`** - Keeps SKILL.md lean (~5k words) while making comprehensive documentation available when needed
- **Added executable scripts** - Common workflows that would be repeatedly rewritten now stored for token efficiency
- **Included template configs** - Ready-to-use examples for project setup
- **Imperative writing style** - Consistent with skill best practices for AI consumption

## Contributing

To improve this skill:

1. Make changes to SKILL.md, scripts, references, or assets
2. Test with Claude to ensure it works as expected
3. Re-package: `zip -r shell-tools-osx.zip . -x "*.git*" -x "*.DS_Store"`
4. Validate using packaging script if available

## License

This skill is provided as-is for use with Claude. The included tools are open-source software with their own licenses.

## References

- [Anthropic Skills Documentation](https://docs.anthropic.com/claude/docs/skills)
- [skill-creator skill](https://github.com/anthropics/claude-skills) - Used to improve this skill
- Individual tool documentation: See `references/commands.md`
