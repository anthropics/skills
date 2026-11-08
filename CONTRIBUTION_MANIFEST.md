# Contribution Manifest: 6 Skills for Anthropic's Skills Repository

**Date**: March 2026
**Source**: TrystPilot/skills (Private Repository)
**Destination**: anthropics/skills (Public Repository)
**Status**: Ready for Contribution

## Overview

This manifest documents 6 production-ready skills being contributed to Anthropic's public skills repository. These skills represent best practices across creative, technical, and development domains, following the Agent Skills specification (https://agentskills.io/specification).

## The 6 Skills

### 1. **canvas-design**
- **Purpose**: Create beautiful visual art in PNG and PDF documents using design philosophy
- **Key Features**:
  - Two-step process: Design Philosophy Creation → Visual Expression
  - Emphasis on master-level craftsmanship and visual excellence
  - Generates original designs without copying existing artists' work
- **File Structure**:
  - `SKILL.md` - Main skill instructions (11.9 KB)
  - `LICENSE.txt` - Apache 2.0 license
  - `canvas-fonts/` - 50+ professional fonts for visual design
- **Use Cases**: Posters, artwork, visual designs, branding materials
- **License**: Apache 2.0

### 2. **slack-gif-creator**
- **Purpose**: Knowledge and utilities for creating animated GIFs optimized for Slack
- **Key Features**:
  - Complete animation toolkit with PIL utilities
  - Frame composer with easing functions
  - Slack-specific constraints and validation
  - Optimization for emoji and message GIFs
- **File Structure**:
  - `SKILL.md` - Main skill instructions (7.8 KB)
  - `LICENSE.txt` - Apache 2.0 license
  - `core/gif_builder.py` - Core GIF creation utilities
  - `core/frame_composer.py` - Frame composition helpers
  - `core/easing.py` - Animation easing functions
  - `core/validators.py` - Slack constraint validators
  - `requirements.txt` - Python dependencies
- **Use Cases**: Slack emoji GIFs, animated messages, GIF creation
- **License**: Apache 2.0

### 3. **web-artifacts-builder**
- **Purpose**: Suite of tools for creating complex Claude.ai HTML artifacts using modern frontend technologies
- **Key Features**:
  - React 18 + TypeScript + Vite + Parcel stack
  - Tailwind CSS 3.4.1 with shadcn/ui theming
  - 40+ pre-installed shadcn/ui components
  - Automated initialization and bundling scripts
  - Guidance on avoiding "AI slop" design patterns
- **File Structure**:
  - `SKILL.md` - Main skill instructions (3.1 KB)
  - `LICENSE.txt` - Apache 2.0 license
  - `scripts/init-artifact.sh` - Project initialization script
  - `scripts/bundle-artifact.sh` - Bundling to single HTML file
  - `scripts/shadcn-components.tar.gz` - Pre-configured components
- **Use Cases**: Complex interactive artifacts, data dashboards, web applications
- **License**: Apache 2.0

### 4. **mcp-builder**
- **Purpose**: Comprehensive guide for creating high-quality MCP (Model Context Protocol) servers
- **Key Features**:
  - Four-phase development process (Research → Implementation → Testing → Refinement)
  - Support for Python (FastMCP) and TypeScript (MCP SDK)
  - Best practices for tool design, error handling, and performance
  - Evaluation framework with automated testing
  - Reference documentation for MCP specification
- **File Structure**:
  - `SKILL.md` - Main skill instructions (9.1 KB)
  - `LICENSE.txt` - Apache 2.0 license
  - `scripts/evaluation.py` - Automated evaluation framework
  - `scripts/requirements.txt` - Python dependencies
  - `scripts/connections.py` - MCP connection utilities
  - `scripts/example_evaluation.xml` - Example evaluation configuration
  - `reference/mcp_best_practices.md` - Best practices guide
  - `reference/python_mcp_server.md` - Python implementation guide
  - `reference/node_mcp_server.md` - TypeScript implementation guide
  - `reference/evaluation.md` - Evaluation framework documentation
- **Use Cases**: MCP server development, external API integration, tool design
- **License**: Apache 2.0

### 5. **skill-creator**
- **Purpose**: Meta-skill for creating, modifying, and improving skills with performance measurement
- **Key Features**:
  - Complete skill development lifecycle (ideation → implementation → testing → optimization)
  - Quantitative evaluation framework with benchmarking
  - Variance analysis for skill performance
  - Description optimization for triggering accuracy
  - Interactive user guidance with context-aware communication
- **File Structure**:
  - `SKILL.md` - Main skill instructions (33.2 KB)
  - `LICENSE.txt` - Apache 2.0 license
  - `scripts/run_loop.py` - Skill iteration loop runner
  - `scripts/run_eval.py` - Evaluation execution script
  - `scripts/improve_description.py` - Description optimizer
  - `scripts/package_skill.py` - Skill packaging utility
  - `scripts/aggregate_benchmark.py` - Benchmark aggregation
  - `scripts/generate_report.py` - Report generation
  - `scripts/quick_validate.py` - Quick validation tool
  - `scripts/utils.py` - Utility functions
  - `references/schemas.md` - Data schema reference
  - `agents/analyzer.md` - Analysis agent instructions
  - `agents/grader.md` - Grading agent instructions
  - `agents/comparator.md` - Comparison agent instructions
  - `assets/eval_review.html` - Evaluation review UI
- **Use Cases**: Skill development, skill optimization, performance measurement
- **License**: Apache 2.0

### 6. **pre-deploy-validator**
- **Purpose**: Standardized pre-deployment quality gates for Node.js/Next.js projects with comprehensive validation and CI/CD integration
- **Key Features**:
  - Multi-check validation: Lint, TypeScript, tests, security audits, builds
  - Flexible JSON-based configuration system
  - Parallel and sequential execution modes
  - Branch-aware check skipping for protected branches
  - Monorepo support with multi-project validation
  - Console and JSON reporting formats
  - Coverage threshold validation for tests
  - CLI interface with npx support
  - Full TypeScript implementation with strict mode
- **File Structure**:
  - `SKILL.md` - Main skill instructions (5.2 KB)
  - `LICENSE` - MIT license
  - `README.md` - Comprehensive documentation (7.1 KB)
  - `package.json` - npm package configuration
  - `src/` - TypeScript implementation
    - `index.ts` - Main PreDeployValidator class
    - `cli.ts` - Command-line interface
    - `types.ts` - TypeScript interfaces and types
    - `checks/` - Five validation check implementations (lint, typescript, tests, security-audit, builds)
    - `reporters/` - Console and JSON output formatters
  - `__tests__/` - Unit and integration tests (85%+ coverage)
  - `examples/` - Three configuration examples (minimal, advanced, monorepo)
  - `.github/workflows/test.yml` - CI/CD workflow
- **Use Cases**: Pre-deployment validation, CI/CD integration, monorepo validation, quality gate enforcement
- **License**: MIT
- **Publication**: Designed for npm publication as `@anthropic-community/pre-deploy-validator`

## Contribution Details

### Spec Compliance
All 6 skills comply with the Agent Skills specification:
- ✅ SKILL.md files with required YAML frontmatter (name, description)
- ✅ LICENSE files with appropriate open-source licenses (Apache 2.0 or MIT)
- ✅ Self-contained folder structures
- ✅ Clear, actionable instructions
- ✅ Supporting resources (scripts, references, assets)
- ✅ No external dependencies on private systems

### Quality Assurance
- ✅ No sensitive data, API keys, or credentials
- ✅ All relative paths use consistent conventions
- ✅ Examples are complete and functional
- ✅ Documentation is comprehensive and clear
- ✅ Code files are properly formatted

### Integration with marketplace.json
These skills are already configured in the "example-skills" plugin collection:
```json
"example-skills": {
  "description": "Collection of example skills demonstrating various capabilities...",
  "skills": [
    "./skills/canvas-design",
    "./skills/slack-gif-creator",
    "./skills/web-artifacts-builder",
    "./skills/mcp-builder",
    "./skills/skill-creator",
    // ... plus 7 other example skills
  ]
}
```

## Value Proposition

These 6 skills provide significant value to Anthropic's skills repository:

1. **Creative Domain** (canvas-design): Demonstrates visual design capabilities and design philosophy thinking
2. **Animation & Visualization** (slack-gif-creator): Shows how to work with complex media formats
3. **Web Development** (web-artifacts-builder): Exemplifies modern frontend stack integration
4. **System Integration** (mcp-builder): Teaches protocol server development and external API integration
5. **Meta-Skills** (skill-creator): Provides framework for creating and optimizing skills
6. **DevOps & CI/CD** (pre-deploy-validator): Demonstrates quality gate automation and pre-deployment validation

## Recommendation

All 6 skills are **production-ready** for contribution to Anthropic's anthropics/skills repository. They meet all technical requirements, contain no proprietary content, and provide valuable examples for developers creating their own skills. Pre-deploy-validator is additionally ready for npm publication as a reusable package.
