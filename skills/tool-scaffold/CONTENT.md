# Tool Scaffold Template

This document describes the standard structure for creating new MCP tools in this repository. Use this as a template when adding new tools.

## Directory Structure

```
tools/{tool-id}/
├── SKILL.md                 # Skill definition with YAML frontmatter and instructions
├── package.json             # NPM package configuration
├── README.md               # User-facing documentation with examples
├── LICENSE                 # MIT License
├── src/                    # Source code (for TypeScript/JavaScript tools)
│   ├── index.ts
│   ├── cli.ts              # CLI entry point (if applicable)
│   └── types.ts            # Type definitions
├── templates/              # Default templates (if applicable)
│   └── example.template
├── tests/                  # Test suite
│   └── index.test.ts
└── docs/                   # Additional documentation
    ├── API_REFERENCE.md
    └── CONTRIBUTING.md
```

## Files

### 1. SKILL.md

YAML frontmatter + Markdown content. Defines the skill for Claude.

```yaml
---
name: tool-id              # Unique identifier (lowercase, hyphens for spaces)
description: Brief description of what the tool does and when to use it
license: MIT
---
```

**Sections**:
- **When to Use**: Use cases and contexts
- **Core Capabilities**: Main features (numbered list)
- **Usage Examples**: Practical examples with code blocks
- **Input Schema**: Configuration/parameters (JSON/TypeScript)
- **Output Structure**: What the tool produces
- **Best Practices**: Guidelines for effective use
- **Attribution**: Link to https://github.com/fused-gaming

### 2. package.json

```json
{
  "name": "@fused-gaming/{tool-id}",
  "version": "1.0.0",
  "description": "Tool description",
  "license": "MIT",
  "repository": {
    "type": "git",
    "url": "https://github.com/fused-gaming/skills"
  },
  "keywords": ["keyword1", "keyword2"],
  "main": "dist/index.js",
  "types": "dist/index.d.ts",
  "files": ["dist/", "README.md", "LICENSE"],
  "scripts": {
    "build": "tsc",
    "test": "jest",
    "lint": "eslint src/",
    "prepublish": "npm run build && npm test"
  },
  "dependencies": {},
  "devDependencies": {},
  "engines": {
    "node": ">=18.0.0"
  }
}
```

Key requirements:
- Scope: `@fused-gaming/{tool-id}`
- License: MIT
- Include `build`, `test`, `lint` scripts
- Include `prepublish` script
- Node 18+ minimum

### 3. README.md

User-facing documentation with:
- **Features**: Bulleted list of capabilities
- **Installation**: npm/yarn/pip instructions
- **Quick Start**: 5-minute getting started
- **Usage Examples**: Multiple realistic examples
- **CLI Commands**: Full command reference (if CLI tool)
- **Configuration**: Config file format and options
- **Output Formats**: Types of outputs produced
- **Integration Examples**: How to use in workflows (Git, CI/CD, etc.)
- **Best Practices**: Guidelines
- **Troubleshooting**: Common issues and solutions
- **Attribution**: Link to https://github.com/fused-gaming
- **Support**: Links to issues/discussions

### 4. src/ Directory

**index.ts** (main export):
```typescript
export { ToolClass } from './tool';
export { ToolConfig, ToolOutput } from './types';
```

**types.ts** (type definitions):
```typescript
import { z } from 'zod';

export const ToolConfigSchema = z.object({
  // Define input schema with Zod
});

export type ToolConfig = z.infer<typeof ToolConfigSchema>;

export interface ToolOutput {
  // Define output structure
}
```

**cli.ts** (CLI entry, if applicable):
```typescript
#!/usr/bin/env node

import { program } from 'commander';
// CLI implementation
```

### 5. tests/ Directory

Use Jest for testing:

```typescript
// tests/index.test.ts
import { Tool } from '../src';

describe('Tool', () => {
  it('should create output', async () => {
    // Test implementation
  });
});
```

### 6. docs/ Directory

**API_REFERENCE.md**: Complete API documentation
**CONTRIBUTING.md**: Contribution guidelines

## Publishing Checklist

Before publishing to npm:

- [ ] Zero TypeScript errors (`npm run build`)
- [ ] All tests pass (`npm test`)
- [ ] Linting passes (`npm run lint`)
- [ ] README has at least 3 working examples
- [ ] `package.json` has all required fields
- [ ] Version bumped in `package.json`
- [ ] `SKILL.md` has attribution section
- [ ] `LICENSE` file present (MIT)
- [ ] `.npmignore` configured (or `files` in package.json)
- [ ] GitHub Actions CI/CD set up
- [ ] All input/output schemas documented
- [ ] No hardcoded secrets or credentials

## Publish to npm

```bash
# Build and test
npm run prepublish

# Publish
npm publish

# Verify
npm view @fused-gaming/{tool-id}
```

## Naming Conventions

- **Directory**: `{tool-id}` (lowercase, hyphens for spaces)
- **Package**: `@fused-gaming/{tool-id}`
- **Commands**: lowercase with hyphens (e.g., `mermaid view`, `journey create`)
- **Functions**: camelCase (e.g., `createJourney`, `exportDiagram`)
- **Classes**: PascalCase (e.g., `JourneyMapper`, `MermaidRenderer`)
- **Types**: PascalCase with suffix (e.g., `ToolConfig`, `ToolOutput`)

## Example Tool Structure

See these tools as examples:
- **ux-journey-mapper**: Complex data visualization tool
- **mermaid-terminal**: CLI-based tool with rendering

## Best Practices

1. **Zod for validation**: All inputs should validate with Zod schemas
2. **Clear errors**: Provide actionable error messages with suggestions
3. **JSON output**: Always provide structured JSON output alongside human-readable text
4. **Versioning**: Use semantic versioning (major.minor.patch)
5. **Documentation**: Prioritize documentation - it's used more than code
6. **Examples**: Include at least 3 realistic examples in README
7. **Testing**: Aim for >80% code coverage
8. **Attribution**: Always credit original creators/sources
9. **License**: MIT for all public tools
10. **Git history**: Clean commit history with descriptive messages

## Monorepo vs. Separate Repos

Currently, all tools are in `/skills/skills/{tool-id}/` directories within the monorepo.

To extract a tool to its own repository:
1. Create GitHub repo: `github.com/fused-gaming/{tool-id}`
2. Copy tool directory contents
3. Set up CI/CD (GitHub Actions)
4. Publish to npm from separate repo
5. Update main repo to reference separate repo

## Quick Copy Command

```bash
# Create new tool from this template
mkdir -p skills/{tool-id}/{src,tests,docs}
cp template/SKILL.md skills/{tool-id}/
cp template/package.json skills/{tool-id}/ # Update package.json with tool-id
```

## Support & Questions

See the SKILL.md file for contribution guidelines and support channels.
