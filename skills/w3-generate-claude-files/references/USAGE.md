# Usage Guide - Generate Claude Files Skill

## Overview

This skill uses **prompts and analysis** (not shell scripts) to help you generate three essential documentation files:

- **CLAUDE.md** - Project Constitution
- **CODEMAP.md** - Codebase Architecture Map
- **MEMORY.md** - Project Context & Knowledge Base

---

## ✨ Three Ways to Use This Skill

### Method 1: Super Quick (15 minutes) 🏃

Perfect for: Small projects, simple structure

1. Open **QUICK_START_PROMPTS.md**
2. Copy Phase 1 prompt → Paste into Claude with your project info
3. Copy Phase 2-4 prompts → Generate your three files
4. Done!

**Result**: Quick documentation for small projects

### Method 2: Thorough (45-60 minutes) 📖

Perfect for: Medium to large projects, detailed documentation

1. Follow **PROMPT_BASED_WORKFLOW.md** step-by-step
2. Answer all analysis questions in Phase 1
3. Use prompts in Phases 2-4 to generate files
4. Review and customize output

**Result**: Professional, detailed documentation

### Method 3: AI-Assisted (30 minutes) 🤖

Perfect for: Balance of speed and quality

1. Do Phase 1 analysis manually (answer questions)
2. Use Phase 2-4 prompts with Claude to generate files
3. Review and customize
4. Done!

**Result**: High-quality docs with less manual work

---

## How It Works

```
You provide:
  ↓
Project analysis (tech stack, structure, patterns)
  ↓
Claude generates:
  ↓
CLAUDE.md + CODEMAP.md + MEMORY.md
  ↓
You customize & commit
```

---

## What Gets Generated

### CLAUDE.md - Project Constitution

✅ Tech stack overview specific to your project
✅ Critical coding rules (validation, error handling, testing)
✅ Project structure documentation
✅ Step-by-step feature addition guide
✅ Pre-commit verification checklist

### CODEMAP.md - Architecture Map

✅ Directory structure with clear purposes
✅ Request/response flow diagrams
✅ Key files and their functions
✅ Navigation guides (how to find code)
✅ Service layer and pattern documentation

### MEMORY.md - Context Knowledge Base

✅ Quick facts about your project
✅ Important code conventions with examples
✅ Known gotchas and their solutions
✅ Performance issues and fixes
✅ Security checklist
✅ Testing patterns

---

## Step-by-Step Guide

### Step 1: Prepare Your Project Info

Gather basic information:

- Project name and purpose
- Technology stack (framework, database, testing)
- Directory structure
- Code examples (validation, error handling, API response)
- Known issues or pain points

### Step 2: Choose Your Approach

- **Quick?** → Use QUICK_START_PROMPTS.md
- **Thorough?** → Use PROMPT_BASED_WORKFLOW.md
- **Balanced?** → Manual Phase 1 + prompts Phase 2-4

### Step 3: Follow the Prompts

Each prompt guides you through generating one file:

- **Phase 1**: Analyze your repository
- **Phase 2**: Generate CLAUDE.md
- **Phase 3**: Generate CODEMAP.md
- **Phase 4**: Generate MEMORY.md

### Step 4: Customize Output

Review the generated files and:
- Remove any placeholder text
- Add project-specific details
- Fix any inaccuracies
- Add company or team conventions

### Step 5: Use Your Documentation

Reference in your Claude requests:

```
See CLAUDE.md, CODEMAP.md, MEMORY.md for context
```

---

## Supported Tech Stacks

### Languages & Runtimes

- Node.js/JavaScript
- Python
- Go
- Java
- C#
- Ruby
- PHP

### Frameworks

- Express, Fastify, NestJS (Node.js)
- Django, FastAPI, Flask (Python)
- Gin, Echo, Chi (Go)
- Spring Boot (Java)
- ASP.NET Core (C#)

### Databases

- PostgreSQL, MySQL, SQLite
- MongoDB, CouchDB
- DynamoDB, Firestore

### Testing Frameworks

- Jest, Vitest, Mocha (JavaScript)
- pytest, unittest (Python)
- Go testing, Testify (Go)
- JUnit, TestNG (Java)

---

## Example Workflows

### Express + PostgreSQL + Jest (Simple API)

**Time**: ~15-20 minutes

1. Copy Phase 1 prompt
2. Provide: Express info, PostgreSQL schema overview, Jest setup
3. Get structured analysis
4. Use Phase 2-4 prompts to generate files
5. Review and customize with Express-specific patterns

**Generated Files**:

- CLAUDE.md (~500 lines): Express rules, validation patterns, testing standards
- CODEMAP.md (~400 lines): Route structure, middleware stack, database layer
- MEMORY.md (~300 lines): Common gotchas, performance tips, security checks

### NestJS + MongoDB + Vitest (Microservice)

**Time**: ~45-60 minutes

1. Follow PROMPT_BASED_WORKFLOW.md Phase 1 completely
2. Document: NestJS modules, MongoDB patterns, Vitest structure
3. Provide: Code examples for each pattern type
4. Use Phase 2-4 prompts with detailed analysis
5. Customize with team-specific conventions

**Generated Files**:

- CLAUDE.md (~800 lines): NestJS patterns, dependency injection, module structure
- CODEMAP.md (~600 lines): Service architecture, request flow, API endpoints
- MEMORY.md (~500 lines): Common issues, performance optimization, security patterns

### Multi-Service Platform (Complex)

**Time**: ~60 minutes

1. Analyze each service separately in Phase 1
2. Document: Shared patterns, API gateways, auth architecture
3. Use Phase 2-4 prompts with comprehensive analysis
4. Integrate documentation across services

**Generated Files**:

- CLAUDE.md (~1000+ lines): Cross-service standards, shared patterns
- CODEMAP.md (~800+ lines): Service architecture, communication patterns
- MEMORY.md (~700+ lines): Platform-wide gotchas, security measures

---

## Common Questions

**Q: How long does it take?**
A: 15-60 minutes depending on project size and your chosen approach

**Q: Do I need to write code?**
A: No! This skill uses prompts and analysis, not code generation

**Q: Works with all backend languages?**
A: Yes! Node.js, Python, Go, Java, C#, Ruby, PHP - any backend project

**Q: Will files stay updated?**
A: You update them manually as your project evolves

**Q: Can I use with existing projects?**
A: Absolutely! Works with projects of any age and complexity

**Q: Should I commit these to git?**
A: Yes! They're valuable documentation for your team and future AI assistance

---

## Next Steps

1. **Choose your approach** (Quick/Thorough/Balanced)
2. **Open the appropriate guide**:
   - Quick: QUICK_START_PROMPTS.md
   - Thorough: PROMPT_BASED_WORKFLOW.md
3. **Follow the workflow** with your project information
4. **Customize the generated files** for your specific needs
5. **Reference** in future Claude requests

---

## Resources

- **SKILL.md** - Overview of what this skill does
- **HOW_TO_USE_THIS_SKILL.md** - Complete getting started guide
- **PROMPT_BASED_WORKFLOW.md** - Detailed 4-phase workflow
- **QUICK_START_PROMPTS.md** - Copy-paste prompts for Claude
- **CLAUDE.md.template** - Template reference
- **CODEMAP.md.template** - Template reference
- **MEMORY.md.template** - Template reference

---

**Last Updated**: February 2026
**Approach**: Prompt-based (no shell scripts)
**Status**: Ready to use ✅
