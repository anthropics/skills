# Quick Start: Copy-Paste Prompts for Claude

Use these prompts with Claude to generate your documentation files.

---

## 📌 How to Use This Guide

1. Copy a prompt below
2. Paste into Claude with your repository context
3. Claude will generate the appropriate file
4. Copy the output into your project
5. Customize as needed

---

## Phase 1: Repository Analysis Prompt

Use this to gather information about your repository.

```markdown
Analyze my backend repository and answer these questions:

## Project Identity
1. What is the project name?
2. What is the primary purpose in 1 sentence?
3. What type of project is it? (REST API, Microservice, CLI, etc.)
4. What business problem does it solve?

## Technology Stack
- Programming language: (Python, Go, Java, Node.js, C#, etc.)
- Framework: (Django, FastAPI, Express, Spring Boot, etc.)
- Database: (PostgreSQL, MongoDB, MySQL, SQLite, etc.)
- ORM/Query builder: (SQLAlchemy, Prisma, Gorm, etc.)
- Validation: (Zod, Pydantic, etc.)
- Auth: (JWT, Session, OAuth?)
- Logger: (Winston, Pino, Python logging, etc.)
- Testing: (Jest, pytest, JUnit, etc.)

## Directory Structure
Show me the main directory structure:
\`\`\`bash
ls -la src/ (or equivalent main directory)
\`\`\`

Then describe:
1. What is in your main API/routes directory?
2. What is in your business logic directory?
3. What is in `/src/middleware/`? (auth, validation, errors?)
4. What is in `/src/utils/`? (helpers, logger, errors?)
5. Are there migrations? Where?

## Code Patterns
Show me:
1. An example of input validation (from any route/controller)
2. An example of error handling (try/catch)
3. An example of logging (logger call)
4. An example API response (success and error)

## Pain Points
1. Are there any known performance issues?
2. Any common bugs or gotchas?
3. Any CORS/auth issues?
4. Any database issues?

Provide the answers to these questions, and I'll analyze your project.
```

---

## Phase 2: Generate CLAUDE.md Prompt

```markdown
Based on this project analysis:

[PASTE YOUR ANSWERS FROM PHASE 1]

Generate a CLAUDE.md file with:
1. **Project Overview**
   - Project name, purpose, type
   - Tech stack (framework, database, testing, auth, logging)

2. **Critical Rules**
   - Code Quality (type safety, proper naming, file/function size limits)
   - Input Validation (language-specific validation library or custom pattern)
   - Error Handling (exception handling pattern, custom error classes if used)
   - Logging (proper logging library usage, no debug prints)
   - Testing Requirements (80% coverage minimum, unit/integration/E2E)
   - Security (no hardcoded secrets, HTTPS, rate limiting, CORS)
   - Git & Commits (conventional commits, branch naming)

3. **Project Structure**
   - Show the actual directory structure from the analysis

4. **How to Add Features**
   - Step-by-step guide for adding a new API endpoint/handler
   - Include code examples from the project's actual patterns

5. **API Response Format**
   - Show the standard success response format
   - Show the standard error response format

6. **Decision Matrix**
   - When to ask first (architecture, tech choice, breaking changes)
   - When to decide autonomously (bug fixes, refactoring)

7. **Pre-Commit Checklist**
   - Compilation/Build check
   - Linter/Format check
   - Tests and coverage
   - No console.log, no secrets
   - Code quality checks

Use SPECIFIC examples from the project, not generic templates.
Include actual file paths and real code snippets.
```

---

## Phase 3: Generate CODEMAP.md Prompt

```markdown
Based on this project analysis:

[PASTE YOUR ANSWERS FROM PHASE 1]

Generate a CODEMAP.md file with:

1. **Project Overview** (ASCII art diagram of the project structure)

2. **Directory Structure** (for each main directory)
   For `/src/server.ts`: purpose, lines, key functions
   For `/src/api/`: how routes are organized, feature pattern
   For `/src/services/`: base service pattern, service examples
   For `/src/models/`: type definitions and zod schemas
   For `/src/middleware/`: list of middleware files and purposes
   For `/src/utils/`: helper functions (logger, errors, db, etc.)
   For `/src/types/`: TypeScript definitions
   For `/tests/`: unit, integration, E2E test locations

3. **Request Flow**
   - Show how a typical request flows through the system
   - Include all middleware steps
   - Show the controller → service → repository → database flow
   - Show error handling

4. **Key Dependencies**
   - Table of important packages and their versions

5. **File Purpose Quick Reference**
   - Table of important files with their purpose and line count

6. **How to Navigate**
   - How to add a new endpoint
   - How to understand the flow
   - How to debug an error
   - How to run tests

7. **Architecture Diagram**
   - ASCII art showing layered architecture
   - Show middleware chain, controller, service, repository layers

Include ACTUAL file paths, REAL function names, and CODE EXAMPLES from the project.
```

---

## Phase 4: Generate MEMORY.md Prompt

```markdown
Based on this project analysis:

[PASTE YOUR ANSWERS FROM PHASE 1]

Generate a MEMORY.md file with:

1. **Quick Facts** (table format)
   - Project name, purpose, tech stack
   - Auth type, database, cache, logging, deployment
   - Main pain point/challenge

2. **Architecture Overview** (diagram of how components interact)

3. **Key Files Quick Reference** (table)
   - Important files, their purpose, last modified date

4. **Important Conventions** (with CODE EXAMPLES)
   - Validation pattern (zod/class-validator)
   - Error handling pattern
   - Service layer pattern
   - Repository/database access pattern
   - API response wrapper
   - Logging pattern

5. **Known Gotchas** (document actual issues from Phase 1)
   - Performance issues and solutions
   - Auth/CORS issues and solutions
   - Database connection issues and solutions
   - Common bugs and how to avoid them
   - Testing/mocking issues

6. **Recent Changes & Context**
   - Notable recent changes to the codebase
   - Breaking changes made
   - Architecture decisions

7. **Performance Notes**
   - Slow endpoints and their fixes
   - Optimization opportunities
   - Caching strategies

8. **Security Checkpoints**
   - Checklist of security measures implemented
   - What's done, what's not done

9. **Testing Patterns**
   - Unit test pattern and location
   - Integration test pattern and location
   - E2E test pattern and location
   - How external APIs are mocked

Include REAL EXAMPLES and ACTUAL PATTERNS from the project.
Focus on this specific project's gotchas, not generic gotchas.
```

---

## 🎯 Complete Workflow in Claude

1. **Copy PHASE 1 PROMPT** → Paste into Claude
   - Include the repository context (you can paste structure)
   - Wait for analysis questions to be answered

2. **Copy your ANSWERS** + **PHASE 2 PROMPT** → New Claude message
   - Claude generates CLAUDE.md

3. **Copy your ANSWERS** + **PHASE 3 PROMPT** → New Claude message
   - Claude generates CODEMAP.md

4. **Copy your ANSWERS** + **PHASE 4 PROMPT** → New Claude message
   - Claude generates MEMORY.md

5. **Review & Customize**
   - Fix any inaccuracies
   - Remove placeholder values
   - Add company-specific rules

---

## 💡 Tips for Better Results

### When Copying Project Context
Include:
- `package.json` (dependencies)
- `tsconfig.json` (TypeScript config)
- Directory structure (run `tree -I 'node_modules' -L 3`)
- 2-3 representative files showing your patterns

### When Answering Questions
- Be specific, not generic
- Show actual examples from your code
- Include real numbers (file sizes, coverage %, dependencies)
- Document actual gotchas you've encountered

### When Using Generated Files
- Review immediately for accuracy
- Update placeholder values
- Add missing context
- Keep Last Updated date current
- Update as your project evolves

---

## 📝 Example Project Context

If Claude asks for context, provide something like:

```markdown
## Project: User Management API

**Stack**:
- Express.js 4.18
- TypeScript (strict mode)
- PostgreSQL 14
- Prisma ORM
- Jest + Supertest
- Zod validation
- Winston logger
- JWT auth

**Structure**:
```
src/
├── api/
│   ├── users/
│   │   ├── routes.ts
│   │   ├── controller.ts
│   │   └── schema.ts
│   ├── auth/
│   └── ...
├── services/
│   ├── UserService.ts
│   └── AuthService.ts
├── middleware/
│   ├── auth.ts
│   ├── errorHandler.ts
│   └── validation.ts
└── server.ts
```

**Main file**: `src/server.ts`
**Entry point**: Starts Express on port 3000

**Pain points**:
- N+1 queries on user relationships
- JWT token refresh logic unclear
- Test setup verbose
```

---

## ✅ Validation Checklist

After generation, verify:

- [ ] **CLAUDE.md**: No placeholder values like [XX]
- [ ] **CLAUDE.md**: Real code examples from your project
- [ ] **CODEMAP.md**: Actual file paths documented
- [ ] **CODEMAP.md**: Real function names listed
- [ ] **MEMORY.md**: Gotchas specific to your project
- [ ] **MEMORY.md**: Code examples show your actual patterns
- [ ] All files have consistent formatting
- [ ] All cross-references are correct

---

## 🚀 Next Steps

After generating the three files:

1. Place them in your project root
2. Review for accuracy
3. Update Last Modified dates
4. Reference them in future Claude requests

Example:
```
"See CLAUDE.md, CODEMAP.md, and MEMORY.md for context about this project"
```

---

**Pro Tip**: Use these files for every Claude request about your project. It saves time and ensures Claude understands your architecture, conventions, and gotchas.

---

**Last Updated**: February 2026
**Version**: 1.0
