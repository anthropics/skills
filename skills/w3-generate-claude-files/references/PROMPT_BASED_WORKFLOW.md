# Prompt-Based Workflow: Generate CLAUDE.md, CODEMAP.md, MEMORY.md

**Approach**: Interactive prompts + manual analysis (minimal code generation)
**Duration**: ~45-60 minutes
**Tech**: Works for any Node.js/TypeScript project

---

## 🎯 Overview

This guide shows how to generate CLAUDE.md, CODEMAP.md, and MEMORY.md using **prompts instead of code**. You'll analyze your repository, answer questions, and use the answers to create comprehensive documentation.

**Advantage**: Personalized, contextual, accurate documentation tailored to YOUR specific project.

---

## 📋 Complete 4-Phase Workflow

### PHASE 1: Repository Analysis & Information Gathering (15-20 min)

Your goal: Understand your project completely before writing documentation.

#### Step 1.1: Project Identity Questions

Open your project and answer:

```markdown
## Project Identity

1. **Project Name**: [Name of your project]
2. **Brief Description** (1 sentence):
3. **Project Type**:
   - [ ] REST API
   - [ ] GraphQL API
   - [ ] Microservice
   - [ ] CLI Tool
   - [ ] Full-stack Backend
   - [ ] Other: ___

4. **Main Business Purpose**: [What problem does it solve?]
5. **Primary Users**: [Who uses this? Internal team? External? Consumers?]
```

#### Step 1.2: Technology Stack Questions

Check your `package.json` and answer:

```markdown
## Technology Stack

**Runtime & Language**
- Node.js version required: v[  ]
- TypeScript enabled: [ ] Yes [ ] No
- TypeScript strict mode: [ ] Yes [ ] No [ ] Not applicable

**Web Framework**
- Framework: [ ] Express [ ] NestJS [ ] Fastify [ ] Other: ___
- Version: [  ]

**Database**
- Database: [ ] PostgreSQL [ ] MongoDB [ ] MySQL [ ] SQLite [ ] Other: ___
- Version: [  ]
- ORM/Query Builder: [ ] Prisma [ ] TypeORM [ ] Sequelize [ ] Raw SQL [ ] Other: ___
- Migrations tool: [ ] Flyway [ ] Liquibase [ ] TypeORM [ ] Knex [ ] None

**Validation**
- Validation library: [ ] Zod [ ] Yup [ ] Class-validator [ ] Custom [ ] Other: ___

**Authentication & Authorization**
- Auth type: [ ] JWT [ ] Session [ ] OAuth [ ] None [ ] Other: ___
- Token storage: [ ] HTTP-only cookie [ ] Local storage [ ] Memory [ ] Other: ___

**Logging**
- Logger: [ ] Winston [ ] Pino [ ] Bunyan [ ] Console [ ] Other: ___

**Testing**
- Unit test framework: [ ] Jest [ ] Vitest [ ] Mocha [ ] Other: ___
- Integration test tool: [ ] Supertest [ ] Axios [ ] Custom [ ] Other: ___
- E2E testing: [ ] Playwright [ ] Cypress [ ] Selenium [ ] None [ ] Other: ___

**Additional Tools**
- Caching: [ ] Redis [ ] In-memory [ ] None
- Message Queue: [ ] RabbitMQ [ ] Kafka [ ] None
- External APIs: [ ] OpenAI [ ] Stripe [ ] Twilio [ ] Others: ___
- Monitoring: [ ] Sentry [ ] DataDog [ ] CloudWatch [ ] None
```

#### Step 1.3: Directory Structure Exploration

Navigate your project and map it:

```bash
# List your main directories
ls -la src/
ls -la tests/
```

Document the structure:

```markdown
## Directory Structure

```
[paste your actual structure here]

Example:
src/
├── api/          ← Purpose?
├── services/     ← Purpose?
├── models/       ← Purpose?
├── middleware/   ← Purpose?
├── utils/        ← Purpose?
├── types/        ← Purpose?
└── server.ts     ← Entry point?

tests/
├── unit/         ← How are unit tests structured?
├── integration/  ← How are integration tests structured?
└── e2e/          ← How are E2E tests structured?

migrations/      ← Database migrations present?
```
"""

#### Step 1.4: Code Pattern Analysis

Open 3-5 important files to understand patterns:

**Files to read:**
- `src/server.ts` or entry point
- One route file: `src/api/[feature]/routes.ts`
- One controller: `src/api/[feature]/controller.ts`
- One service: `src/services/[Feature]Service.ts`
- One test: `tests/integration/[feature].test.ts`

**Questions to answer while reading:**

```markdown
## Code Patterns Observed

### Validation Pattern
- Where is input validation done? (controller, middleware, service?)
- What library? (zod, class-validator, custom?)
- Example:
  [copy 5-10 lines showing validation]

### Error Handling Pattern
- How are errors thrown? (throw new Error, AppError class, etc?)
- How are errors caught? (try/catch, middleware?)
- Example:
  [copy 5-10 lines showing error handling]

### Logging Pattern
- Where is logging used?
- Format used? (console.log, logger.info, etc?)
- Example:
  [copy 5-10 lines showing logging]

### API Response Format
- How are successful responses formatted?
- How are error responses formatted?
- Example success response:
  [copy real example]
- Example error response:
  [copy real example]

### Service Layer Pattern
- How do controllers call services?
- How do services access database?
- Does repository pattern exist? (Y/N)
- Example:
  [copy 5-10 lines showing service pattern]

### Testing Pattern
- How are unit tests structured?
- How are integration tests structured?
- Mocking approach used?
- Example test:
  [copy 10-15 lines of actual test]
```

#### Step 1.5: Pain Points & Gotchas Identification

Document what you know about the project:

```markdown
## Known Issues & Gotchas

### Performance Issues
- Are there any slow endpoints? Which ones?
- Are there N+1 query problems?
- Database connection pooling configured?
- Pagination implemented?

### Security Issues
- Are secrets hardcoded anywhere?
- Rate limiting implemented? Where?
- CORS properly configured?
- Input validation comprehensive?

### Testing Issues
- Test coverage percentage?
- Flaky tests? Which ones?
- Test isolation issues?
- Mock configuration issues?

### Database Issues
- Migration issues encountered?
- Schema versioning problems?
- Connection timeout issues?

### Authentication Issues
- JWT expiration handling?
- Refresh token issues?
- CORS problems with auth?

### Common Developer Mistakes
- What do new developers get wrong?
- Common debugging steps?
- Frequent refactoring needs?
```

---

### PHASE 2: Generate CLAUDE.md (5-10 min)

Now you have all the information. Create CLAUDE.md:

#### Template to follow:

```markdown
# CLAUDE.md - Project Constitution

## 📋 Project Overview

**Name**: [From Step 1.1]
**Purpose**: [From Step 1.1]
**Type**: [From Step 1.1]

**Tech Stack**:
- Runtime: Node.js v[XX]+
- Language: TypeScript
- Framework: [From Step 1.2]
- Database: [From Step 1.2]
- Testing: [From Step 1.2]
- Additional: [From Step 1.2]

---

## ⚡ Critical Rules (MUST FOLLOW)

### Code Quality
- [ ] **TypeScript**: Strict mode ([yes/no])
- [ ] **No `any`**: Type everything explicitly
- [ ] **File Size**: Max 600 lines per file
- [ ] **Function Size**: Max 40 lines per function
- [ ] **Nesting Depth**: Max 3 levels
- [ ] **Immutability**: Use spread operator, never mutate

### Input Validation
[From Step 1.4 - Validation Pattern]
- [ ] All inputs validated with [zod/class-validator/custom]
- [ ] Validation schemas in [where?]
- [ ] Error handling: [error type?]

```typescript
// Your validation pattern
[paste your actual validation code]
```

### Error Handling
[From Step 1.4 - Error Handling Pattern]

```typescript
// Your error handling pattern
[paste your actual error handling code]
```

### Logging
- [ ] **NO console.log** in production code
- [ ] **Use**: [Winston/Pino/Bunyan]
- [ ] **Never log**: passwords, API keys, tokens

```typescript
// Your logging pattern
[paste your actual logging code]
```

### Testing Requirements
- [ ] **Minimum Coverage**: [XX]%
- [ ] **Unit Tests**: [location]
- [ ] **Integration Tests**: [location]
- [ ] **E2E Tests**: [location or "Not implemented"]
- [ ] **Mock External APIs**: [how you do it]

### Security (CRITICAL)
- [ ] **NO Hardcoded Secrets**: Use .env variables
- [ ] **VALIDATE All Inputs**: [your validation approach]
- [ ] **SANITIZE Outputs**: [your sanitization approach]
- [ ] **RATE LIMITING**: [configured? where?]
- [ ] **HTTPS Only**: In production
- [ ] **Error Messages**: Don't expose internal details

### Git & Commits
- [ ] **Conventional Commits**: `feat:`, `fix:`, `test:`, `docs:`, `refactor:`, `chore:`
- [ ] **Before Commit**: Tests pass + linter passes
- [ ] **Never Force Push**: To main/develop

---

## 📂 Project Structure

```
[your actual structure from Step 1.3]
```

---

## 🛠️ How to Add Features

### Adding New API Endpoint

[Show actual pattern from your codebase]

```typescript
// 1. Create schema (src/api/[feature]/schema.ts)
[real code example]

// 2. Create controller (src/api/[feature]/controller.ts)
[real code example]

// 3. Create route (src/api/[feature]/routes.ts)
[real code example]

// 4. Create service (src/services/[Feature]Service.ts)
[real code example]

// 5. Write tests (tests/integration/[feature].test.ts)
[real test example]
```

---

## 📌 API Response Format

```typescript
// Your actual API response format
[paste real examples]
```

---

## 🚨 When To Ask First

- ❓ Technology choice unclear?
- ❓ Multiple valid approaches?
- ❓ Risky action? (Force push, delete, deploy)
- ❓ Breaking change?
- ❓ Architecture decision?

## ✅ When I Can Decide

- ✅ Bug fix (clear fix)
- ✅ Add test (matches pattern)
- ✅ Refactor (no behavior change)
- ✅ Update docs
- ✅ Add feature (clear spec)

---

## 🔍 Pre-Commit Checklist

- [ ] TypeScript compiles (`tsc --noEmit`)
- [ ] Linter passes (`npm run lint` or similar)
- [ ] Tests pass (`npm run test`)
- [ ] [XX]%+ coverage (`npm run test:coverage`)
- [ ] No console.log
- [ ] No hardcoded secrets
- [ ] [Your validator] validation on inputs
- [ ] Error handling in try/catch
- [ ] No mutation
- [ ] No `any` types
- [ ] Conventional commit message

---

## 🔗 Related Files
- [MEMORY.md](./MEMORY.md) - Project context
- [CODEMAP.md](./CODEMAP.md) - Codebase architecture
- [README.md](./README.md) - Setup instructions
```

**Time to fill this in: 5-10 minutes**

---

### PHASE 3: Generate CODEMAP.md (10-15 min)

Map your actual codebase architecture.

#### Step 3.1: Directory Mapping

For each important directory, document it:

```markdown
# CODEMAP.md - Codebase Architecture Map

**Generated**: [today's date]
**Version**: 1.0

---

## 📊 Project Overview

```
[your project structure visual]
```

---

## 🗂️ Directory Structure

### `/src/server.ts` - Express App Setup
**Purpose**: Initialize Express, register middleware, start server
**Lines**: [count actual lines]
**Key Functions**: [list actual functions]

**Dependencies**: [what does it import?]

**Code snippet**:
```typescript
[show relevant code]
```

---

### `/src/api/` - REST API Routes
**Purpose**: [describe what you use this for]

**Structure**:
```
api/
├── [feature1]/
│   ├── routes.ts       ← Route definitions
│   ├── controller.ts   ← Request handlers
│   └── schema.ts       ← validation schemas
├── [feature2]/
│   └── ...
```

**Pattern**:
[describe how you organize API endpoints]

**Examples**:
- `/users` - [what endpoints?]
- `/auth` - [what endpoints?]
- `/[other features]` - [what endpoints?]

---

### `/src/services/` - Business Logic
**Purpose**: Service layer between controller and repository

**Files**: [list actual services in your project]
- `UserService.ts` - [what does it do?]
- `AuthService.ts` - [what does it do?]
- [others...]

**Pattern**:
[describe how services are structured]

**Example**:
```typescript
[show real service method]
```

---

### `/src/models/` - Database Models & Types
**Purpose**: TypeScript interfaces and zod schemas

**Files**:
- `User.ts` - [type definitions]
- `Post.ts` - [type definitions]
- `schemas.ts` - [zod schemas]

**Example**:
```typescript
[show real model definition]
```

---

### `/src/middleware/` - Express Middleware
**Purpose**: Request processing before handlers

**Files**:
| File | Purpose |
|------|---------|
| `auth.ts` | [what does it do?] |
| `errorHandler.ts` | [what does it do?] |
| `validation.ts` | [what does it do?] |
| `logger.ts` | [what does it do?] |
| `cors.ts` | [what does it do?] |

**Usage example**:
```typescript
[show how middleware is used in routes]
```

---

### `/src/utils/` - Helper Functions
**Purpose**: Shared utilities

**Files**:
| File | Purpose | Key Functions |
|------|---------|---|
| `logger.ts` | [purpose] | [functions] |
| `errors.ts` | [purpose] | [functions] |
| `db.ts` | [purpose] | [functions] |

---

### `/src/types/` - TypeScript Definitions
**Purpose**: Shared type definitions

**Files**:
- `index.ts` - [what types?]
- `express.d.ts` - [what extensions?]
- `api.ts` - [what response types?]

---

### `/tests` - Test Files

#### Unit Tests (`src/**/__tests__/`)
**Purpose**: Test individual functions/methods
**Location**: [actual location]
**Pattern**: [how you structure unit tests]

#### Integration Tests (`tests/integration/`)
**Purpose**: Test API endpoints with database
**Location**: [actual location]
**Pattern**: [how you structure integration tests]

#### E2E Tests (`tests/e2e/`)
**Purpose**: Test complete user journeys
**Location**: [actual location or "Not implemented"]
**Pattern**: [how you structure E2E tests]

---

## 🔄 Request Flow

Document how a real request flows through your system:

```
1. Client: POST /api/[endpoint] { ... }

2. Middleware Chain:
   ├─ [middleware1] → [what it does]
   ├─ [middleware2] → [what it does]
   ├─ [middleware3] → [what it does]
   └─ [middleware4] → [what it does]

3. Route Handler
   └─ Matches route and calls controller

4. Controller
   ├─ Extracts/validates request data
   └─ Calls service

5. Service
   ├─ Applies business logic
   └─ Calls repository/database

6. Repository
   └─ Executes database query

7. Response
   └─ Returns to client
```

---

## 📦 Key Dependencies

| Package | Version | Purpose |
|---------|---------|---------|
| [list from package.json] |

---

## 🎯 File Purpose Quick Reference

| File Path | Purpose | Lines | Key Functions |
|-----------|---------|-------|---|
| [list actual files with their purposes] |

---

## 🔍 How to Navigate

**Want to add new endpoint?**
1. Read: `src/api/[similar-feature]/routes.ts` (pattern)
2. Check: `src/api/[similar-feature]/schema.ts` (validation)
3. Create: New files following same pattern

**Want to understand flow?**
1. Start: `src/server.ts` (entry point)
2. Then: `src/api/index.ts` (route registration)
3. Then: Specific feature routes/controller/service

**Want to debug error?**
1. Check: `src/middleware/errorHandler.ts` (error catch)
2. Check: `src/utils/errors.ts` (error definitions)
3. Grep: Search for where error is thrown

**Want to run tests?**
[Show actual npm scripts you have]
- Unit: `npm run test:unit`
- Integration: `npm run test:integration`
- E2E: `npm run test:e2e`
- Coverage: `npm run test:coverage`

---

## 📊 Architecture Diagram

[Create ASCII art showing your architecture]

```
[paste your architecture diagram]
```

---

## 📝 Notes

- Update when structure changes
- Keep in sync with actual code
```

**Time to fill this in: 10-15 minutes**

---

### PHASE 4: Generate MEMORY.md (10-15 min)

Document project context and gotchas.

#### Template:

```markdown
# MEMORY.md - Project Context & Knowledge Base

**Last Updated**: [today's date]
**Updated By**: [your name]

---

## 🎯 Quick Facts

| Aspect | Details |
|--------|---------|
| **Project** | [your project name] |
| **Purpose** | [what it does] |
| **Tech** | Node.js + TypeScript + [your stack] |
| **Main Pain Point** | [from Step 1.5] |
| **Auth Type** | [JWT/Session/OAuth/None] |
| **Database** | [PostgreSQL/MongoDB/etc] v[XX] |
| **Cache** | [Redis/In-memory/None] |
| **Logging** | [Winston/Pino/Bunyan] |
| **Deployment** | [Docker/AWS/Vercel/etc] |

---

## 🏗️ Architecture Overview

[Your architecture diagram from CODEMAP]

---

## 📁 Key Files Quick Reference

| File | Purpose | Last Modified |
|------|---------|---|
| `src/server.ts` | [purpose] | [date] |
| `src/api/index.ts` | [purpose] | [date] |
| [list other important files] |

---

## 🔑 Important Conventions

### 1. **Validation Pattern**
[Show real code example from your project]

### 2. **Error Handling Pattern**
[Show real code example from your project]

### 3. **Service Layer Pattern**
[Show real code example from your project]

### 4. **Repository Pattern** (DB Access)
[Show real code example from your project]

### 5. **API Response Wrapper**
[Show real code example from your project]

### 6. **Logging Pattern**
[Show real code example from your project]

---

## 🚨 Known Gotchas

[From Step 1.5, document each issue]

### 1. **[Issue Name]**
**Issue**: [What goes wrong?]
**Solution**: [How to fix it]
**File**: [Where to look]

### 2. **[Issue Name]**
**Issue**: [What goes wrong?]
**Solution**: [How to fix it]
**File**: [Where to look]

---

## 🔄 Recent Changes & Context

### [Date] - [Feature/Change]
- **What changed**: [Description]
- **Files affected**: [list files]
- **Breaking**: Yes/No
- **Context**: [Why this changed]

---

## 📊 Performance Notes

### Slow Endpoints
| Endpoint | Issue | Fix |
|----------|-------|-----|
| [document any slow endpoints] |

### Optimization Opportunities
- [ ] [opportunity 1]
- [ ] [opportunity 2]
- [ ] [opportunity 3]

---

## 🔐 Security Checkpoints

- [x] No hardcoded secrets (using .env)
- [x] Input validation with [your validator]
- [x] JWT token validation
- [x] Rate limiting enabled
- [x] CORS configured
- [ ] [add more as needed]

---

## 🧪 Testing Patterns

### Unit Tests
Location: `src/services/__tests__/[Service].test.ts`
Pattern: [describe pattern]

### Integration Tests
Location: `tests/integration/[feature].test.ts`
Pattern: [describe pattern]

### E2E Tests
Location: `tests/e2e/[flow].test.ts`
Pattern: [or "Not implemented"]

---

## 📚 References

- [CLAUDE.md](./CLAUDE.md) - Project rules
- [CODEMAP.md](./CODEMAP.md) - Codebase structure
- [README.md](./README.md) - Setup & how to run
- Database Schema: [/migrations](./migrations/)

---

## 💡 Tips for Future Changes

1. **New Database Column?** → Create migration, update model
2. **New Validation Rule?** → Update [your validator] schema
3. **New Error Type?** → Add to [your error file]
4. **New API Endpoint?** → Follow existing pattern [reference pattern]
5. **Slow Query?** → Check indexes, add eager loading, implement pagination
```

**Time to fill this in: 10-15 minutes**

---

## 📊 Checklist: All Files Complete

After completing all 4 phases:

- [ ] **CLAUDE.md** created with:
  - [ ] Project overview & tech stack
  - [ ] Critical rules (code quality, validation, error handling, logging)
  - [ ] Testing requirements & security rules
  - [ ] Project structure
  - [ ] How to add features (with real code examples)
  - [ ] Pre-commit checklist

- [ ] **CODEMAP.md** created with:
  - [ ] Directory structure mapped
  - [ ] Each folder documented with purpose
  - [ ] Request flow documented
  - [ ] Key dependencies listed
  - [ ] File quick reference table
  - [ ] Navigation guide

- [ ] **MEMORY.md** created with:
  - [ ] Quick facts table
  - [ ] Architecture overview
  - [ ] Key files reference
  - [ ] Important conventions with code examples
  - [ ] Known gotchas documented
  - [ ] Performance notes
  - [ ] Security checklist

---

## ✨ Final Quality Check

Review your generated files:

```markdown
## CLAUDE.md Check
- [ ] No placeholder values like [XX]
- [ ] Real file paths, not generic ones
- [ ] Code examples from actual codebase
- [ ] Specific rules, not generic rules

## CODEMAP.md Check
- [ ] Real file locations documented
- [ ] Actual function names listed
- [ ] Real code examples included
- [ ] Request flow based on actual middleware
- [ ] Navigation paths reflect actual structure

## MEMORY.md Check
- [ ] Actual gotchas from this project
- [ ] Real conventions with code examples
- [ ] Performance issues specific to your setup
- [ ] Security measures actually implemented
- [ ] Testing patterns you actually use
```

---

## 🎉 You're Done!

Your project now has:
✅ CLAUDE.md - Project constitution
✅ CODEMAP.md - Architecture map
✅ MEMORY.md - Context & gotchas

Use these in Claude requests:
```
"See CLAUDE.md, CODEMAP.md, and MEMORY.md for context"
```

Total time invested: ~45-60 minutes
Time saved in future AI assistance: Hundreds of hours!

---

**Last Updated**: February 2026
**Version**: 1.0
