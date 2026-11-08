# Language-Specific Guide

This skill supports **any backend language**. Here's how to adapt the prompts for your specific tech stack.

---

## 🎯 Supported Languages

- ✅ JavaScript / Node.js
- ✅ Python
- ✅ Go
- ✅ Java
- ✅ C# / .NET
- ✅ Ruby
- ✅ PHP
- ✅ Other languages (with adaptation)

---

## 🔄 How to Adapt Prompts

The prompts in `QUICK_START_PROMPTS.md` are **language-agnostic**. Simply replace framework/tool names with your tech stack:

### Template for Adaptation

```markdown
# Replace These Frameworks

Node.js/Express     →  Your Framework
TypeScript          →  Your Language
Zod                 →  Your Validation
Jest                →  Your Test Framework
PostgreSQL          →  Your Database
Prisma              →  Your ORM
Winston             →  Your Logger
```

---

## 📋 Language-Specific Mappings

### JavaScript / Node.js ✅

**Fully supported with:**
- Express, Fastify, NestJS, Koa
- Jest, Vitest, Mocha
- Zod, class-validator
- PostgreSQL, MongoDB, MySQL
- Winston, Pino

**Use**: QUICK_START_PROMPTS.md as-is

---

### Python 🐍

**Replace in prompts:**

| Original | Python |
|----------|--------|
| Express / NestJS | Django / FastAPI / Flask |
| TypeScript | Python (type hints) |
| Zod | Pydantic / dataclasses |
| Jest | pytest |
| PostgreSQL | PostgreSQL / MySQL |
| Prisma | SQLAlchemy / Django ORM |
| Winston | logging / structlog |
| Middleware | middleware / decorators |
| Controllers | views / route handlers |

**Example Adaptation:**
```markdown
# Phase 1: Replace these

Framework: Django/FastAPI (instead of Express)
Language: Python (instead of TypeScript)
Validation: Pydantic (instead of Zod)
Testing: pytest (instead of Jest)
Logging: structlog (instead of Winston)

# Then use QUICK_START_PROMPTS.md
# Claude will understand Python context
```

**Key Frameworks:**
- **Django**: Full-featured, batteries included
- **FastAPI**: Modern, async-first, REST-focused
- **Flask**: Lightweight, minimal
- **Starlette**: ASGI framework, async

---

### Go 🐹

**Replace in prompts:**

| Original | Go |
|----------|---|
| Express | Gin / Echo / Chi |
| TypeScript | Go (static types) |
| Zod | Built-in validation / validator |
| Jest | testing package / Testify |
| PostgreSQL | PostgreSQL / MySQL |
| Prisma | GORM / Ent |
| Winston | logrus / zap |
| Middleware | middleware / handlers |
| Decorators | struct tags |

**Example Adaptation:**
```markdown
# Phase 1: Replace these

Framework: Gin/Echo (instead of Express)
Language: Go (instead of TypeScript)
Validation: Go struct tags / validator (instead of Zod)
Testing: Testify/testing (instead of Jest)
Logging: logrus (instead of Winston)
Router: Gin/Echo (instead of Express Router)

# Then use QUICK_START_PROMPTS.md
# Claude will understand Go context
```

**Key Frameworks:**
- **Gin**: High-performance, fast routing
- **Echo**: Fast, extensible framework
- **Chi**: Lightweight, composable routing
- **Fiber**: Express-like API, high performance

---

### Java (Spring Boot) ☕

**Replace in prompts:**

| Original | Spring Boot |
|----------|------------|
| Express | Spring Boot |
| TypeScript | Java (static types) |
| Zod | Bean Validation / Jakarta Validation |
| Jest | JUnit 5 / Mockito |
| PostgreSQL | PostgreSQL / MySQL |
| Prisma | JPA / Hibernate |
| Winston | Logback / Log4j |
| Middleware | Filters / Interceptors |
| Controllers | @RestController |

**Example Adaptation:**
```markdown
Framework: Spring Boot
Language: Java
Validation: Jakarta Bean Validation
Testing: JUnit 5 + Mockito
Database: JPA / Hibernate
Logging: Logback
```

---

### C# / .NET 🔷

**Replace in prompts:**

| Original | .NET |
|----------|------|
| Express | ASP.NET Core |
| TypeScript | C# (static types) |
| Zod | DataAnnotations / FluentValidation |
| Jest | xUnit / NUnit / Moq |
| PostgreSQL | SQL Server / PostgreSQL |
| Prisma | Entity Framework / Dapper |
| Winston | Serilog / NLog |
| Middleware | Custom Middleware |
| Controllers | ApiController |

**Example Adaptation:**
```markdown
Framework: ASP.NET Core
Language: C#
Validation: FluentValidation
Testing: xUnit + Moq
Database: Entity Framework Core
Logging: Serilog
```

---

## 🚀 Step-by-Step Adaptation

### Step 1: Identify Your Tech Stack

```markdown
Framework: [Your framework - e.g., FastAPI, Gin, Spring Boot]
Language: [Your language - e.g., Python, Go, Java]
Database: [e.g., PostgreSQL, MySQL]
Testing: [e.g., pytest, Testify, JUnit]
ORM/Query Builder: [e.g., SQLAlchemy, GORM, Hibernate]
Logger: [e.g., structlog, logrus, Logback]
```

### Step 2: Open QUICK_START_PROMPTS.md

Copy the Phase 1 prompt

### Step 3: Replace Framework Names

```markdown
# ORIGINAL (Node.js)
- Framework: Express / NestJS
- Language: TypeScript
- Testing: Jest
- Validation: Zod

# YOUR STACK (e.g., Python)
- Framework: FastAPI
- Language: Python
- Testing: pytest
- Validation: Pydantic
```

### Step 4: Ask Claude Phase 1 Prompt

```markdown
Analyze my [FRAMEWORK] [LANGUAGE] repository and answer these questions:

[Paste adapted Phase 1 prompt with YOUR frameworks]

Additional context:
- Framework: FastAPI (not Express)
- Language: Python (not TypeScript)
- Database: PostgreSQL
- Testing: pytest (not Jest)
- Validation: Pydantic (not Zod)
```

### Step 5: Use Phase 2-4 Prompts

Use the same adaptation pattern for Phase 2, 3, 4 prompts.

---

## 📝 Quick Reference Table

### Popular Framework Combinations

```markdown
# Node.js
Express + TypeScript + Jest + PostgreSQL + Zod

# Python (Django)
Django + Python + pytest + PostgreSQL + Pydantic

# Python (FastAPI)
FastAPI + Python + pytest + PostgreSQL + Pydantic

# Go
Gin + Go + Testify + PostgreSQL + validator

# Go (Echo)
Echo + Go + testing + PostgreSQL + validator

# Java
Spring Boot + Java + JUnit 5 + PostgreSQL + Validation API

# C#
ASP.NET Core + C# + xUnit + SQL Server + FluentValidation

# Ruby
Rails + Ruby + RSpec + PostgreSQL + ActiveModel
```

---

## 💡 Tips for Language-Specific Adaptation

### Python-Specific
- Mention **Django ORM** vs **SQLAlchemy** (affects query patterns)
- Ask about **async** vs **sync** (FastAPI is async-first)
- Note: Python uses **decorators** instead of annotations
- Validation: **Pydantic v1** vs **v2** syntax differs

### Go-Specific
- Go is **compiled** & **statically typed** (different deployment)
- **go mod** for dependency management (not npm/pip)
- **interfaces** instead of inheritance
- **goroutines** for concurrency (unique to Go)
- No built-in validation library (use third-party)

### Java-Specific
- **Annotations** (@RequestMapping, @Service, @Autowired)
- **Dependency Injection** central to Spring
- **JPA/Hibernate** for ORM (different from Prisma)
- **Spring profiles** for environment config
- **Maven** or **Gradle** for builds (not npm)

### C#-Specific
- **async/await** built-in and widely used
- **Dependency Injection** in .NET Core
- **Entity Framework** is the standard ORM
- **NuGet** for package management
- **appsettings.json** for configuration

---

## 🎯 When Prompts Are Language-Agnostic

The prompts work well across languages for:

✅ **Architecture topics**
- Request flow diagrams
- Service layer patterns
- Directory structure
- Middleware concepts

✅ **General practices**
- Error handling patterns
- Validation approach
- Logging strategy
- Testing methodology

❌ **Language-Specific topics**
- Syntax examples (adapt these)
- Framework-specific decorators/annotations
- Package manager commands
- Language-specific gotchas

---

## 📚 Additional Resources

For language-specific patterns, check:

- **Python**: Django/FastAPI documentation
- **Go**: Go best practices guide
- **Java**: Spring Boot documentation
- **C#**: Microsoft .NET documentation
- **Others**: Official framework docs

---

## 🔗 Example: Full Python Adaptation

Here's how to fully adapt for a **FastAPI + Python + PostgreSQL** project:

### Original Phase 1 Prompt (Node.js)
```markdown
## Technology Stack

**Framework**: Express/Fastify/NestJS
**Language**: TypeScript
**Database**: PostgreSQL/MongoDB
**Testing**: Jest/Vitest
```

### Adapted Phase 1 Prompt (Python)
```markdown
## Technology Stack

**Framework**: FastAPI (modern Python web framework)
**Language**: Python (with type hints)
**Database**: PostgreSQL
**Testing**: pytest (Python's standard testing tool)
**Validation**: Pydantic (Python's validation library)
**Async**: Yes (FastAPI uses async/await)
```

Then continue with the prompt, and Claude will generate Python/FastAPI-specific CLAUDE.md, CODEMAP.md, MEMORY.md!

---

## ❓ Frequently Asked Questions

**Q: Will the quality be the same for Python/Go?**
A: Yes! The approach is language-agnostic. Just replace framework names accurately.

**Q: What if I can't find exact equivalent frameworks?**
A: Describe your framework and ask Claude in Phase 1 - Claude can adapt.

**Q: Should I mention language in prompts?**
A: Yes, be explicit: "I'm using FastAPI (Python framework)" not just "Express".

**Q: Can I mix languages in one project?**
A: Yes - document each component separately or ask Claude for multi-language guidance.

---

**Last Updated**: February 2026
**Status**: Ready for any language ✅
