# Reusability Patterns

Patterns for creating adaptable skills that handle variations across requirements.

---

## Skills = Procedural Knowledge + Domain Expertise

Every production-grade skill encodes TWO types of knowledge:

### Procedural Knowledge (HOW)
Step-by-step processes, decision trees, workflows that guide execution.

| Examples |
|----------|
| "First validate input, then process, then verify output" |
| "If authentication fails, retry with backoff, then prompt for credentials" |
| "Check for null → validate format → transform → return" |

### Domain Expertise (WHAT)
Concepts, best practices, patterns, anti-patterns specific to the domain.

| Examples |
|----------|
| "WCAG AA requires 4.5:1 contrast ratio for text" |
| "React components should be pure functions" |
| "API rate limits are typically 1000 req/min" |

### How They Work Together

```
User Request
     │
     ▼
┌─────────────────────────────────┐
│ Domain Expertise (WHAT)         │
│ - Understand the domain         │
│ - Apply best practices          │
│ - Avoid anti-patterns           │
└─────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────┐
│ Procedural Knowledge (HOW)      │
│ - Follow step-by-step workflow  │
│ - Make decisions at branches    │
│ - Handle errors appropriately   │
└─────────────────────────────────┘
     │
     ▼
Quality Output
```

### Encoding in Skills (Embedded, Not Discovered at Runtime)

| Knowledge Type | Where to Embed |
|----------------|----------------|
| Procedural (workflows) | SKILL.md main sections |
| Domain expertise | `references/` (structured per domain needs) |
| Complex procedures | `scripts/` for executable code |
| Templates | `assets/` for boilerplate |

**What goes in references/**:
- Library/API documentation
- Best practices
- Code examples
- Patterns and anti-patterns
- Domain-specific details

**Key**: Domain expertise is EMBEDDED during skill creation. Generated skills are zero-shot experts. Structure `references/` based on what the domain needs.

---

## Core Concept: Varies vs Constant

Every domain has elements that VARY across use cases and elements that remain CONSTANT.

**Skills encode the CONSTANT patterns and ask clarifying questions for what VARIES.**

---

## Domain Analysis Pattern

Before creating a skill, analyze the domain:

| Question | Purpose |
|----------|---------|
| What changes between use cases? | Identify clarification questions needed |
| What stays the same? | Identify patterns to encode in skill |
| What are the common variations? | Identify options to present |
| What are the boundaries? | Identify scope (does/does not do) |

---

## Examples by Domain

### Visualization Skills

| Varies | Constant |
|--------|----------|
| Data shape/structure | Rendering lifecycle |
| Chart type (bar, line, pie) | Accessibility requirements |
| Library (Recharts, D3, Chart.js) | Responsive patterns |
| Color scheme | Loading/error states |
| Interactivity level | Data validation |

**Skill should**: Ask for data shape, chart type, library preference
**Skill should NOT**: Hardcode specific data fields or single chart type

### Web Framework Skills (Next.js, React, etc.)

| Varies | Constant |
|--------|----------|
| Database (Postgres, MongoDB, Prisma) | Project structure patterns |
| CSS framework (Tailwind, CSS Modules) | Component architecture |
| Auth provider (NextAuth, Clerk) | Error handling patterns |
| Deployment target (Vercel, AWS) | Performance best practices |
| Features (specific pages, APIs) | Security patterns |

**Skill should**: Ask for tech stack preferences, feature requirements
**Skill should NOT**: Hardcode database schema or specific routes

### Deployment Skills

| Varies | Constant |
|--------|----------|
| Platform (AWS, GCP, Azure) | CI/CD principles |
| Orchestration (Kubernetes, ECS, serverless) | Rollback strategies |
| Configuration (Helm, Terraform, CDK) | Health check patterns |
| Environment (dev, staging, prod) | Secret management principles |
| Scale requirements | Monitoring patterns |

**Skill should**: Ask for platform, orchestration preference, environment
**Skill should NOT**: Hardcode specific cloud resources or configs

### API Integration Skills

| Varies | Constant |
|--------|----------|
| Endpoint URLs | Error handling patterns |
| Authentication method | Retry with backoff |
| Request/response shape | Rate limiting handling |
| Third-party service | Timeout management |
| Rate limits | Response validation |

**Skill should**: Ask for API details, auth method
**Skill should NOT**: Hardcode specific API endpoints

### Data Processing Skills

| Varies | Constant |
|--------|----------|
| Input format (CSV, JSON, XML) | Validation patterns |
| Output format | Error recovery |
| Transformation rules | Streaming for large files |
| Data schema | Progress reporting |
| Volume/scale | Cleanup procedures |

**Skill should**: Ask for input/output formats, transformation needs
**Skill should NOT**: Hardcode specific field names or schemas

---

## Abstraction Levels

### Level 1: Domain-Agnostic (Highest Reuse)

Skills that work across many domains:
- Error handling patterns
- Logging and monitoring
- Testing strategies
- Documentation generation

### Level 2: Domain-Specific, Tool-Agnostic (High Reuse)

Skills that work within a domain but across tools:
- "Visualization" (not "Recharts visualization")
- "Deployment" (not "Kubernetes deployment")
- "API integration" (not "Stripe integration")

### Level 3: Tool-Specific (Moderate Reuse)

Skills for specific tools but adaptable workflows:
- "Next.js applications" (adaptable to different features)
- "PostgreSQL databases" (adaptable to different schemas)

### Level 4: Requirement-Specific (Avoid)

Skills tied to single requirements:
- "Sales dashboard with bar chart" - TOO SPECIFIC
- "User auth with email/password" - TOO SPECIFIC

---

## Clarification Questions for Reusability

Structure questions to capture variations:

```markdown
## Required Clarifications

1. **[Variable Element]**: "What [element] will you use?"
   - Option A → implications
   - Option B → implications
   - Other → ask for details

2. **[Another Variable]**: "What are your requirements for [aspect]?"
```

### Good Examples

```markdown
## Required Clarifications

1. **Data source**: "What shape will the input data have?"
   - Provide example structure

2. **Output format**: "What type of visualization?"
   - Chart (bar, line, pie, etc.)
   - Table
   - Dashboard
   - Other

3. **Library preference**: "Any preferred visualization library?"
   - Recharts (React)
   - D3.js (vanilla)
   - Chart.js
   - No preference (recommend based on use case)
```

### Bad Examples (Too Specific)

```markdown
## This skill creates:
- A bar chart showing monthly sales
- Using Recharts
- With blue color scheme
```

---

## Reusability Checklist

Before finalizing a skill, verify:

### Scope
- [ ] Does NOT hardcode specific data fields/schemas
- [ ] Does NOT hardcode specific tool/library (unless tool-specific skill)
- [ ] Does NOT hardcode specific configurations
- [ ] DOES handle common variations via clarifications

### Clarifications
- [ ] Asks for variable elements (data shape, tool preference, etc.)
- [ ] Provides reasonable options for common choices
- [ ] Allows "other" for uncommon variations

### Patterns
- [ ] Encodes CONSTANT domain patterns (best practices, error handling)
- [ ] Separates concerns (what varies vs what's constant)
- [ ] Works for multiple use cases within the domain

### Boundaries
- [ ] Clear scope (what it does / does not do)
- [ ] Explicit about abstraction level (domain vs tool-specific)

---

## Anti-Patterns

### Hardcoded Specifics

```markdown
# Bad: Hardcoded data fields
The widget displays:
- product.name
- product.price
- product.quantity
```

```markdown
# Good: Adaptable to data shape
Ask for data structure, then map fields dynamically.
```

### Single Tool Lock-in (when domain-level skill)

```markdown
# Bad: Tool lock-in for domain skill
This visualization skill uses Recharts exclusively.
```

```markdown
# Good: Tool-agnostic with preference
Ask for library preference. Support Recharts, D3, Chart.js, or recommend based on use case.
```

### Feature Enumeration

```markdown
# Bad: Listing specific features
Creates:
- Login page
- Dashboard
- Settings page
```

```markdown
# Good: Feature categories
Ask what features are needed. Provide patterns for:
- Authentication flows
- Data display pages
- Configuration interfaces
```
