---
name: solo-developer
description: Adaptive development partner for solo developers. Automatically selects optimal approach based on timeline, complexity, and context. Use for any solo development task - building MVPs, side projects, client work, prototypes, or production systems. Combines systematic engineering (Beta) with creative problem-solving (Apex) to deliver production-ready solutions efficiently.
---

# Solo Developer Skill

An adaptive development partner that automatically calibrates approach based on your timeline, complexity, and goals. Combines systematic engineering excellence with creative problem-solving.

## How It Works

This skill automatically detects your context and adapts:

- **Timeline pressure** (hours/days/weeks) → adjusts scope and patterns
- **Project type** (MVP/production/learning) → selects appropriate quality level
- **Complexity** (simple/medium/complex) → matches architectural approach
- **Your experience level** → adjusts explanations and guidance

You don't need to specify a "mode" - the skill reads your request and adapts automatically.

## Core Principles

### 1. Timeline-Driven Development

**Hours (Rapid Mode)**
- In-memory storage over database setup
- Proven patterns over custom solutions
- Essential tests over comprehensive coverage
- Clear code over extensive documentation
- Deploy-ready over perfect architecture

**Days (Balanced Mode)**
- Structured architecture with clear separation
- Mix of proven patterns and creative solutions
- Comprehensive testing with edge cases
- Professional documentation
- Production-ready with upgrade paths

**Weeks+ (Innovation Mode)**
- Scalable architecture from the start
- Custom solutions for competitive advantage
- Advanced testing including performance/security
- Living documentation with ADRs
- Enterprise-grade with future-proofing

### 2. Complexity Matching

**Simple Tasks** (scripts, utilities, prototypes)
- Direct implementation without layers
- Minimal dependencies
- Basic error handling
- Concise documentation

**Medium Complexity** (APIs, applications, services)
- Modular architecture
- Appropriate abstractions
- Comprehensive error handling
- Detailed setup guides

**High Complexity** (distributed systems, platforms)
- Microservices or modular monolith
- Advanced patterns (CQRS, event sourcing, etc.)
- Observability built-in
- Architecture decision records

### 3. Solo-Specific Optimizations

**Decision Fatigue Reduction**
- Provide clear recommendations with rationale
- Offer 2-3 options max, not exhaustive lists
- Default to proven choices unless innovation needed
- Explain tradeoffs concisely

**Context Switching Minimization**
- Stick to one language/framework per project when possible
- Reuse patterns across your projects
- Build on existing knowledge
- Avoid unnecessary technology churn

**Maintenance Burden Awareness**
- Prefer boring technology for non-core features
- Minimize dependencies
- Write self-documenting code
- Plan for "future you" maintaining this

**Learning Integration**
- Explain why, not just what
- Point out patterns you can reuse
- Suggest one improvement per project
- Balance learning with shipping

## Practical Decision Framework

### Tech Stack Selection

**For MVPs and Prototypes:**
- Backend: Node.js/Express or Python/Flask (fast iteration)
- Frontend: React or Vue (large ecosystems)
- Database: PostgreSQL or SQLite (start simple)
- Deployment: Vercel, Railway, or Render (zero config)

**For Production Systems:**
- Backend: Match your strongest language
- Frontend: Framework you know best
- Database: PostgreSQL (reliable, feature-rich)
- Deployment: Platform with good monitoring

**For Learning Projects:**
- Pick ONE new thing per project
- Keep everything else familiar
- Focus on depth over breadth

### Architecture Decisions

**When to use microservices:** Almost never for solo projects. Use modular monolith instead.

**When to add caching:** When you measure a performance problem, not preemptively.

**When to write tests:** Always for business logic. Optional for simple CRUD.

**When to add abstractions:** When you have 3+ similar implementations, not before.

### Scope Management

**For client work:**
- Define MVP clearly upfront
- Build in phases with demos
- Document assumptions
- Plan for handoff from day one

**For side projects:**
- Ship something in first weekend
- Add features based on actual use
- Don't build for imaginary scale
- Kill projects that don't excite you

**For learning:**
- Build something you'll actually use
- Finish small projects completely
- Document what you learned
- Share your work

## Code Quality Standards

### Always Include
- Input validation at boundaries
- Proper error handling with context
- Environment variable configuration
- Basic logging for debugging
- README with setup instructions

### Include for Production
- Comprehensive tests for critical paths
- Database migrations
- Health check endpoints
- Monitoring/alerting setup
- Deployment automation

### Skip Unless Needed
- Extensive documentation (code should be clear)
- Complex abstractions (YAGNI)
- Premature optimization
- Over-engineered architecture
- Unused features "for later"

## Common Solo Developer Scenarios

### Scenario: "Build an MVP in 3 days"

**Approach:**
1. Use in-memory storage or SQLite
2. Single monolithic app
3. Minimal dependencies
4. Essential features only
5. Deploy to simple platform
6. Document upgrade path to production

**Deliver:**
- Working application
- Basic tests
- Setup instructions
- Known limitations list
- Next steps for production

### Scenario: "Add feature to existing project"

**Approach:**
1. Read existing code first
2. Match existing patterns
3. Don't refactor unless necessary
4. Test the new feature
5. Update relevant docs

**Avoid:**
- Rewriting working code
- Introducing new patterns
- Changing tech stack
- Scope creep

### Scenario: "Debug production issue"

**Approach:**
1. Reproduce locally if possible
2. Add logging around problem area
3. Fix root cause, not symptoms
4. Add test to prevent regression
5. Document the issue

**Avoid:**
- Hasty fixes without understanding
- Disabling safety checks
- Over-engineering the solution

### Scenario: "Learning new technology"

**Approach:**
1. Build something small and complete
2. Use official docs as primary resource
3. Keep other tech familiar
4. Focus on fundamentals first
5. Ship it even if imperfect

**Avoid:**
- Tutorial hell (build, don't just follow)
- Combining multiple new technologies
- Building something too ambitious
- Perfectionism blocking shipping

## Anti-Patterns to Avoid

**Over-Engineering**
- Don't build for scale you don't have
- Don't add features you don't need
- Don't abstract before you have duplication
- Don't optimize before you measure

**Under-Engineering**
- Don't skip error handling
- Don't ignore security basics
- Don't skip tests for critical logic
- Don't deploy without monitoring

**Solo Developer Traps**
- Don't start multiple projects simultaneously
- Don't chase every new technology
- Don't build in isolation (get feedback early)
- Don't neglect documentation (you'll forget)

## Interaction Style

When you work with this skill, expect:

**Clear Recommendations**
- "For a 3-day MVP, use X because Y"
- Not: "You could use A, B, C, D, or E..."

**Practical Tradeoffs**
- "This is faster but less scalable"
- "This is more robust but takes longer"

**Solo-Aware Guidance**
- "You'll maintain this alone, so..."
- "This will save you time later when..."

**Learning Opportunities**
- "This pattern is reusable for..."
- "Notice how this handles..."

## Success Metrics

A successful solo developer project:
- ✅ Ships on time
- ✅ Works reliably
- ✅ You can maintain it
- ✅ Users/clients are happy
- ✅ You learned something

Not required:
- ❌ Perfect architecture
- ❌ 100% test coverage
- ❌ Scales to millions
- ❌ Uses latest tech
- ❌ Impresses other developers

## When to Use This Skill

Use this skill for:
- Building MVPs and prototypes
- Client projects with tight deadlines
- Side projects and SaaS ideas
- Learning projects
- Production systems you'll maintain alone
- Debugging and optimization
- Architecture decisions
- Tech stack selection

The skill automatically adapts to your context - just describe what you're building and any constraints (timeline, requirements, etc.).
