---
name: "senior-fullstack"
description: Fullstack development toolkit with project scaffolding for Next.js, FastAPI, MERN, and Django stacks, code quality analysis with security and complexity scoring, and stack selection guidance. Use when the user asks to "scaffold a new project", "create a Next.js app", "set up FastAPI with React", "analyze code quality", "audit my codebase", "what stack should I use", "generate project boilerplate", or mentions fullstack development, project setup, or tech stack comparison.
---

# Senior Fullstack

Fullstack development skill with project scaffolding and code quality analysis tools.

---

## Table of Contents

- [Trigger Phrases](#trigger-phrases)
- [Tools](#tools)
- [Workflows](#workflows)
- [Reference Guides](#reference-guides)

---

## Trigger Phrases

Use this skill when you hear:
- "scaffold a new project"
- "create a Next.js app"
- "set up FastAPI with React"
- "analyze code quality"
- "check for security issues in codebase"
- "what stack should I use"
- "set up a fullstack project"
- "generate project boilerplate"

---

## Tools

### Decision Engine

Deterministic profile picker. Given four assumptions (team-size, cadence, user-facing, budget) plus optional traffic/sensitivity inputs, ranks the four built-in profiles and returns the matched profile with SLO floor and named approver chain. Refuses to recommend a profile without the four required inputs.

**Usage:**

```bash
# See all options
python scripts/fullstack_decision_engine.py --help

# Run against a sample input
python scripts/fullstack_decision_engine.py --sample

# Pick a profile from real inputs
python scripts/fullstack_decision_engine.py \
    --team-size-12mo 8 --cadence daily --user-facing true --budget 5000 \
    --traffic-p99-rps 50 --data-sensitivity pii-only

# JSON output for downstream tools
python scripts/fullstack_decision_engine.py --sample --output json
```

Returns: matched profile name, score, matched/violated constraints, stack recommendation, anti-recommendations, SLO floor, named-approver chain, and canon references.

The engine encodes the same matrix the conversational grill walks through — use it directly when inputs are already known, or via the `cs-fullstack-engineer` agent for the question-by-question grill.

---

### Project Scaffolder

Generates fullstack project structures with boilerplate code.

**Supported Templates:**
- `nextjs` - Next.js 14+ with App Router, TypeScript, Tailwind CSS
- `fastapi-react` - FastAPI backend + React frontend + PostgreSQL
- `mern` - MongoDB, Express, React, Node.js with TypeScript
- `django-react` - Django REST Framework + React frontend

**Usage:**

```bash
# List available templates
python scripts/project_scaffolder.py --list-templates

# Create Next.js project
python scripts/project_scaffolder.py nextjs my-app

# Create FastAPI + React project
python scripts/project_scaffolder.py fastapi-react my-api

# Create MERN stack project
python scripts/project_scaffolder.py mern my-project

# Create Django + React project
python scripts/project_scaffolder.py django-react my-app

# Specify output directory
python scripts/project_scaffolder.py nextjs my-app --output ./projects

# JSON output
python scripts/project_scaffolder.py nextjs my-app --json
```

**Parameters:**

| Parameter | Description |
|-----------|-------------|
| `template` | Template name (nextjs, fastapi-react, mern, django-react) |
| `project_name` | Name for the new project directory |
| `--output, -o` | Output directory (default: current directory) |
| `--list-templates, -l` | List all available templates |
| `--json` | Output in JSON format |

**Output includes:**
- Project structure with all necessary files
- Package configurations (package.json, requirements.txt)
- TypeScript configuration
- Docker and docker-compose setup
- Environment file templates
- Next steps for running the project

---

### Code Quality Analyzer

Analyzes fullstack codebases for quality issues.

**Analysis Categories:**
- Security vulnerabilities (hardcoded secrets, injection risks)
- Code complexity metrics (cyclomatic complexity, nesting depth)
- Dependency health (outdated packages, known CVEs)
- Test coverage estimation
- Documentation quality

**Usage:**

```bash
# Analyze current directory
python scripts/code_quality_analyzer.py .

# Analyze specific project
python scripts/code_quality_analyzer.py /path/to/project

# Verbose output with detailed findings
python scripts/code_quality_analyzer.py . --verbose

# JSON output
python scripts/code_quality_analyzer.py . --json

# Save report to file
python scripts/code_quality_analyzer.py . --output report.json
```

**Parameters:**

| Parameter | Description |
|-----------|-------------|
| `project_path` | Path to project directory (default: current directory) |
| `--verbose, -v` | Show detailed findings |
| `--json` | Output in JSON format |
| `--output, -o` | Write report to file |

**Output includes:**
- Overall score (0-100) with letter grade
- Security issues by severity (critical, high, medium, low)
- High complexity files
- Vulnerable dependencies with CVE references
- Test coverage estimate
- Documentation completeness
- Prioritized recommendations

**Sample Output:**

```
============================================================
CODE QUALITY ANALYSIS REPORT
============================================================

Overall Score: 75/100 (Grade: C)
Files Analyzed: 45
Total Lines: 12,500

--- SECURITY ---
  Critical: 1
  High: 2
  Medium: 5

--- COMPLEXITY ---
  Average Complexity: 8.5
  High Complexity Files: 3

--- RECOMMENDATIONS ---
1. [P0] SECURITY
   Issue: Potential hardcoded secret detected
   Action: Remove or secure sensitive data at line 42
```

---

## Workflows

### Workflow 1: Start New Project

1. Choose appropriate stack based on requirements (see Stack Decision Matrix)
2. Scaffold project structure
3. Verify scaffold: confirm `package.json` (or `requirements.txt`) exists
4. Run initial quality check — address any P0 issues before proceeding
5. Set up development environment

```bash
# 1. Scaffold project
python scripts/project_scaffolder.py nextjs my-saas-app

# 2. Verify scaffold succeeded
ls my-saas-app/package.json

# 3. Navigate and install
cd my-saas-app
npm install

# 4. Configure environment
cp .env.example .env.local

# 5. Run quality check
python scripts/code_quality_analyzer.py .

# 6. Start development
npm run dev
```

### Workflow 2: Audit Existing Codebase

1. Run code quality analysis
2. Review security findings — fix all P0 (critical) issues immediately
3. Re-run analyzer to confirm P0 issues are resolved
4. Create tickets for P1/P2 issues

```bash
# 1. Full analysis
python scripts/code_quality_analyzer.py /path/to/project --verbose

# 2. Generate detailed report
python scripts/code_quality_analyzer.py /path/to/project --json --output audit.json

# 3. After fixing P0 issues, re-run to verify
python scripts/code_quality_analyzer.py /path/to/project --verbose
```

### Workflow 3: Stack Selection

Use the tech stack guide to evaluate options:

1. **SEO Required?** → Next.js with SSR
2. **API-heavy backend?** → Separate FastAPI or NestJS
3. **Real-time features?** → Add WebSocket layer
4. **Team expertise** → Match stack to team skills

See `references/tech_stack_guide.md` for detailed comparison.

---

## Reference Guides

### Architecture Patterns (`references/architecture_patterns.md`)

- Frontend component architecture (Atomic Design, Container/Presentational)
- Backend patterns (Clean Architecture, Repository Pattern)
- API design (REST conventions, GraphQL schema design)
- Database patterns (connection pooling, transactions, read replicas)
- Caching strategies (cache-aside, HTTP cache headers)
- Authentication architecture (JWT + refresh tokens, sessions)

### Development Workflows (`references/development_workflows.md`)

- Local development setup (Docker Compose, environment config)
- Git workflows (trunk-based, conventional commits)
- CI/CD pipelines (GitHub Actions examples)
- Testing strategies (unit, integration, E2E)
- Code review process (PR templates, checklists)
- Deployment strategies (blue-green, canary, feature flags)
- Monitoring and observability (logging, metrics, health checks)

### Tech Stack Guide (`references/tech_stack_guide.md`)

- Frontend frameworks comparison (Next.js, React+Vite, Vue)
- Backend frameworks (Express, Fastify, NestJS, FastAPI, Django)
- Database selection (PostgreSQL, MongoDB, Redis)
- ORMs (Prisma, Drizzle, SQLAlchemy)
- Authentication solutions (Auth.js, Clerk, custom JWT)
- Deployment platforms (Vercel, Railway, AWS)
- Stack recommendations by use case (MVP, SaaS, Enterprise)

---

## Quick Reference

### Stack Decision Matrix

| Requirement | Recommendation |
|-------------|---------------|
| SEO-critical site | Next.js with SSR |
| Internal dashboard | React + Vite |
| API-first backend | FastAPI or Fastify |
| Enterprise scale | NestJS + PostgreSQL |
| Rapid prototype | Next.js API routes |
| Document-heavy data | MongoDB |
| Complex queries | PostgreSQL |

### Common Issues

| Issue | Solution |
|-------|----------|
| N+1 queries | Use DataLoader or eager loading |
| Slow builds | Check bundle size, lazy load |
| Auth complexity | Use Auth.js or Clerk |
| Type errors | Enable strict mode in tsconfig |
| CORS issues | Configure middleware properly |

---

## Assumptions and Verifiable Success Criteria (Karpathy discipline)

Before this skill scaffolds, recommends, or modifies any code, the following four assumptions MUST be surfaced. If any are unknown, the skill stops and walks the [Forcing-question library](#forcing-question-library-matt-pocock-grill) instead.

1. **Team size today + 12-month headcount** — drives architecture (monolith / modular / services). Sam Newman: "MonolithFirst."
2. **Deployment cadence target** — drives CI/CD spend and feature-flag investment. *Accelerate* (Forsgren et al. 2018).
3. **User-facing vs. internal vs. marketing-site** — drives stack pick and a11y/perf budget.
4. **Monthly cloud + SaaS budget ceiling** — drives the build-vs-managed-service split.

**Verifiable success criteria** (Karpathy #4) — every recommendation this skill emits must include three machine-checkable numbers:

- An API latency target (p50, p95, p99 in ms)
- A frontend perf target (LCP, INP, CLS on mobile-4G)
- An uptime / SLO target

If any of those three is not stated, the recommendation is incomplete — go back to Q7 of the forcing-question library.

The `scripts/fullstack_decision_engine.py` tool encodes these checks: it refuses to recommend a profile without all four assumption inputs and prints the verifiable thresholds for the matched profile.

---

## Customization profiles

Four built-in profiles in `profiles/` calibrate every recommendation:

| Profile | When to pick | Cloud ceiling | Pattern |
|---|---|---|---|
| `saas-startup` | < 10 eng, customer-facing, daily+ cadence | $8K/mo | Modular monolith on Next.js + Postgres |
| `enterprise-scale` | 50+ eng, regulated, per-PR with gates | $250K/mo | Domain-bounded services + platform team |
| `internal-tool` | ≤ 5 eng, auth-walled, < 100 DAU | $500/mo | Retool-first; thin custom stack if forced |
| `marketing-site` | SEO-dependent, near-zero write | $200/mo | Static-first (Astro / 11ty / Next-static) |

Pick a profile via:

```bash
python scripts/fullstack_decision_engine.py \
  --team-size 6 --team-size-12mo 12 \
  --cadence daily --user-facing true --budget 5000 \
  --traffic-p99-rps 45 --data-sensitivity pii-only
```

The tool returns the best-fit profile, the tradeoff against the runner-up (if within 15%), the stack recommendation, the anti-patterns to avoid on that profile, and the named-approver chain. **This tool never auto-approves.**

To add a custom profile: copy `profiles/saas-startup.json` to `profiles/<your-org>.json`, adjust the `constraints` and `stack_recommendations` blocks, and rerun. The JSON is the customization surface — no code changes needed.

---

## Composition map

This skill does NOT reimplement scope owned by the POWERFUL-tier specialists. It forks into them. See `references/composition_map.md` for the full routing table. Key forks:

| Concern | Fork into |
|---|---|
| API contract review | `engineering/skills/api-design-reviewer/` |
| Database schema design | `engineering/skills/database-designer/` |
| Reliability / SLO design | `engineering/slo-architect/` |
| CI/CD pipeline | `engineering/skills/ci-cd-pipeline-builder/` |
| Performance profiling | `engineering/skills/performance-profiler/` |
| Pre-commit Karpathy review | `engineering/karpathy-coder/` |
| Pre-flight architecture grill | `engineering/grill-me/` |

The `cs-fullstack-engineer` agent (in `agents/engineering/cs-fullstack-engineer.md`) orchestrates these forks via `context: fork`. Invoke it from another agent with `Agent({subagent_type: "cs-fullstack-engineer", prompt: "..."})` or via the slash command `/cs:fullstack-review <your problem>`.

---

## Forcing-question library (Matt Pocock grill)

Before locking any architecture or stack decision, walk the seven forcing questions in `references/forcing_questions.md`. Each has a recommended answer, canon citation, and kill criterion. The discipline:

1. One question per turn. No bundling.
2. Always recommend the answer with cited canon.
3. Track answers in a working file (e.g., `/tmp/fullstack-grill-<date>.md`).
4. If a kill criterion trips, stop. Do not scaffold around an unresolved gap.
5. After Q7, run `fullstack_decision_engine.py` with the seven answers as inputs.

Summary of the seven questions (full content in the reference):

1. Team size today + 12-month headcount?
2. Deployment cadence — per-PR, daily, weekly, quarterly?
3. Customer-facing, internal tool, or marketing site?
4. One-year p50 / p99 traffic forecast?
5. Hiring against the stack or training the team?
6. Year-one monthly cloud + SaaS ceiling?
7. Three verifiable success criteria with numeric targets?

---

## Invocation from other agents and skills

This skill is invokable by any other agent or skill via three surfaces:

1. **Slash command:** `/cs:fullstack-review <prompt>` — runs the full grill + decision engine + composition routing.
2. **Agent subagent:** `Agent({subagent_type: "cs-fullstack-engineer", prompt: "..."})` — forks context, returns ≤ 200-word digest.
3. **Direct tool call:** `python scripts/fullstack_decision_engine.py ...` — deterministic profile match without the conversational grill (use when inputs are already known).

See `agents/engineering/cs-fullstack-engineer.md` for the full invocation contract.
