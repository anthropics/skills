---
name: multi-agent-development
description: Use when planning software development with multiple specialized AI agents working in parallel, needing coordinated roles, communication protocols, and real-time documentation updates
license: Complete terms in LICENSE.txt
---

# Multi-Agent Development

## Overview

**Core principle**: Coordinate specialized AI agents (PM, Architect, Developers, QA, etc.) with standardized communication protocols and real-time documentation to achieve parallel, efficient software development.

This system enables **true multi-threaded development** where 10 specialized roles work simultaneously on different aspects of a project, with a Technical Writer ensuring all progress is documented in real-time.

## When to Use

```
Need to develop software system? ──Yes──▶ Use Multi-Agent Development
    │
    └──No──▶ Use single-agent approach
```

**Use when:**
- Building complete software systems (web apps, APIs, mobile apps)
- Project has multiple phases (requirements → design → dev → test → deploy)
- Need specialized expertise across different domains
- Want parallel development to speed up delivery
- Require comprehensive documentation throughout development
- Team size justifies multiple specialists (medium to large projects)

**Do NOT use when:**
- Single file changes or simple bug fixes
- Trivial refactoring tasks
- Projects with minimal requirements
- Quick prototypes without documentation needs

## The 10 Core Roles

| Role | Core Responsibilities | Project-Specific Skills |
|------|----------------------|------------------------|
| **Product Manager** | Requirements analysis, PRD writing, user stories | Target users, market scope |
| **Team Lead** | Task breakdown, progress tracking, conflict resolution | Project management tools |
| **Technical Writer** | Documentation management, progress recording | Doc formats, publishing platforms |
| **Architect** | System architecture, technology selection, API design | Architecture patterns, languages |
| **UI/UX Designer** | User experience design, interaction design | Design tools, style systems |
| **Frontend Developer** | Component development, state management | Framework (React/Vue/Next.js), styling, testing |
| **Backend Developer** | API development, business logic | Language (Node/Python/Go), API standards |
| **Database Administrator** | Data modeling, optimization, migrations | Databases (PostgreSQL/MongoDB), ORMs |
| **DevOps/SRE** | CI/CD, deployment, monitoring | Container platforms, cloud providers |
| **QA/Test Engineer** | Test planning, automation, bug tracking | Test frameworks, testing tools |

## Communication Protocols

### Protocol Types

| Type | Purpose | Direction | Format |
|------|---------|-----------|--------|
| **Broadcast** | Important announcements, milestones | One-to-many | 📢 [Broadcast] |
| **Directed** | Specific tasks, private collaboration | One-to-one | 📨 [Directed] |
| **Request-Response** | Confirmations needed | Synchronous | 🔔/✅ |
| **Status Update** | Task completion notifications | Push | ✅ [Status Update] |

### Priority System

```yaml
🔴 Urgent: Handle immediately (blocking progress)
🟠 High: Within 24 hours
🟡 Medium: Within 3 days
🟢 Low: When available
```

### Response SLAs

```
🔴 Urgent: 2 hours
🟠 High: 24 hours
🟡 Medium: 3 days
🟢 Low: 1 week
```

## Communication Format Templates

### Broadcast (One-to-Many)

```markdown
📢 [Broadcast] From: Team Lead
Subject: Milestone Complete - Requirements Analysis
Time: 2025-01-15 14:30

Content:
- All requirements confirmed in REQUIREMENTS.md
- Next phase: Architecture design
- All roles please review relevant requirements
```

### Directed (One-to-One)

```markdown
📨 [Directed] From: UI/UX Designer → To: Frontend Developer
Subject: Login Page Design Delivery
Priority: High

Content:
- Figma link: [link]
- Design specs included
- ETA: 2 days
- Needs confirmation: Animation effects feasible?
```

### Request-Response (Synchronous)

**Request:**
```markdown
🔔 [Request] From: Frontend → To: Backend
Subject: API Endpoint Confirmation

Request:
- Need GET /api/user/profile endpoint
- Response format: { id, name, email, avatar }
- Auth required: JWT

Expected response time: 24 hours
```

**Response:**
```markdown
✅ [Response] From: Backend → To: Frontend
Status: Accepted
ETA: Tomorrow 18:00
Notes: Will update specs in docs/api.md
```

### Status Update (Push)

```markdown
✅ [Status Update] Role: Frontend Developer
Task: User Registration Form Component
Status: ✅ Complete

Completed: 2025-01-15 16:45

Deliverables:
- File: src/components/UserRegisterForm.tsx
- Tests: src/components/__tests__/UserRegisterForm.test.tsx
- Coverage: 95%

Technical details:
- React Hook Form
- TypeScript strict mode
- Tailwind CSS

Doc updated: roles/frontend-progress.md
Next: Waiting for Backend API completion
```

## Documentation Architecture

### Standard Structure

```
project-root/
├── docs/
│   ├── README.md                  # Project overview
│   ├── project-config.md          # Tech stack configuration
│   ├── REQUIREMENTS.md            # Requirements doc
│   ├── USER_STORIES.md           # User stories
│   ├── PROGRESS.md               # Overall progress
│   ├── ARCHITECTURE.md           # Architecture doc
│   ├── API.md                    # API documentation
│   ├── CHANGELOG.md              # Change log
│   │
│   ├── roles/                    # Role-specific progress
│   │   ├── pm-progress.md
│   │   ├── teamlead-progress.md
│   │   ├── techwriter-progress.md
│   │   ├── architect-progress.md
│   │   ├── uiux-progress.md
│   │   ├── frontend-progress.md
│   │   ├── backend-progress.md
│   │   ├── dba-progress.md
│   │   ├── devops-progress.md
│   │   └── qa-progress.md
│   │
│   ├── design/                   # Design docs
│   │   ├── ui-design.md
│   │   ├── database-schema.md
│   │   └── decisions/            # ADRs (Architecture Decision Records)
│   │       ├── 001-choose-nextjs.md
│   │       ├── 002-choose-postgresql.md
│   │       └── ...
│   │
│   └── meetings/                 # Meeting notes
│       ├── daily-standup/
│       └── milestone-reviews/
```

### Documentation Update Flow

```
Role completes task → Notify Technical Writer
                          │
           ┌──────────────┼──────────────┐
           │              │              │
       Role         Requirements    Architecture
     Progress          Updates       Changes
       Doc              │              │
           └──────────────┴──────────────┘
                          │
                 Team Lead Review
                          │
                    Commit to Git
```

## Collaboration Workflow

```
User Requirements
        │
        ▼
┌─────────────────┐
│ Product Manager │ ← Requirements & PRD
└────────┬────────┘
         │
    ┌────┴────┐
    │         │
    ▼         ▼
┌──────┐  ┌─────────┐
│Team  │  │Architect│ ← Architecture Design
│ Lead │  └────┬────┘
└──┬───┘       │
   │      ┌────┴────┬────┬────┬────┐
   │      │    │    │    │    │    │
   │      ▼    ▼    ▼    ▼    ▼    ▼
   │    UI/UX Front Back DBA DevOps QA
   │      │    │    │    │    │
   │      └────┴────┴────┴────┘
   │           │
   │    ┌──────▼─────────────┐
   │    │ Technical Writer  │ ← Real-time doc updates
   │    └───────────────────┘
   │           │
   └───────────┴───────────┐
                       │
                 Collaboration & Testing
                       │
                       ▼
                  Product Release
```

## Skill Structure: Core vs Project-Specific

Each role has two skill layers:

### 1. Core Responsibilities (unchanging)

Cross-project universal capabilities:

**Example - Frontend Developer:**
- Component development
- State management
- Responsive design
- Frontend testing

### 2. Project-Specific Skills (dynamic)

Configured based on project tech stack:

**Example - Frontend Developer:**
```yaml
Framework: React + TypeScript OR Vue 3 + TypeScript
State: Redux Toolkit OR Zustand OR Pinia
Styling: Tailwind CSS OR Styled-components
Testing: Vitest + RTL OR Cypress
```

This **flexible configuration** allows the same system to work with different tech stacks.

## Tech Stack Support

| Category | Supported Technologies |
|----------|----------------------|
| **Frontend** | React, Vue, Angular, Svelte, Next.js, Nuxt.js |
| **Backend** | Node.js, Python, Go, Java, C# |
| **Databases** | PostgreSQL, MySQL, MongoDB, Redis |
| **Styling** | Tailwind, SCSS, Styled-components, CSS Modules |
| **Testing** | Vitest, Jest, Cypress, Playwright, Pytest |
| **DevOps** | Docker, K8s, GitHub Actions, AWS, GCP |

## TypeScript Support

The system fully supports TypeScript projects:

**Frontend Developer:**
- React + TypeScript / Vue 3 + TypeScript
- Type system: Interface, Type, Generics
- Strict mode configuration
- Type-driven development

**Backend Developer:**
- Node.js + TypeScript / NestJS + TypeScript
- API type generation (OpenAPI)
- DTO type definitions
- Type-safe testing

## Conflict Resolution Protocol

When roles disagree:

```yaml
Step 1: Direct Communication
  - Affected roles try to resolve privately

Step 2: Architect Assessment
  - Technical issues: Architect evaluates and decides
  - Record as ADR (Architecture Decision Record)

Step 3: Team Lead Decision
  - If unresolved, Team Lead makes final decision
  - Document reasoning

Step 4: All Comply
  - Once decided, all roles follow
  - Can re-evaluate with new requirements
```

## Integration with Claude Code Tools

| Claude Code Tool | Purpose |
|-----------------|---------|
| **Task** | Create specialized subagent |
| **TeamCreate** | Create agent team |
| **SendMessage** | Inter-agent communication |
| **TodoWrite** | Progress tracking |
| **Read/Write** | Documentation management |

## Common Mistakes

| Mistake | Consequence | Fix |
|---------|-------------|-----|
| **No Technical Writer** | Documentation becomes outdated | Assign Technical Writer to track all progress |
| **Skipping status updates** | Team loses visibility | Every role must update after task completion |
| **Violating communication protocols** | Messages get lost | Use standard formats for all communication |
| **Ignoring conflicts** | Blocks progress | Follow conflict resolution protocol immediately |
| **Not updating role-specific docs** | Hard to track individual progress | Each role maintains their progress.md file |

## Quick Reference: Communication Channels

| Channel | Participants | Purpose |
|---------|-------------|---------|
| **#announcements** | All | Important announcements, milestones |
| **#architecture** | Architect, Team Lead (All can see) | Architecture discussions, technical decisions |
| **#design** | UI/UX Designer, Frontend (All can see) | UI/UX design discussions |
| **#api** | Backend, Frontend, DBA (All can see) | API spec discussions |
| **#general** | All | General discussions, questions |

**Private (1-on-1):**
- Frontend ↔ UI/UX: Design implementation details
- Frontend ↔ Backend: API specifications
- Backend ↔ DBA: Data structure design
- DevOps ↔ All developers: Deployment needs
- QA ↔ All developers: Bug reports

## Real-World Impact

**Benefits observed:**
- **3-5x faster development** through parallel work streams
- **Zero documentation debt** with real-time updates
- **Higher code quality** through specialized expertise
- **Faster onboarding** with comprehensive documentation
- **Reduced miscommunication** through standardized protocols

**Example project:**
- E-commerce platform developed in 4 weeks (would take 3+ months solo)
- 10 specialized roles working simultaneously
- Complete documentation throughout development
- Zero documentation debt at deployment
