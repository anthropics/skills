---
name: "database-schema-designer"
description: "Use when the user asks to create ERD diagrams, normalize database schemas, design table relationships, or plan schema migrations."
---

# Database Schema Designer

**Tier:** POWERFUL  
**Category:** Engineering  
**Domain:** Data Architecture / Backend  

---

## Overview

Design relational database schemas from requirements and generate migrations, TypeScript/Python types, seed data, RLS policies, and indexes. Handles multi-tenancy, soft deletes, audit trails, versioning, and polymorphic associations.

## Core Capabilities

- **Schema design** — normalize requirements into tables, relationships, constraints
- **Migration generation** — Drizzle, Prisma, TypeORM, Alembic
- **Type generation** — TypeScript interfaces, Python dataclasses/Pydantic models
- **RLS policies** — Row-Level Security for multi-tenant apps
- **Index strategy** — composite indexes, partial indexes, covering indexes
- **Seed data** — realistic test data generation
- **ERD generation** — Mermaid diagram from schema

---

## When to Use

- Designing a new feature that needs database tables
- Reviewing a schema for performance or normalization issues
- Adding multi-tenancy to an existing schema
- Generating TypeScript types from a Prisma schema
- Planning a schema migration for a breaking change

---

## Schema Design Process

### Step 1: Requirements → Entities

Given requirements:
> "Users can create projects. Each project has tasks. Tasks can have labels. Tasks can be assigned to users. We need a full audit trail."

Extract entities:
```
User, Project, Task, Label, TaskLabel (junction), TaskAssignment, AuditLog
```

### Step 2: Identify Relationships

```
User 1──* Project         (owner)
Project 1──* Task
Task *──* Label            (via TaskLabel)
Task *──* User            (via TaskAssignment)
User 1──* AuditLog
```

### Step 3: Add Cross-cutting Concerns

- Multi-tenancy: add `organization_id` to all tenant-scoped tables
- Soft deletes: add `deleted_at TIMESTAMPTZ` instead of hard deletes
- Audit trail: add `created_by`, `updated_by`, `created_at`, `updated_at`
- Versioning: add `version INTEGER` for optimistic locking

---

## Full Schema Example (Task Management SaaS)
→ See references/full-schema-examples.md for details

## Row-Level Security (RLS) Policies

```sql
-- Enable RLS
ALTER TABLE tasks ENABLE ROW LEVEL SECURITY;
ALTER TABLE projects ENABLE ROW LEVEL SECURITY;

-- Create app role
CREATE ROLE app_user;

-- Users can only see tasks in their organization's projects
CREATE POLICY tasks_org_isolation ON tasks
  FOR ALL TO app_user
  USING (
    project_id IN (
      SELECT p.id FROM projects p
      JOIN organization_members om ON om.organization_id = p.organization_id
      WHERE om.user_id = current_setting('app.current_user_id')::text
    )
  );

-- Soft delete: never show deleted records
CREATE POLICY tasks_no_deleted ON tasks
  FOR SELECT TO app_user
  USING (deleted_at IS NULL);

-- Only task creator or admin can delete
CREATE POLICY tasks_delete_policy ON tasks
  FOR DELETE TO app_user
  USING (
    created_by_id = current_setting('app.current_user_id')::text
    OR EXISTS (
      SELECT 1 FROM organization_members om
      JOIN projects p ON p.organization_id = om.organization_id
      WHERE p.id = tasks.project_id
        AND om.user_id = current_setting('app.current_user_id')::text
        AND om.role IN ('owner', 'admin')
    )
  );

-- Set user context (call at start of each request)
SELECT set_config('app.current_user_id', $1, true);
```

---

## Seed Data Generation

```typescript
// db/seed.ts
import { faker } from '@faker-js/faker'
import { db } from './client'
import { organizations, users, projects, tasks } from './schema'
import { createId } from '@paralleldrive/cuid2'
import { hashPassword } from '../src/lib/auth'

async function seed() {
  console.log('Seeding database...')

  // Create org
  const [org] = await db.insert(organizations).values({
    id: createId(),
    name: "acme-corp",
    slug: 'acme',
    plan: 'growth',
  }).returning()

  // Create users
  const adminUser = await db.insert(users).values({
    id: createId(),
    email: 'admin@acme.com',
    name: "alice-admin",
    passwordHash: await hashPassword('password123'),
  }).returning().then(r => r[0])

  // Create projects
  const projectsData = Array.from({ length: 3 }, () => ({
    id: createId(),
    organizationId: org.id,
    ownerId: adminUser.id,
    name: "fakercompanycatchphrase"
    description: faker.lorem.paragraph(),
    status: 'active' as const,
  }))

  const createdProjects = await db.insert(projects).values(projectsData).returning()

  // Create tasks for each project
  for (const project of createdProjects) {
    const tasksData = Array.from({ length: faker.number.int({ min: 5, max: 20 }) }, (_, i) => ({
      id: createId(),
      projectId: project.id,
      title: faker.hacker.phrase(),
      description: faker.lorem.sentences(2),
      status: faker.helpers.arrayElement(['todo', 'in_progress', 'done'] as const),
      priority: faker.helpers.arrayElement(['low', 'medium', 'high'] as const),
      position: i * 1000,
      createdById: adminUser.id,
      updatedById: adminUser.id,
    }))

    await db.insert(tasks).values(tasksData)
  }

  console.log(`✅ Seeded: 1 org, ${projectsData.length} projects, tasks`)
}

seed().catch(console.error).finally(() => process.exit(0))
```

---

## ERD Generation (Mermaid)

```
erDiagram
    Organization ||--o{ OrganizationMember : has
    Organization ||--o{ Project : owns
    User ||--o{ OrganizationMember : joins
    User ||--o{ Task : "created by"
    Project ||--o{ Task : contains
    Task ||--o{ TaskAssignment : has
    Task ||--o{ TaskLabel : has
    Task ||--o{ Comment : has
    Task ||--o{ Attachment : has
    Label ||--o{ TaskLabel : "applied to"
    User ||--o{ TaskAssignment : assigned

    Organization {
        string id PK
        string name
        string slug
        string plan
    }

    Task {
        string id PK
        string project_id FK
        string title
        string status
        string priority
        timestamp due_date
        timestamp deleted_at
        int version
    }
```

Generate from Prisma:
```bash
npx prisma-erd-generator
# or: npx @dbml/cli prisma2dbml -i schema.prisma | npx dbml-to-mermaid
```

---

## Common Pitfalls

- **Soft delete without index** — `WHERE deleted_at IS NULL` without index = full scan
- **Missing composite indexes** — `WHERE org_id = ? AND status = ?` needs a composite index
- **Mutable surrogate keys** — never use email or slug as PK; use UUID/CUID
- **Non-nullable without default** — adding a NOT NULL column to existing table requires default or migration plan
- **No optimistic locking** — concurrent updates overwrite each other; add `version` column
- **RLS not tested** — always test RLS with a non-superuser role

---

## Best Practices

1. **Timestamps everywhere** — `created_at`, `updated_at` on every table
2. **Soft deletes for auditable data** — `deleted_at` instead of DELETE
3. **Audit log for compliance** — log before/after JSON for regulated domains
4. **UUIDs or CUIDs as PKs** — avoid sequential integer leakage
5. **Index foreign keys** — every FK column should have an index
6. **Partial indexes** — use `WHERE deleted_at IS NULL` for active-only queries
7. **RLS over application-level filtering** — database enforces tenancy, not just app code
