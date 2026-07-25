# database-schema-designer reference

## Full Schema Example (Task Management SaaS)

### Prisma Schema

```prisma
// schema.prisma
generator client {
  provider = "prisma-client-js"
}

datasource db {
  provider = "postgresql"
  url      = env("DATABASE_URL")
}

// ── Multi-tenancy ─────────────────────────────────────────────────────────────

model Organization {
  id        String   @id @default(cuid())
  name      String
  slug      String   @unique
  plan      Plan     @default(FREE)
  createdAt DateTime @default(now()) @map("created_at")
  updatedAt DateTime @updatedAt @map("updated_at")
  deletedAt DateTime? @map("deleted_at")

  users      OrganizationMember[]
  projects   Project[]
  auditLogs  AuditLog[]

  @@map("organizations")
}

model OrganizationMember {
  id             String   @id @default(cuid())
  organizationId String   @map("organization_id")
  userId         String   @map("user_id")
  role           OrgRole  @default(MEMBER)
  joinedAt       DateTime @default(now()) @map("joined_at")

  organization Organization @relation(fields: [organizationId], references: [id], onDelete: Cascade)
  user         User         @relation(fields: [userId], references: [id], onDelete: Cascade)

  @@unique([organizationId, userId])
  @@index([userId])
  @@map("organization_members")
}

model User {
  id           String    @id @default(cuid())
  email        String    @unique
  name         String?
  avatarUrl    String?   @map("avatar_url")
  passwordHash String?   @map("password_hash")
  emailVerifiedAt DateTime? @map("email_verified_at")
  lastLoginAt  DateTime? @map("last_login_at")
  createdAt    DateTime  @default(now()) @map("created_at")
  updatedAt    DateTime  @updatedAt @map("updated_at")
  deletedAt    DateTime? @map("deleted_at")

  memberships  OrganizationMember[]
  ownedProjects Project[]           @relation("ProjectOwner")
  assignedTasks TaskAssignment[]
  comments     Comment[]
  auditLogs    AuditLog[]

  @@map("users")
}

// ── Core entities ─────────────────────────────────────────────────────────────

model Project {
  id             String   @id @default(cuid())
  organizationId String   @map("organization_id")
  ownerId        String   @map("owner_id")
  name           String
  description    String?
  status         ProjectStatus @default(ACTIVE)
  settings       Json     @default("{}")
  createdAt      DateTime @default(now()) @map("created_at")
  updatedAt      DateTime @updatedAt @map("updated_at")
  deletedAt      DateTime? @map("deleted_at")

  organization Organization @relation(fields: [organizationId], references: [id])
  owner        User         @relation("ProjectOwner", fields: [ownerId], references: [id])
  tasks        Task[]
  labels       Label[]

  @@index([organizationId])
  @@index([organizationId, status])
  @@index([deletedAt])
  @@map("projects")
}

model Task {
  id          String     @id @default(cuid())
  projectId   String     @map("project_id")
  title       String
  description String?
  status      TaskStatus @default(TODO)
  priority    Priority   @default(MEDIUM)
  dueDate     DateTime?  @map("due_date")
  position    Float      @default(0)          // For drag-and-drop ordering
  version     Int        @default(1)           // Optimistic locking
  createdById String     @map("created_by_id")
  updatedById String     @map("updated_by_id")
  createdAt   DateTime   @default(now()) @map("created_at")
  updatedAt   DateTime   @updatedAt @map("updated_at")
  deletedAt   DateTime?  @map("deleted_at")

  project     Project          @relation(fields: [projectId], references: [id])
  assignments TaskAssignment[]
  labels      TaskLabel[]
  comments    Comment[]
  attachments Attachment[]

  @@index([projectId])
  @@index([projectId, status])
  @@index([projectId, deletedAt])
  @@index([dueDate], where: { deletedAt: null })  // Partial index
  @@map("tasks")
}

// ── Polymorphic attachments ───────────────────────────────────────────────────

model Attachment {
  id           String   @id @default(cuid())
  // Polymorphic association
  entityType   String   @map("entity_type")   // "task" | "comment"
  entityId     String   @map("entity_id")
  filename     String
  mimeType     String   @map("mime_type")
  sizeBytes    Int      @map("size_bytes")
  storageKey   String   @map("storage_key")   // S3 key
  uploadedById String   @map("uploaded_by_id")
  createdAt    DateTime @default(now()) @map("created_at")

  // Only one concrete relation (task) — polymorphic handled at app level
  task      Task? @relation(fields: [entityId], references: [id], map: "attachment_task_fk")

  @@index([entityType, entityId])
  @@map("attachments")
}

// ── Audit trail ───────────────────────────────────────────────────────────────

model AuditLog {
  id             String   @id @default(cuid())
  organizationId String   @map("organization_id")
  userId         String?  @map("user_id")
  action         String                           // "task.created", "task.status_changed"
  entityType     String   @map("entity_type")
  entityId       String   @map("entity_id")
  before         Json?                            // Previous state
  after          Json?                            // New state
  ipAddress      String?  @map("ip_address")
  userAgent      String?  @map("user_agent")
  createdAt      DateTime @default(now()) @map("created_at")

  organization Organization @relation(fields: [organizationId], references: [id])
  user         User?        @relation(fields: [userId], references: [id])

  @@index([organizationId, createdAt(sort: Desc)])
  @@index([entityType, entityId])
  @@index([userId])
  @@map("audit_logs")
}

enum Plan        { FREE STARTER GROWTH ENTERPRISE }
enum OrgRole     { OWNER ADMIN MEMBER VIEWER }
enum ProjectStatus { ACTIVE ARCHIVED }
enum TaskStatus  { TODO IN_PROGRESS IN_REVIEW DONE CANCELLED }
enum Priority    { LOW MEDIUM HIGH CRITICAL }
```

---

### Drizzle Schema (TypeScript)

```typescript
// db/schema.ts
import {
  pgTable, text, timestamp, integer, boolean,
  varchar, jsonb, real, pgEnum, uniqueIndex, index,
} from 'drizzle-orm/pg-core'
import { createId } from '@paralleldrive/cuid2'

export const taskStatusEnum = pgEnum('task_status', [
  'todo', 'in_progress', 'in_review', 'done', 'cancelled'
])
export const priorityEnum = pgEnum('priority', ['low', 'medium', 'high', 'critical'])

export const tasks = pgTable('tasks', {
  id:          text('id').primaryKey().$defaultFn(() => createId()),
  projectId:   text('project_id').notNull().references(() => projects.id),
  title:       varchar('title', { length: 500 }).notNull(),
  description: text('description'),
  status:      taskStatusEnum('status').notNull().default('todo'),
  priority:    priorityEnum('priority').notNull().default('medium'),
  dueDate:     timestamp('due_date', { withTimezone: true }),
  position:    real('position').notNull().default(0),
  version:     integer('version').notNull().default(1),
  createdById: text('created_by_id').notNull().references(() => users.id),
  updatedById: text('updated_by_id').notNull().references(() => users.id),
  createdAt:   timestamp('created_at', { withTimezone: true }).notNull().defaultNow(),
  updatedAt:   timestamp('updated_at', { withTimezone: true }).notNull().defaultNow(),
  deletedAt:   timestamp('deleted_at', { withTimezone: true }),
}, (table) => ({
  projectIdx:       index('tasks_project_id_idx').on(table.projectId),
  projectStatusIdx: index('tasks_project_status_idx').on(table.projectId, table.status),
}))

// Infer TypeScript types
export type Task = typeof tasks.$inferSelect
export type NewTask = typeof tasks.$inferInsert
```

---

### Alembic Migration (Python / SQLAlchemy)

```python
# alembic/versions/20260301_create_tasks.py
"""Create tasks table

Revision ID: a1b2c3d4e5f6
Revises: previous_revision
Create Date: 2026-03-01 12:00:00
"""

from alembic import op
import sqlalchemy as sa
from sqlalchemy.dialects import postgresql

revision = 'a1b2c3d4e5f6'
down_revision = 'previous_revision'


def upgrade() -> None:
    # Create enums
    task_status = postgresql.ENUM(
        'todo', 'in_progress', 'in_review', 'done', 'cancelled',
        name='task_status'
    )
    task_status.create(op.get_bind())
    
    op.create_table(
        'tasks',
        sa.Column('id', sa.Text(), primary_key=True),
        sa.Column('project_id', sa.Text(), sa.ForeignKey('projects.id'), nullable=False),
        sa.Column('title', sa.VARCHAR(500), nullable=False),
        sa.Column('description', sa.Text()),
        sa.Column('status', postgresql.ENUM('todo', 'in_progress', 'in_review', 'done', 'cancelled', name='task_status', create_type=False), nullable=False, server_default='todo'),
        sa.Column('priority', sa.Text(), nullable=False, server_default='medium'),
        sa.Column('due_date', sa.TIMESTAMP(timezone=True)),
        sa.Column('position', sa.Float(), nullable=False, server_default='0'),
        sa.Column('version', sa.Integer(), nullable=False, server_default='1'),
        sa.Column('created_by_id', sa.Text(), sa.ForeignKey('users.id'), nullable=False),
        sa.Column('updated_by_id', sa.Text(), sa.ForeignKey('users.id'), nullable=False),
        sa.Column('created_at', sa.TIMESTAMP(timezone=True), nullable=False, server_default=sa.text('NOW()')),
        sa.Column('updated_at', sa.TIMESTAMP(timezone=True), nullable=False, server_default=sa.text('NOW()')),
        sa.Column('deleted_at', sa.TIMESTAMP(timezone=True)),
    )
    
    # Indexes
    op.create_index('tasks_project_id_idx', 'tasks', ['project_id'])
    op.create_index('tasks_project_status_idx', 'tasks', ['project_id', 'status'])
    # Partial index for active tasks only
    op.create_index(
        'tasks_due_date_active_idx',
        'tasks', ['due_date'],
        postgresql_where=sa.text('deleted_at IS NULL')
    )


def downgrade() -> None:
    op.drop_table('tasks')
    op.execute("DROP TYPE IF EXISTS task_status")
```

---
