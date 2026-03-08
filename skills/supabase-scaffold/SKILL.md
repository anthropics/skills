---
name: supabase-scaffold
description: Generate Supabase SQL migrations with RLS, TypeScript types, Next.js API routes, Zod schemas, and React forms from natural language data model descriptions. Use when user asks to scaffold a Supabase project.
license: MIT
---

# Supabase 全栈项目脚手架生成器

## 触发条件

当用户提到以下关键词时激活此 skill：
- "supabase 脚手架"、"supabase scaffold"
- "生成数据模型"、"新建 supabase 表"
- "supabase migration"、"supabase RLS"
- "supabase 项目初始化"

## 概述

从自然语言的数据模型描述出发，一站式生成 Supabase 全栈项目代码：
- SQL migration（含 RLS 策略）
- TypeScript 类型定义（Supabase Database 格式）
- Next.js App Router CRUD API routes
- Zod validation schema
- Auth 配置（邮箱 / OAuth / Magic Link）
- React 表单组件（基于 schema）
- 关联表支持（外键、多对多中间表）

---

## 第一步：数据模型分析

从用户的自然语言描述中提取以下信息：

### 1.1 实体提取

识别所有名词性实体，例如：
- "用户可以创建多个项目，每个项目有多个任务" → 实体：`users`、`projects`、`tasks`

对每个实体确定：
| 要素 | 说明 |
|------|------|
| 表名 | 复数、snake_case（如 `blog_posts`） |
| 主键 | 默认 `id uuid default gen_random_uuid()` |
| 时间戳 | 默认添加 `created_at` 和 `updated_at` |
| 软删除 | 如需要，添加 `deleted_at timestamp` |

### 1.2 属性提取

从描述中推断字段类型：

| 自然语言 | PostgreSQL 类型 | 备注 |
|----------|----------------|------|
| 名称/标题 | `text` | 不用 varchar，Postgres 中 text 更优 |
| 邮箱 | `text` + unique 约束 | |
| 数量/计数 | `integer` | |
| 价格/金额 | `numeric(10,2)` | 不用 float，避免精度问题 |
| 是否/布尔 | `boolean default false` | |
| 日期 | `date` | |
| 时间 | `timestamptz` | 始终使用带时区的时间戳 |
| 长文本 | `text` | |
| 枚举状态 | 创建 PostgreSQL enum 或 `text check` | |
| JSON 数据 | `jsonb` | 不用 json，jsonb 支持索引 |
| 文件/图片 | `text`（存储 Storage URL） | |
| 数组 | `text[]` / `integer[]` 等 | PostgreSQL 原生数组类型 |
| 坐标/位置 | `point` | 二维坐标，如 `(x, y)` |
| 时间间隔 | `interval` | 如 `'2 hours'`、`'30 days'` |
| IP 地址 | `inet` | 支持 IPv4/IPv6 |
| 范围 | `int4range` / `tstzrange` 等 | 如价格区间、时间段 |
| 二进制 | `bytea` | 小型二进制数据，大文件用 Storage |

### 1.3 关系提取

| 自然语言 | 关系类型 | 实现方式 |
|----------|---------|---------|
| "属于"、"的" | 一对多 | 子表添加 `parent_id uuid references parent(id)` |
| "有多个" | 一对多 | 同上（从父表角度描述） |
| "多对多" | 多对多 | 创建中间表 `table_a_table_b` |
| "有一个" | 一对一 | 添加外键 + unique 约束 |

### 1.4 所有权模型判断

询问或推断每个表的数据所有权模式：

| 模式 | 适用场景 | RLS 策略 |
|------|---------|---------|
| owner-based | 用户拥有自己的数据 | `auth.uid() = user_id` |
| role-based | 管理员/编辑/查看者 | `auth.jwt() ->> 'role'` 检查 |
| org-based | 组织级多租户 | 通过 `org_members` 表关联检查 |

---

## 第二步：SQL Migration 生成

### 2.1 基础模板

```sql
-- migration: YYYYMMDDHHMMSS_create_<table_name>.sql

-- gen_random_uuid() is built into PostgreSQL 14+ (used by Supabase).
-- No need for uuid-ossp extension.

-- Create enum types (if needed)
create type public.<enum_name> as enum ('value1', 'value2', 'value3');

-- Create table
create table public.<table_name> (
  id uuid primary key default gen_random_uuid(),
  -- user ownership
  user_id uuid not null references auth.users(id) on delete cascade,

  -- business fields
  title text not null,
  description text,
  status public.<enum_name> not null default 'value1',

  -- metadata
  created_at timestamptz not null default now(),
  updated_at timestamptz not null default now()
);

-- Indexes
create index idx_<table_name>_user_id on public.<table_name>(user_id);
create index idx_<table_name>_status on public.<table_name>(status);
create index idx_<table_name>_created_at on public.<table_name>(created_at desc);

-- Updated_at trigger
-- NOTE: Only create this function once (in the first migration).
-- Subsequent migrations should only create the trigger, not the function.
create or replace function public.handle_updated_at()
returns trigger as $$
begin
  new.updated_at = now();
  return new;
end;
$$ language plpgsql;

create trigger on_<table_name>_updated
  before update on public.<table_name>
  for each row
  execute function public.handle_updated_at();

-- Enable RLS
alter table public.<table_name> enable row level security;
```

### 2.2 RLS 策略模板

#### Owner-Based（用户拥有自己的数据）

```sql
-- Owner can read own data
create policy "<table>_select_own"
  on public.<table_name>
  for select
  to authenticated
  using (user_id = auth.uid());

-- Owner can insert own data
create policy "<table>_insert_own"
  on public.<table_name>
  for insert
  to authenticated
  with check (user_id = auth.uid());

-- Owner can update own data
create policy "<table>_update_own"
  on public.<table_name>
  for update
  to authenticated
  using (user_id = auth.uid())
  with check (user_id = auth.uid());

-- Owner can delete own data
create policy "<table>_delete_own"
  on public.<table_name>
  for delete
  to authenticated
  using (user_id = auth.uid());
```

#### Role-Based（基于角色）

```sql
-- Create roles enum
create type public.app_role as enum ('admin', 'editor', 'viewer');

-- User roles table
create table public.user_roles (
  id uuid primary key default gen_random_uuid(),
  user_id uuid not null references auth.users(id) on delete cascade,
  role public.app_role not null default 'viewer',
  unique(user_id)
);

-- Helper function
create or replace function public.get_user_role()
returns public.app_role as $$
  select role from public.user_roles where user_id = auth.uid();
$$ language sql security definer stable;

-- Admin: full access
create policy "<table>_all_admin"
  on public.<table_name>
  for all
  to authenticated
  using (public.get_user_role() = 'admin')
  with check (public.get_user_role() = 'admin');

-- Editor: read (select)
create policy "<table>_select_editor"
  on public.<table_name>
  for select
  to authenticated
  using (public.get_user_role() in ('admin', 'editor'));

-- Editor: insert
create policy "<table>_insert_editor"
  on public.<table_name>
  for insert
  to authenticated
  with check (public.get_user_role() in ('admin', 'editor'));

-- Editor: update (no delete)
create policy "<table>_update_editor"
  on public.<table_name>
  for update
  to authenticated
  using (public.get_user_role() in ('admin', 'editor'))
  with check (public.get_user_role() in ('admin', 'editor'));

-- Viewer: read only
create policy "<table>_select_viewer"
  on public.<table_name>
  for select
  to authenticated
  using (public.get_user_role() in ('admin', 'editor', 'viewer'));
```

#### Org-Based（组织级多租户）

```sql
-- Organizations table
create table public.organizations (
  id uuid primary key default gen_random_uuid(),
  name text not null,
  slug text not null unique,
  created_at timestamptz not null default now()
);

-- Organization members
create table public.org_members (
  id uuid primary key default gen_random_uuid(),
  org_id uuid not null references public.organizations(id) on delete cascade,
  user_id uuid not null references auth.users(id) on delete cascade,
  role public.app_role not null default 'viewer',
  unique(org_id, user_id)
);

-- Helper function: check org membership
create or replace function public.is_org_member(org_id uuid)
returns boolean as $$
  select exists (
    select 1 from public.org_members
    where org_members.org_id = is_org_member.org_id
    and user_id = auth.uid()
  );
$$ language sql security definer stable;

-- Helper function: check org role
create or replace function public.get_org_role(org_id uuid)
returns public.app_role as $$
  select role from public.org_members
  where org_members.org_id = get_org_role.org_id
  and user_id = auth.uid();
$$ language sql security definer stable;

-- Org members can read
create policy "<table>_org_select"
  on public.<table_name>
  for select
  to authenticated
  using (public.is_org_member(org_id));

-- Org admins/editors can insert
create policy "<table>_org_insert"
  on public.<table_name>
  for insert
  to authenticated
  with check (
    public.get_org_role(org_id) in ('admin', 'editor')
  );

-- Org admins/editors can update
create policy "<table>_org_update"
  on public.<table_name>
  for update
  to authenticated
  using (public.get_org_role(org_id) in ('admin', 'editor'))
  with check (public.get_org_role(org_id) in ('admin', 'editor'));

-- Org admins can delete
create policy "<table>_org_delete"
  on public.<table_name>
  for delete
  to authenticated
  using (public.get_org_role(org_id) = 'admin');
```

### 2.3 多对多中间表模板

```sql
create table public.<table_a>_<table_b> (
  id uuid primary key default gen_random_uuid(),
  <table_a>_id uuid not null references public.<table_a>(id) on delete cascade,
  <table_b>_id uuid not null references public.<table_b>(id) on delete cascade,
  created_at timestamptz not null default now(),
  unique(<table_a>_id, <table_b>_id)
);

-- Indexes for join performance
create index idx_<table_a>_<table_b>_a on public.<table_a>_<table_b>(<table_a>_id);
create index idx_<table_a>_<table_b>_b on public.<table_a>_<table_b>(<table_b>_id);

-- RLS: junction tables do NOT inherit policies from parent tables — explicit policies required
alter table public.<table_a>_<table_b> enable row level security;

-- Read: user can see links where they own the parent record
create policy "<a>_<b>_select_own"
  on public.<table_a>_<table_b>
  for select
  to authenticated
  using (
    exists (select 1 from public.<table_a> where id = <table_a>_id and user_id = auth.uid())
  );

-- Create: user can link if they own the parent record
create policy "<a>_<b>_insert_own"
  on public.<table_a>_<table_b>
  for insert
  to authenticated
  with check (
    exists (select 1 from public.<table_a> where id = <table_a>_id and user_id = auth.uid())
  );

-- Delete: user can unlink if they own the parent record
create policy "<a>_<b>_delete_own"
  on public.<table_a>_<table_b>
  for delete
  to authenticated
  using (
    exists (select 1 from public.<table_a> where id = <table_a>_id and user_id = auth.uid())
  );
```

---

## 第三步：TypeScript 类型生成

### 3.1 Supabase Database 类型格式

```typescript
// src/types/database.types.ts

export type Json =
  | string
  | number
  | boolean
  | null
  | { [key: string]: Json | undefined }
  | Json[]

export type Database = {
  public: {
    Tables: {
      <table_name>: {
        Row: {
          id: string
          user_id: string
          title: string
          description: string | null
          status: Database['public']['Enums']['<enum_name>']
          created_at: string
          updated_at: string
        }
        Insert: {
          id?: string
          user_id: string
          title: string
          description?: string | null
          status?: Database['public']['Enums']['<enum_name>']
          created_at?: string
          updated_at?: string
        }
        Update: {
          id?: string
          user_id?: string
          title?: string
          description?: string | null
          status?: Database['public']['Enums']['<enum_name>']
          created_at?: string
          updated_at?: string
        }
        Relationships: [
          {
            foreignKeyName: '<table_name>_user_id_fkey'
            columns: ['user_id']
            isOneToOne: false
            referencedRelation: 'users'
            referencedColumns: ['id']
          }
        ]
      }
    }
    Enums: {
      <enum_name>: 'value1' | 'value2' | 'value3'
    }
  }
}

// Convenience types
export type Tables<T extends keyof Database['public']['Tables']> =
  Database['public']['Tables'][T]['Row']
export type InsertTables<T extends keyof Database['public']['Tables']> =
  Database['public']['Tables'][T]['Insert']
export type UpdateTables<T extends keyof Database['public']['Tables']> =
  Database['public']['Tables'][T]['Update']
export type Enums<T extends keyof Database['public']['Enums']> =
  Database['public']['Enums'][T]
```

### 3.2 类型映射规则

| PostgreSQL | TypeScript |
|-----------|-----------|
| `uuid` | `string` |
| `text` | `string` |
| `integer` / `bigint` | `number` |
| `numeric` | `number` |
| `boolean` | `boolean` |
| `timestamptz` / `timestamp` | `string` |
| `date` | `string` |
| `jsonb` | `Json` |
| `enum` | 字面量联合类型 |
| `text[]` / `integer[]` | `string[]` / `number[]` |
| `point` | `{ x: number; y: number }` 或 `string`（Supabase 返回 `"(x,y)"` 格式字符串） |
| `interval` | `string`（如 `"2 hours"`、`"P1D"`） |
| `inet` | `string` |
| `int4range` / `tstzrange` | `string`（如 `"[1,10)"`）或自定义 `{ start: T; end: T }` |
| `bytea` | `string`（Base64 编码） |
| 可空字段 | `T \| null` |
| 有默认值的字段 | Insert 中标记为可选 `?` |

---

## 第四步：Next.js App Router API Routes 生成

### 4.1 Supabase Client 初始化

```typescript
// src/lib/supabase/server.ts
import { createServerClient } from '@supabase/ssr'
import { cookies } from 'next/headers'
import type { Database } from '@/types/database.types'

export async function createClient() {
  const cookieStore = await cookies()

  return createServerClient<Database>(
    process.env.NEXT_PUBLIC_SUPABASE_URL!,
    process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!,
    {
      cookies: {
        getAll() {
          return cookieStore.getAll()
        },
        setAll(cookiesToSet) {
          try {
            cookiesToSet.forEach(({ name, value, options }) =>
              cookieStore.set(name, value, options)
            )
          } catch {
            // Ignore in Server Components
          }
        },
      },
    }
  )
}
```

```typescript
// src/lib/supabase/client.ts
import { createBrowserClient } from '@supabase/ssr'
import type { Database } from '@/types/database.types'

export function createClient() {
  return createBrowserClient<Database>(
    process.env.NEXT_PUBLIC_SUPABASE_URL!,
    process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!
  )
}
```

### 4.2 CRUD API Route 模板

```typescript
// src/app/api/<table_name>/route.ts
import { NextRequest, NextResponse } from 'next/server'
import { z } from 'zod'
import { createClient } from '@/lib/supabase/server'
import { create<Entity>Schema, update<Entity>Schema } from '@/lib/validations/<table_name>'

// GET - List all (with pagination)
export async function GET(request: NextRequest) {
  try {
    const supabase = await createClient()
    const { data: { user }, error: authError } = await supabase.auth.getUser()

    if (authError || !user) {
      return NextResponse.json(
        { success: false, error: 'Unauthorized', hint: 'Please sign in to access this resource. If your session expired, try refreshing your login.' },
        { status: 401 }
      )
    }

    const searchParams = request.nextUrl.searchParams
    const page = Math.max(1, parseInt(searchParams.get('page') ?? '1', 10))
    const limit = Math.min(100, Math.max(1, parseInt(searchParams.get('limit') ?? '20', 10)))
    const offset = (page - 1) * limit

    // ⚠️ N+1 查询警告：`.select('*')` 在有大量关联表时可能导致性能问题。
    // 建议：指定具体字段如 `.select('id, title, status, created_at')`，
    // 关联查询用 `.select('id, title, category:categories(id, name)')` 替代多次查询。
    const { data, error, count } = await supabase
      .from('<table_name>')
      .select('*', { count: 'exact' })
      .range(offset, offset + limit - 1)
      .order('created_at', { ascending: false })

    if (error) {
      return NextResponse.json(
        { success: false, error: error.message },
        { status: 400 }
      )
    }

    return NextResponse.json({
      success: true,
      data,
      meta: { total: count ?? 0, page, limit },
    })
  } catch (error) {
    return NextResponse.json(
      { success: false, error: 'Internal server error' },
      { status: 500 }
    )
  }
}

// POST - Create
export async function POST(request: NextRequest) {
  try {
    const supabase = await createClient()
    const { data: { user }, error: authError } = await supabase.auth.getUser()

    if (authError || !user) {
      return NextResponse.json(
        { success: false, error: 'Unauthorized', hint: 'Please sign in to access this resource. If your session expired, try refreshing your login.' },
        { status: 401 }
      )
    }

    let body: unknown
    try {
      body = await request.json()
    } catch {
      return NextResponse.json(
        { success: false, error: 'Invalid JSON in request body' },
        { status: 400 }
      )
    }

    const validated = create<Entity>Schema.parse(body)

    const { data, error } = await supabase
      .from('<table_name>')
      .insert({ ...validated, user_id: user.id })
      .select()
      .single()

    if (error) {
      return NextResponse.json(
        { success: false, error: error.message },
        { status: 400 }
      )
    }

    return NextResponse.json({ success: true, data }, { status: 201 })
  } catch (error) {
    if (error instanceof z.ZodError) {
      return NextResponse.json(
        { success: false, error: 'Validation failed', details: error.errors },
        { status: 422 }
      )
    }
    return NextResponse.json(
      { success: false, error: 'Internal server error' },
      { status: 500 }
    )
  }
}
```

```typescript
// src/app/api/<table_name>/[id]/route.ts
import { NextRequest, NextResponse } from 'next/server'
import { z } from 'zod'
import { createClient } from '@/lib/supabase/server'
import { update<Entity>Schema } from '@/lib/validations/<table_name>'

type Params = { params: Promise<{ id: string }> }

// GET - Read single
export async function GET(request: NextRequest, { params }: Params) {
  try {
    const { id } = await params
    const supabase = await createClient()
    const { data: { user }, error: authError } = await supabase.auth.getUser()

    if (authError || !user) {
      return NextResponse.json(
        { success: false, error: 'Unauthorized', hint: 'Please sign in to access this resource. If your session expired, try refreshing your login.' },
        { status: 401 }
      )
    }

    // ⚠️ 生产环境建议指定具体字段替代 '*'，减少不必要的数据传输
    const { data, error } = await supabase
      .from('<table_name>')
      .select('*')
      .eq('id', id)
      .single()

    if (error) {
      return NextResponse.json(
        { success: false, error: error.message },
        { status: 404 }
      )
    }

    return NextResponse.json({ success: true, data })
  } catch (error) {
    return NextResponse.json(
      { success: false, error: 'Internal server error' },
      { status: 500 }
    )
  }
}

// PUT - Update
export async function PUT(request: NextRequest, { params }: Params) {
  try {
    const { id } = await params
    const supabase = await createClient()
    const { data: { user }, error: authError } = await supabase.auth.getUser()

    if (authError || !user) {
      return NextResponse.json(
        { success: false, error: 'Unauthorized', hint: 'Please sign in to access this resource. If your session expired, try refreshing your login.' },
        { status: 401 }
      )
    }

    let body: unknown
    try {
      body = await request.json()
    } catch {
      return NextResponse.json(
        { success: false, error: 'Invalid JSON in request body' },
        { status: 400 }
      )
    }

    const validated = update<Entity>Schema.parse(body)

    const { data, error } = await supabase
      .from('<table_name>')
      .update(validated)
      .eq('id', id)
      .select()
      .single()

    if (error) {
      return NextResponse.json(
        { success: false, error: error.message },
        { status: 400 }
      )
    }

    return NextResponse.json({ success: true, data })
  } catch (error) {
    if (error instanceof z.ZodError) {
      return NextResponse.json(
        { success: false, error: 'Validation failed', details: error.errors },
        { status: 422 }
      )
    }
    return NextResponse.json(
      { success: false, error: 'Internal server error' },
      { status: 500 }
    )
  }
}

// DELETE
export async function DELETE(request: NextRequest, { params }: Params) {
  try {
    const { id } = await params
    const supabase = await createClient()
    const { data: { user }, error: authError } = await supabase.auth.getUser()

    if (authError || !user) {
      return NextResponse.json(
        { success: false, error: 'Unauthorized', hint: 'Please sign in to access this resource. If your session expired, try refreshing your login.' },
        { status: 401 }
      )
    }

    const { error } = await supabase
      .from('<table_name>')
      .delete()
      .eq('id', id)

    if (error) {
      return NextResponse.json(
        { success: false, error: error.message },
        { status: 400 }
      )
    }

    return NextResponse.json({ success: true }, { status: 200 })
  } catch (error) {
    return NextResponse.json(
      { success: false, error: 'Internal server error' },
      { status: 500 }
    )
  }
}
```

---

## 第五步：Zod Validation Schema 生成

### 5.1 Schema 生成规则

```typescript
// src/lib/validations/<table_name>.ts
import { z } from 'zod'

// Create schema - exclude id, user_id, timestamps (server-generated)
export const create<Entity>Schema = z.object({
  title: z.string().min(1, 'Title is required').max(255),
  description: z.string().max(5000).nullable().optional(),
  status: z.enum(['value1', 'value2', 'value3']).default('value1'),
  // Foreign keys provided by client
  category_id: z.string().uuid('Invalid category ID').optional(),
})

// Update schema - all fields optional
export const update<Entity>Schema = create<Entity>Schema.partial()

// Query params schema
export const list<Entity>QuerySchema = z.object({
  page: z.coerce.number().int().min(1).default(1),
  limit: z.coerce.number().int().min(1).max(100).default(20),
  status: z.enum(['value1', 'value2', 'value3']).optional(),
  search: z.string().max(100).optional(),
  sort_by: z.enum(['created_at', 'updated_at', 'title']).default('created_at'),
  sort_order: z.enum(['asc', 'desc']).default('desc'),
})

// `.default()` vs `.optional()` 使用规则：
// - `.default('value')` — 字段缺失时自动填充默认值，parse 后一定有值。
//   适用场景：状态字段（如 status）、排序方式、分页参数等有合理默认值的字段。
// - `.optional()` — 字段可以缺失，parse 后值为 undefined。
//   适用场景：描述、备注等非必填且无默认值的字段。
// - `.nullable().optional()` — 字段可以缺失或显式传 null。
//   适用场景：对应数据库中可空（nullable）且无默认值的列。
// - 不要同时使用 `.default().optional()`，这会导致 default 永远不生效。

// Type inference
export type Create<Entity>Input = z.infer<typeof create<Entity>Schema>
export type Update<Entity>Input = z.infer<typeof update<Entity>Schema>
export type List<Entity>Query = z.infer<typeof list<Entity>QuerySchema>
```

### 5.2 类型映射：PostgreSQL → Zod

| PostgreSQL | Zod |
|-----------|-----|
| `text not null` | `z.string().min(1)` |
| `text` (nullable) | `z.string().nullable().optional()` |
| `integer` | `z.number().int()` |
| `numeric(10,2)` | `z.number().min(0)` |
| `boolean` | `z.boolean()` |
| `uuid` | `z.string().uuid()` |
| `timestamptz` | `z.string().datetime()` |
| `date` | `z.string().date()` |
| `jsonb` | `z.record(z.unknown())` 或自定义 schema |
| `enum` | `z.enum([...values])` |
| `text[]` | `z.array(z.string())` |
| `integer[]` | `z.array(z.number().int())` |
| `point` | `z.string().regex(/^\([-\d.]+,[-\d.]+\)$/)` 或自定义 `z.object({ x: z.number(), y: z.number() })` |
| `interval` | `z.string()` |
| `inet` | `z.string().ip()` |
| `int4range` | `z.string().regex(/^[\[(][-\d]*,[-\d]*[\])]$/)` |
| `bytea` | `z.string()` |

---

## 第六步：Auth 配置生成

### 6.1 邮箱密码认证

```typescript
// src/lib/auth/email.ts
// ⚠️ BROWSER ONLY - 仅在客户端组件中调用
// 不要在 Server Components、API Routes 或 Middleware 中使用此函数
// 服务端认证请使用 createServerClient
import { createClient } from '@/lib/supabase/client'

export async function signUpWithEmail(email: string, password: string) {
  const supabase = createClient()
  const { data, error } = await supabase.auth.signUp({
    email,
    password,
    options: {
      emailRedirectTo: `${window.location.origin}/auth/callback`,
    },
  })

  if (error) throw new Error(error.message)
  return data
}

export async function signInWithEmail(email: string, password: string) {
  const supabase = createClient()
  const { data, error } = await supabase.auth.signInWithPassword({
    email,
    password,
  })

  if (error) throw new Error(error.message)
  return data
}

export async function signOut() {
  const supabase = createClient()
  const { error } = await supabase.auth.signOut()
  if (error) throw new Error(error.message)
}
```

### 6.2 OAuth 认证

```typescript
// src/lib/auth/oauth.ts
import { createClient } from '@/lib/supabase/client'
import type { Provider } from '@supabase/supabase-js'

export async function signInWithOAuth(provider: Provider) {
  const supabase = createClient()
  const { data, error } = await supabase.auth.signInWithOAuth({
    provider,
    options: {
      redirectTo: `${window.location.origin}/auth/callback`,
    },
  })

  if (error) throw new Error(error.message)
  return data
}
```

### 6.3 Magic Link 认证

```typescript
// src/lib/auth/magic-link.ts
import { createClient } from '@/lib/supabase/client'

export async function signInWithMagicLink(email: string) {
  const supabase = createClient()
  const { data, error } = await supabase.auth.signInWithOtp({
    email,
    options: {
      emailRedirectTo: `${window.location.origin}/auth/callback`,
    },
  })

  if (error) throw new Error(error.message)
  return data
}
```

### 6.4 Auth Callback Route

```typescript
// src/app/auth/callback/route.ts
import { NextRequest, NextResponse } from 'next/server'
import { createClient } from '@/lib/supabase/server'

export async function GET(request: NextRequest) {
  const { searchParams, origin } = new URL(request.url)
  const code = searchParams.get('code')
  const next = searchParams.get('next') ?? '/'

  if (code) {
    const supabase = await createClient()
    const { error } = await supabase.auth.exchangeCodeForSession(code)

    if (!error) {
      return NextResponse.redirect(`${origin}${next}`)
    }
  }

  return NextResponse.redirect(`${origin}/auth/error`)
}
```

### 6.5 Auth Middleware

```typescript
// src/middleware.ts
import { NextResponse, type NextRequest } from 'next/server'
import { createServerClient } from '@supabase/ssr'

export async function middleware(request: NextRequest) {
  let supabaseResponse = NextResponse.next({ request })

  const supabase = createServerClient(
    process.env.NEXT_PUBLIC_SUPABASE_URL!,
    process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!,
    {
      cookies: {
        getAll() {
          return request.cookies.getAll()
        },
        setAll(cookiesToSet) {
          cookiesToSet.forEach(({ name, value }) =>
            request.cookies.set(name, value)
          )
          supabaseResponse = NextResponse.next({ request })
          cookiesToSet.forEach(({ name, value, options }) =>
            supabaseResponse.cookies.set(name, value, options)
          )
        },
      },
    }
  )

  // ⚠️ getUser() 可能失效的场景：
  // 1. JWT 过期且 refresh token 也失效 — 用户需要重新登录
  // 2. 用户在 Supabase Dashboard 中被手动删除/禁用 — getUser() 返回 null
  // 3. Supabase 服务不可用（网络问题/服务宕机）— 会抛出异常
  // 4. Cookie 被清除或被第三方拦截（Safari ITP 等）— 返回 null
  // 处理方式：对所有非预期情况统一重定向到登录页，不要暴露具体错误原因
  const { data: { user } } = await supabase.auth.getUser()

  // Redirect unauthenticated users to login
  if (
    !user &&
    !request.nextUrl.pathname.startsWith('/auth') &&
    !request.nextUrl.pathname.startsWith('/api/public')
  ) {
    const url = request.nextUrl.clone()
    url.pathname = '/auth/login'
    return NextResponse.redirect(url)
  }

  return supabaseResponse
}

export const config = {
  matcher: [
    '/((?!_next/static|_next/image|favicon.ico|.*\\.(?:svg|png|jpg|jpeg|gif|webp)$).*)',
  ],
}
```

---

## 第七步：React 表单组件生成

### 7.1 基于 Zod Schema 的表单模板

```tsx
// src/components/forms/<entity>-form.tsx
'use client'

import { useForm } from 'react-hook-form'
import { zodResolver } from '@hookform/resolvers/zod'
import {
  create<Entity>Schema,
  type Create<Entity>Input,
} from '@/lib/validations/<table_name>'

interface <Entity>FormProps {
  defaultValues?: Partial<Create<Entity>Input>
  onSubmit: (data: Create<Entity>Input) => Promise<void>
  isLoading?: boolean
}

export function <Entity>Form({
  defaultValues,
  onSubmit,
  isLoading = false,
}: <Entity>FormProps) {
  const {
    register,
    handleSubmit,
    formState: { errors },
  } = useForm<Create<Entity>Input>({
    resolver: zodResolver(create<Entity>Schema),
    defaultValues,
  })

  return (
    <form onSubmit={handleSubmit(onSubmit)} className="space-y-4">
      {/* Text field */}
      <div>
        <label htmlFor="title" className="block text-sm font-medium">
          Title
        </label>
        <input
          id="title"
          type="text"
          {...register('title')}
          className="mt-1 block w-full rounded-md border px-3 py-2"
          disabled={isLoading}
        />
        {errors.title && (
          <p className="mt-1 text-sm text-red-600">{errors.title.message}</p>
        )}
      </div>

      {/* Textarea field */}
      <div>
        <label htmlFor="description" className="block text-sm font-medium">
          Description
        </label>
        <textarea
          id="description"
          {...register('description')}
          rows={4}
          className="mt-1 block w-full rounded-md border px-3 py-2"
          disabled={isLoading}
        />
        {errors.description && (
          <p className="mt-1 text-sm text-red-600">
            {errors.description.message}
          </p>
        )}
      </div>

      {/* Select/Enum field */}
      <div>
        <label htmlFor="status" className="block text-sm font-medium">
          Status
        </label>
        <select
          id="status"
          {...register('status')}
          className="mt-1 block w-full rounded-md border px-3 py-2"
          disabled={isLoading}
        >
          <option value="value1">Value 1</option>
          <option value="value2">Value 2</option>
          <option value="value3">Value 3</option>
        </select>
        {errors.status && (
          <p className="mt-1 text-sm text-red-600">{errors.status.message}</p>
        )}
      </div>

      <button
        type="submit"
        disabled={isLoading}
        className="rounded-md bg-blue-600 px-4 py-2 text-white hover:bg-blue-700 disabled:opacity-50"
      >
        {isLoading ? 'Saving...' : 'Save'}
      </button>
    </form>
  )
}
```

---

## 第八步：实时订阅（可选）

如果需求中包含实时更新（如聊天、通知、协作编辑），生成以下代码：

```typescript
// src/hooks/use-realtime.ts
'use client'

import { useEffect } from 'react'
import { createClient } from '@/lib/supabase/client'
import type { RealtimeChannel } from '@supabase/supabase-js'

export function useRealtime<T extends Record<string, unknown>>(
  table: string,
  onInsert?: (payload: T) => void,
  onUpdate?: (payload: T) => void,
  onDelete?: (payload: { id: string }) => void
) {
  useEffect(() => {
    const supabase = createClient()
    const channel: RealtimeChannel = supabase
      .channel(`${table}-changes`)
      .on(
        'postgres_changes',
        { event: 'INSERT', schema: 'public', table },
        (payload) => onInsert?.(payload.new as T)
      )
      .on(
        'postgres_changes',
        { event: 'UPDATE', schema: 'public', table },
        (payload) => onUpdate?.(payload.new as T)
      )
      .on(
        'postgres_changes',
        { event: 'DELETE', schema: 'public', table },
        (payload) => onDelete?.(payload.old as { id: string })
      )
      .subscribe()

    return () => {
      supabase.removeChannel(channel)
    }
  }, [table, onInsert, onUpdate, onDelete])
}
```

> ⚠️ Realtime 需要在 Supabase Dashboard 中为目标表启用 Replication。

---

## 常见 Supabase 陷阱提醒

生成代码时，始终在注释或文档中包含以下警告：

| 陷阱 | 严重性 | 说明 |
|------|-------|------|
| RLS 忘记开启 | **致命** | 新建表默认不开启 RLS，任何人都能读写。必须 `alter table ... enable row level security` |
| service_role key 泄漏到客户端 | **致命** | `service_role` key 绕过所有 RLS，绝对不能暴露给浏览器。只在服务端使用。**自动检测建议**：① 添加 ESLint 规则 `no-restricted-syntax` 禁止在 `src/app`、`src/components` 等客户端目录引用 `SUPABASE_SERVICE_ROLE_KEY`；② 在 CI 中运行 `grep -r "SUPABASE_SERVICE_ROLE_KEY" src/app src/components src/hooks --include="*.ts" --include="*.tsx"` 如有匹配则阻断构建；③ 使用 `secretlint` 或 `gitleaks` 扫描整个仓库 |
| anon key 不等于安全 | **高** | `anon` key 虽然是公开的，但必须配合正确的 RLS 策略才安全 |
| RLS 策略遗漏 DELETE | **高** | 常见错误：只写了 SELECT/INSERT/UPDATE 策略，忘了 DELETE |
| 忘记给中间表加 RLS | **高** | 多对多关联表也需要独立的 RLS 策略 |
| `using` vs `with check` 混淆 | **中** | `using` 控制读取/删除，`with check` 控制写入验证。UPDATE 需要同时设置两者 |
| 时间戳不带时区 | **中** | 始终使用 `timestamptz`，不要用 `timestamp` |
| 缺少索引 | **中** | 外键列、经常查询的列必须建索引 |
| `supabase.auth.getSession()` 不安全 | **中** | 在 Server Component 中用 `getUser()` 代替 `getSession()`，后者不会验证 JWT |
| Storage bucket 权限 | **中** | Storage bucket 默认私有，需要单独配置 RLS 策略 |
| 递归 RLS 策略 | **低** | 如果策略查询了另一个也有 RLS 的表，可能导致无限递归。使用 `security definer` 函数解决 |

---

## 质量检查清单

生成代码完成后，逐项检查：

### SQL Migration
- [ ] 所有表都启用了 RLS（`enable row level security`）
- [ ] 每个表都有完整的 CRUD 策略（SELECT / INSERT / UPDATE / DELETE）
- [ ] 外键列都有索引
- [ ] 使用 `timestamptz` 而非 `timestamp`
- [ ] 使用 `text` 而非 `varchar`
- [ ] 金额字段使用 `numeric` 而非 `float`
- [ ] `updated_at` 触发器已创建
- [ ] 枚举类型使用 PostgreSQL `create type` 定义
- [ ] 中间表有复合唯一约束
- [ ] `on delete cascade` 设置合理（不会级联删除不该删的数据）

### TypeScript 类型
- [ ] Row / Insert / Update 三种类型都已定义
- [ ] 可空字段标记为 `T | null`
- [ ] 有默认值的字段在 Insert 中标记为可选
- [ ] Relationships 数组正确描述了外键关系
- [ ] 便捷类型（Tables, InsertTables, UpdateTables）已导出

### API Routes
- [ ] 所有路由都先验证认证状态（`getUser()`）
- [ ] 使用 Zod 验证请求体
- [ ] 错误响应格式一致（`{ success, error }`）
- [ ] 分页参数有默认值和上限
- [ ] 没有使用 `service_role` key

### Auth
- [ ] `emailRedirectTo` 配置正确
- [ ] Auth callback route 处理了错误情况
- [ ] Middleware 正确刷新了 session
- [ ] 公开路由（/auth/*）不被 middleware 拦截

### Zod Schema
- [ ] Create schema 排除了服务端生成的字段（id, user_id, timestamps）
- [ ] Update schema 是 Create schema 的 `.partial()`
- [ ] 字符串字段有 min/max 限制
- [ ] 数字字段有合理的范围限制
- [ ] 枚举值与 PostgreSQL enum 一致

### 安全
- [ ] `service_role` key 只在服务端 Admin 操作中使用
- [ ] 环境变量文件（`.env.local`）在 `.gitignore` 中
- [ ] RLS 策略覆盖所有操作（不存在无策略的"漏洞"）
- [ ] `security definer` 函数只在必要时使用
- [ ] 没有在客户端暴露敏感信息

---

## 环境变量模板

生成项目时，始终包含 `.env.local.example`：

```bash
# ⚠️ CRITICAL SECURITY CHECKLIST:
# 1. 确保 .env.local 已添加到 .gitignore
# 2. NEVER commit .env.local to version control
# 3. SUPABASE_SERVICE_ROLE_KEY 仅用于服务端，绝不能暴露到客户端
# 4. NEXT_PUBLIC_* 变量会暴露到浏览器，不要放置任何密钥

# Supabase
NEXT_PUBLIC_SUPABASE_URL=https://your-project.supabase.co
NEXT_PUBLIC_SUPABASE_ANON_KEY=your-anon-key

# Only for server-side admin operations (NEVER expose to client)
SUPABASE_SERVICE_ROLE_KEY=your-service-role-key

# OAuth providers (if using)
# Configure in Supabase Dashboard > Authentication > Providers
```

---

## 第十步：验证与测试

生成代码后，按以下步骤验证所有组件是否正常工作：

### 10.1 本地 Supabase 启动

```bash
# 安装 Supabase CLI（如未安装）
brew install supabase/tap/supabase

# 初始化并启动本地 Supabase 实例
supabase init  # 仅首次
supabase start

# 启动后会输出本地 URL 和 key，将其写入 .env.local
# API URL:   http://127.0.0.1:54321
# anon key:  eyJ...
# service_role key: eyJ...
```

### 10.2 迁移执行

```bash
# 执行所有待运行的 migration
supabase db reset

# 验证表结构
supabase db lint
```

### 10.3 RLS 策略测试

```bash
# 使用 psql 连接本地数据库
psql "postgresql://postgres:postgres@127.0.0.1:54322/postgres"
```

```sql
-- 1. 验证 RLS 已启用
select tablename, rowsecurity
from pg_tables
where schemaname = 'public';

-- 2. 以 anon 角色测试（应被拒绝）
set role anon;
select * from public.<table_name>;  -- 预期：0 行或报错
reset role;

-- 3. 以 authenticated 角色模拟特定用户
set role authenticated;
set request.jwt.claims = '{"sub": "<test-user-uuid>"}';
select * from public.<table_name>;  -- 预期：仅返回该用户的数据
reset role;

-- 4. 测试写入策略
set role authenticated;
set request.jwt.claims = '{"sub": "<test-user-uuid>"}';
insert into public.<table_name> (user_id, title) values ('<other-user-uuid>', 'hack');  -- 预期：被 RLS 拦截
reset role;
```

### 10.4 API 端点测试

```bash
# 确保 Next.js 开发服务器已启动
bun run dev

# 测试未认证请求（预期 401）
curl -s http://localhost:3000/api/<table_name> | jq

# 测试认证请求（使用从 Supabase 获取的 JWT）
TOKEN="<your-jwt-token>"

# GET - 列表
curl -s -H "Authorization: Bearer $TOKEN" \
  http://localhost:3000/api/<table_name> | jq

# POST - 创建
curl -s -X POST \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"title": "Test item"}' \
  http://localhost:3000/api/<table_name> | jq

# PUT - 更新
curl -s -X PUT \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"title": "Updated item"}' \
  http://localhost:3000/api/<table_name>/<item-id> | jq

# DELETE - 删除
curl -s -X DELETE \
  -H "Authorization: Bearer $TOKEN" \
  http://localhost:3000/api/<table_name>/<item-id> | jq

# 测试非法 JSON（预期 400）
curl -s -X POST \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d 'not-json' \
  http://localhost:3000/api/<table_name> | jq

# 测试验证失败（预期 422）
curl -s -X POST \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{}' \
  http://localhost:3000/api/<table_name> | jq
```

### 10.5 验证清单

- [ ] `supabase db reset` 无报错，所有 migration 执行成功
- [ ] 所有表的 RLS 已启用（`rowsecurity = true`）
- [ ] 未认证请求返回 401 并包含 `hint` 字段
- [ ] 认证用户只能访问自己的数据
- [ ] 跨用户写入被 RLS 拦截
- [ ] 非法 JSON 返回 400（非 500）
- [ ] Zod 验证失败返回 422 及具体错误详情
- [ ] 分页参数边界值正常（page=0、limit=-1、limit=999）

---

## 执行流程总结

1. **分析** → 从自然语言提取实体、属性、关系、所有权模型
2. **Migration** → 生成 SQL（表 + 索引 + 触发器 + RLS）
3. **类型** → 生成 TypeScript Database 类型
4. **验证** → 生成 Zod schema
5. **API** → 生成 Next.js App Router CRUD routes
6. **Auth** → 根据需求生成认证配置
7. **表单** → 生成 React 表单组件
8. **Realtime** → 如需实时更新，生成 Realtime 订阅 hook（参见「实时订阅」章节）
9. **环境检查** → 自动检查 `.gitignore` 包含 `.env.local`，若不包含则添加
10. **验证与测试** → 本地 Supabase 启动、迁移执行、RLS 测试、API 测试（参见「验证与测试」章节）
11. **检查** → 运行质量检查清单
12. **提醒** → 输出陷阱警告
