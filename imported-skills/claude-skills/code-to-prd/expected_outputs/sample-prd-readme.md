# My App — Product Requirements Document

## System Overview

My App is a user management platform for internal teams. It provides CRUD operations for users, a dashboard with key metrics, and system settings. Built with Next.js 14 (App Router) and Tailwind CSS.

## Module Overview

| Module | Pages | Core Functionality |
|--------|-------|--------------------|
| Dashboard | Dashboard | Key metrics, activity feed |
| User Management | User list, User detail | CRUD users, role assignment |
| Settings | Settings | System configuration |

## Page Inventory

| # | Page Name | Route | Module | Doc Link |
|---|-----------|-------|--------|----------|
| 1 | Home | / | — | [→](./pages/01-home.md) |
| 2 | Dashboard | /dashboard | Dashboard | [→](./pages/02-dashboard.md) |
| 3 | User List | /users | User Mgmt | [→](./pages/03-user-list.md) |
| 4 | User Detail | /users/:id | User Mgmt | [→](./pages/04-user-detail.md) |
| 5 | Settings | /settings | Settings | [→](./pages/05-settings.md) |

## API Inventory

| # | Method | Path | Status | Notes |
|---|--------|------|--------|-------|
| 1 | GET | /api/users | Integrated | Paginated list |
| 2 | POST | /api/users | Integrated | Create user |
| 3 | GET | /api/users/:id | Integrated | User detail |
| 4 | PUT | /api/users/:id | Integrated | Update user |
| 5 | GET | /api/dashboard/stats | Mock | Dashboard metrics |

## Global Notes

### Permission Model
Role-based access: ADMIN (full access), MANAGER (read + edit), USER (read-only).

### Common Interaction Patterns
- All delete operations require confirmation modal
- Lists default to `created_at` descending, 20 items per page
- Form validation shows inline errors below each field
