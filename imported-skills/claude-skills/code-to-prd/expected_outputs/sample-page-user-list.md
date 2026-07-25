# User List

> **Route:** `/users`
> **Module:** User Management
> **Generated:** 2026-03-17

## Overview

Displays all system users in a searchable, paginated table. Supports creating, editing, and deleting users. Only ADMIN and MANAGER roles can access this page.

## Layout

- **Top bar**: Search input + "Create User" button
- **Main area**: Data table with pagination
- **Modal**: Create/Edit user form (triggered by buttons)

## Fields

### Search Filters

| Field | Type | Required | Options | Default | Notes |
|-------|------|----------|---------|---------|-------|
| Keyword | Text input | No | — | — | Searches name and email |
| Role | Select dropdown | No | Admin, Manager, User | All | Filters by role |
| Status | Select dropdown | No | Active, Inactive, Suspended | All | Filters by status |

### Data Table

| Column | Format | Sortable | Filterable | Notes |
|--------|--------|----------|-----------|-------|
| Name | Text | Yes | No | Full name |
| Email | Text (link) | Yes | No | Clickable → opens detail |
| Role | Badge | No | Yes | Color-coded by role |
| Status | Badge | No | Yes | Green=active, Red=suspended |
| Created | Date (YYYY-MM-DD) | Yes | No | — |
| Actions | Buttons | No | No | Edit, Delete |

### Actions

| Button | Visibility | Behavior |
|--------|-----------|----------|
| Create User | ADMIN, MANAGER | Opens create modal |
| Edit | ADMIN, MANAGER | Opens edit modal with prefilled data |
| Delete | ADMIN only | Confirmation dialog → soft delete |

## Interactions

### Page Load
- Fetches first page of users via `GET /api/users?page=1&size=20`
- Default sort: `created_at` descending

### Search
- **Trigger:** User types in search field (300ms debounce)
- **Behavior:** Re-fetches users with `keyword` param, resets to page 1
- **Special rules:** Minimum 2 characters to trigger search

### Create User
- **Trigger:** Click "Create User" button
- **Modal content:** Name (required, max 50), Email (required, email format), Role (required, select), Status (default: Active)
- **Validation:** Name required + max length, Email required + format check
- **API:** `POST /api/users` with form data
- **On success:** Toast "User created", close modal, refresh list
- **On failure:** Show API error below form

### Delete User
- **Trigger:** Click "Delete" button on row
- **Behavior:** Confirmation dialog "Are you sure you want to delete {name}?"
- **API:** `DELETE /api/users/:id`
- **On success:** Toast "User deleted", refresh list

## API Dependencies

| API | Method | Path | Trigger | Notes |
|-----|--------|------|---------|-------|
| List users | GET | /api/users | Load, search, paginate | Params: page, size, keyword, role, status |
| Create user | POST | /api/users | Submit create form | Body: name, email, role |
| Delete user | DELETE | /api/users/:id | Confirm delete | — |

## Page Relationships

- **From:** Dashboard (click "View Users" link)
- **To:** User Detail (click email or row)
- **Data coupling:** Creating/deleting a user triggers dashboard stats refresh
