# Enum Dictionary

All enums, status codes, and constant mappings found in the codebase.

## UserRole

**Source:** `types/user.ts`
**Type:** TypeScript enum

| Value | Label | Description |
|-------|-------|-------------|
| `admin` | Admin | Full system access, can manage all users |
| `manager` | Manager | Can view and edit users, cannot delete |
| `user` | User | Read-only access |

## STATUS_MAP

**Source:** `constants/status.ts`
**Type:** Constant map

| Key | Display Value | Color | Description |
|-----|--------------|-------|-------------|
| `active` | Active | Green | Normal active account |
| `inactive` | Inactive | Gray | Account disabled by user |
| `suspended` | Suspended | Red | Account suspended by admin |
