# Example: Adding a Dropdown to a React App

## User says
```
Add a dropdown to let users select their timezone on the settings page
```

## Pattern Enforcer activates

**Domain detected:** UI

**Scan results:**
```
Found 8 files using <Select> from shadcn/ui:
- src/components/settings/CurrencySelect.tsx
- src/components/profile/RoleSelect.tsx
- src/components/filters/StatusFilter.tsx
...
```

**Assessment:**
> "Found 8 dropdowns using `<Select>` from `@/components/ui/select` (shadcn/ui), consistently using `onValueChange` prop and Tailwind for sizing. Implementing the same way."

## Implementation

```tsx
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue,
} from "@/components/ui/select"

<Select onValueChange={(value) => setTimezone(value)} defaultValue={timezone}>
  <SelectTrigger className="w-[280px]">
    <SelectValue placeholder="Select timezone" />
  </SelectTrigger>
  <SelectContent>
    {timezones.map((tz) => (
      <SelectItem key={tz.value} value={tz.value}>
        {tz.label}
      </SelectItem>
    ))}
  </SelectContent>
</Select>
```

> Used `<Select>` from shadcn/ui — consistent with `CurrencySelect.tsx` and 7 other places.

---

# Example: Multiple Patterns Found

## User says
```
Write a test for the UserService.create method
```

## Pattern Enforcer activates

**Domain detected:** Tests

**Assessment:**
> "Found two test styles:
> 1. Jest + React Testing Library — used in 14 places (`src/**/*.test.tsx`)
> 2. Vitest — used in 3 older places (`src/lib/*.spec.ts`)
>
> Which should I use?"

## User responds
```
Jest
```

## Implementation matches Jest style exactly — same describe/it structure, same mock setup, same assertion style as the 14 existing Jest tests.

---

# Example: No Pattern Found

## User says
```
Add error handling when the payment API fails
```

## Pattern Enforcer activates

**Domain detected:** Error handling

**Assessment:**
> "No existing API error handling found in this codebase — this will be the first.
> Based on your stack (Next.js + TypeScript), the standard approach is a custom `ApiError` class extending `Error` with a `statusCode` field, caught in a top-level error boundary.
> Proceeding with that — this will set the pattern for future use."
