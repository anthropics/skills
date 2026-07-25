# A11y Audit Report — sample-component.tsx

**Scanned:** 1 file | **Issues:** 9 | **Status:** FAIL

## Critical (3)

### 1. Missing alt text on image
- **File:** sample-component.tsx:7
- **Code:** `<img src={user.avatar} />`
- **WCAG:** 1.1.1 Non-text Content (Level A)
- **Fix:** Add descriptive alt text: `<img src={user.avatar} alt={`${user.name}'s avatar`} />`

### 2. Click handler without keyboard support
- **File:** sample-component.tsx:5
- **Code:** `<div className="card" onClick={() => onEdit(user.id)}>`
- **WCAG:** 2.1.1 Keyboard (Level A)
- **Fix:** Use `<button>` or add `role="button"`, `tabIndex={0}`, and `onKeyDown`

### 3. Click handler without keyboard support
- **File:** sample-component.tsx:11
- **Code:** `<div onClick={() => onDelete(user.id)} ...>`
- **WCAG:** 2.1.1 Keyboard (Level A)
- **Fix:** Replace `<div>` with `<button>`

## Serious (4)

### 4. Missing form label
- **File:** sample-component.tsx:15
- **Code:** `<input placeholder="Add note" />`
- **WCAG:** 3.3.2 Labels or Instructions (Level A)
- **Fix:** Add `<label>` or `aria-label="Add note"`

### 5. Empty link
- **File:** sample-component.tsx:14
- **Code:** `<a href="#">Edit</a>`
- **WCAG:** 2.4.4 Link Purpose (Level A)
- **Fix:** Use a real href or replace with `<button>`

### 6. tabindex greater than 0
- **File:** sample-component.tsx:24
- **Code:** `tabIndex={5}`
- **WCAG:** 2.4.3 Focus Order (Level A)
- **Fix:** Use `tabIndex={0}` — positive values disrupt natural tab order

### 7. Missing table headers
- **File:** sample-component.tsx:30
- **Code:** `<td><b>Name</b></td>` (using td+b instead of th)
- **WCAG:** 1.3.1 Info and Relationships (Level A)
- **Fix:** Use `<th scope="col">Name</th>`

## Moderate (2)

### 8. Missing form label
- **File:** sample-component.tsx:22
- **Code:** `<input type="text" placeholder="Search..." />`
- **WCAG:** 3.3.2 Labels or Instructions (Level A)
- **Fix:** Add `aria-label="Search"` or visible label

### 9. Color as sole indicator
- **File:** sample-component.tsx:38
- **Code:** `style={{ color: row.active ? 'green' : 'red' }}`
- **WCAG:** 1.4.1 Use of Color (Level A)
- **Fix:** Add text or icon alongside color: `{row.active ? '✓ Active' : '✗ Inactive'}`
