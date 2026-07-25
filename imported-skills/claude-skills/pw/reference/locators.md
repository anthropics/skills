# Locator Priority

Use the first option that works:

| Priority | Locator | Use for |
|---|---|---|
| 1 | `getByRole('button', { name: 'Submit' })` | Buttons, links, headings, form elements |
| 2 | `getByLabel('Email address')` | Form fields with associated labels |
| 3 | `getByText('Welcome back')` | Non-interactive text content |
| 4 | `getByPlaceholder('Search...')` | Inputs with placeholder text |
| 5 | `getByAltText('Company logo')` | Images with alt text |
| 6 | `getByTitle('Close dialog')` | Elements with title attribute |
| 7 | `getByTestId('checkout-summary')` | When no semantic option exists |
| 8 | `page.locator('.legacy-widget')` | CSS/XPath — absolute last resort |

## Role Locator Cheat Sheet

```typescript
// Buttons — <button>, <input type="submit">, [role="button"]
page.getByRole('button', { name: 'Save changes' })

// Links — <a href>
page.getByRole('link', { name: 'View profile' })

// Headings — h1-h6
page.getByRole('heading', { name: 'Dashboard', level: 1 })

// Text inputs — by label association
page.getByRole('textbox', { name: 'Email' })

// Checkboxes
page.getByRole('checkbox', { name: 'Remember me' })

// Radio buttons
page.getByRole('radio', { name: 'Monthly billing' })

// Dropdowns — <select>
page.getByRole('combobox', { name: 'Country' })

// Navigation
page.getByRole('navigation', { name: 'Main' })

// Tables
page.getByRole('table', { name: 'Recent orders' })

// Rows within tables
page.getByRole('row', { name: /Order #123/ })

// Tab panels
page.getByRole('tab', { name: 'Settings' })

// Dialogs
page.getByRole('dialog', { name: 'Confirm deletion' })

// Alerts
page.getByRole('alert')
```

## Filtering and Chaining

```typescript
// Filter by text
page.getByRole('listitem').filter({ hasText: 'Product A' })

// Filter by child locator
page.getByRole('listitem').filter({
  has: page.getByRole('button', { name: 'Buy' })
})

// Chain locators
page.getByRole('navigation').getByRole('link', { name: 'Settings' })

// Nth match
page.getByRole('listitem').nth(0)
page.getByRole('listitem').first()
page.getByRole('listitem').last()
```
