# E2E Test Selectors: Best Practices & Strategies

> **Reference:** https://bugbug.io/blog/software-testing/data-testid-attributes/

## Selector Hierarchy (Priority Order)

### 1. ✅ data-testid (BEST)

**Why:** Explicit testing API contract, stable, intentional

```typescript
// HTML
<button data-testid="submit-button">Submit</button>
<input data-testid="email-input" type="email" />

// Test
await page.getByTestId('submit-button').click();
await page.getByTestId('email-input').fill('test@example.com');
```

**Advantages:**
- ✅ Explicitly designed for testing
- ✅ Survives CSS/styling changes
- ✅ Survives text content changes
- ✅ Survives HTML structure changes
- ✅ Self-documents test intent
- ✅ Decouples tests from implementation

**Disadvantages:**
- ❌ Requires adding attributes to HTML
- ❌ Team buy-in needed for maintenance

**When to use:** Always, for every interactive element and container

---

### 2. ✅ Accessibility Attributes (GOOD)

**Why:** Semantic, helps accessibility, stable

```typescript
// HTML with proper semantic HTML
<button aria-label="Close modal">×</button>
<form aria-label="Login form">
  <label for="email">Email</label>
  <input id="email" type="email" />
</form>

// Test
await page.getByRole('button', { name: 'Close modal' }).click();
await page.getByLabel('Email').fill('test@example.com');
await page.getByRole('form', { name: 'Login form' }).submit();
```

**Playwright Query Methods:**
```typescript
page.getByRole('button', { name: 'Submit' })
page.getByLabel('Email')
page.getByPlaceholder('Enter text')
page.getByAltText('Product image')
page.getByTitle('Tooltip text')
```

**Advantages:**
- ✅ Improves accessibility
- ✅ Fairly stable
- ✅ Tests user-visible behavior
- ✅ No extra attributes needed (uses semantic HTML)

**Disadvantages:**
- ⚠️ Breaks if text content changes
- ⚠️ Requires proper semantic HTML
- ⚠️ Can be brittle for complex UIs

**When to use:** When semantic HTML is already in place

---

### 3. ⚠️ Text Content (OKAY - Use Carefully)

**Why:** Tests user-visible content, but fragile

```typescript
// HTML
<button>Sign In</button>
<span>Success Message</span>

// Test
await page.getByText('Sign In').click();
await expect(page.getByText('Success Message')).toBeVisible();
```

**Playwright Methods:**
```typescript
page.getByText('Sign In')
page.getByText(/sign in/i)  // Regex for case-insensitive
page.getByText('Sign In', { exact: true })  // Exact match
```

**Advantages:**
- ✅ Easy to read and understand
- ✅ Tests actual user-visible text
- ✅ No special setup needed

**Disadvantages:**
- ❌ Breaks if text changes (even slightly)
- ❌ Internationalization problems (multi-language)
- ❌ Works poorly for dynamic content

**When to use:** Only for very stable, user-visible text

**Example of when to avoid:**
```typescript
// ❌ BAD: Changes when translations update
await page.getByText('Welcome User').click();

// ✅ GOOD: Use data-testid instead
await page.getByTestId('welcome-message').click();
```

---

### 4. ❌ CSS Selectors (AVOID)

**Why:** Brittle, breaks on minor UI changes

```typescript
// ❌ DON'T DO THIS
page.locator('.form-container > div:nth-child(3) input[type="email"]')
page.locator('[class*="btn"][class*="primary"]')
page.locator('div.wrapper div.content input:first-of-type')
```

**Problems:**
- ❌ Breaks when CSS classes change
- ❌ Breaks when HTML structure changes
- ❌ Hard to understand intent
- ❌ Tightly coupled to implementation

**Example of brittleness:**
```typescript
// Original HTML
<form class="form-container">
  <div class="form-group">
    <input type="email" />
  </div>
</form>

// CSS Selector
page.locator('.form-container .form-group input')

// After CSS refactor (selector BREAKS)
<form class="auth-form">  // Class name changed
  <fieldset>
    <input type="email" />
  </fieldset>
</form>

// Test still works (CSS doesn't care about class):
page.locator('.form-container .form-group input')  // ❌ FAILS!

// With data-testid (SURVIVES):
<input data-testid="email-input" type="email" />
page.getByTestId('email-input')  // ✅ Still works!
```

**When it might be okay:**
- Only for very stable, structural selectors
- Use `getByRole()` instead of CSS
- Never use for dynamic content

---

### 5. ❌ XPath (AVOID UNLESS NECESSARY)

**Why:** Complex, fragile, slow

```typescript
// ❌ DON'T DO THIS
page.locator('xpath=//button[contains(text(), "Submit")]')
page.locator('xpath=//*[@id="root"]//div[3]//button[1]')
```

**Problems:**
- ❌ Hardest to read and maintain
- ❌ Most brittle to HTML changes
- ❌ Performance overhead
- ❌ Not recommended by any testing library

**Only use if:**
- Selecting text nodes in shadow DOM
- No other option available
- (Honestly: almost never)

---

## Comparison Matrix

| Method | Stability | Readability | Setup | Use Case |
|--------|-----------|-------------|-------|----------|
| **data-testid** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Easy | Interactive elements, containers |
| **Semantic (role)** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | HTML | Buttons, links, forms |
| **Label/Text** | ⭐⭐⭐ | ⭐⭐⭐⭐ | HTML | Very stable text |
| **CSS selectors** | ⭐⭐ | ⭐⭐ | Easy | Almost never (avoid) |
| **XPath** | ⭐ | ⭐ | Hard | Last resort only |

---

## Real-World Examples

### Example 1: Simple Form

```html
<!-- HTML with best practices -->
<form data-testid="login-form">
  <label for="email-input">Email</label>
  <input
    id="email-input"
    data-testid="email-input"
    type="email"
    aria-label="Email address"
  />

  <label for="password-input">Password</label>
  <input
    id="password-input"
    data-testid="password-input"
    type="password"
    aria-label="Password"
  />

  <button
    type="submit"
    data-testid="login-button"
  >
    Sign In
  </button>

  <a
    href="/reset"
    data-testid="forgot-password-link"
  >
    Forgot password?
  </a>
</form>

<div data-testid="error-alert" role="alert">
  Invalid credentials
</div>
```

**Test with selectors (in priority order):**

```typescript
// ✅ BEST: Use data-testid
await page.getByTestId('email-input').fill('user@example.com');
await page.getByTestId('password-input').fill('password123');
await page.getByTestId('login-button').click();

// ✅ GOOD: Use semantic selectors when available
await page.getByRole('form', { name: 'Login form' }).submit();
await page.getByLabel('Email').fill('user@example.com');

// ⚠️ OKAY: Use text as fallback
await page.getByText('Forgot password?').click();

// ❌ AVOID: CSS selectors
page.locator('.login-form input[type="email"]')
page.locator('form > div:nth-child(1) input')
```

### Example 2: Dynamic Lists

```html
<!-- Shopping cart with dynamic items -->
<div data-testid="cart-items">
  <div data-testid="cart-item-123" data-item-id="123">
    <h3>Product Name</h3>
    <span data-testid="item-price-123">$99.99</span>
    <button data-testid="remove-button-123">Remove</button>
  </div>

  <div data-testid="cart-item-456" data-item-id="456">
    <h3>Another Product</h3>
    <span data-testid="item-price-456">$49.99</span>
    <button data-testid="remove-button-456">Remove</button>
  </div>
</div>
```

**Test approach:**

```typescript
// ✅ Target specific item by ID
const itemId = '123';
await page.getByTestId(`remove-button-${itemId}`).click();

// ✅ Get all items and iterate
const cartItems = await page.getByTestId(/^cart-item-/).all();
expect(cartItems).toHaveLength(2);

// ❌ AVOID: Position-based selectors
page.locator('[data-testid="cart-items"] > div:first-child')
```

### Example 3: Modal/Dialog

```html
<!-- Modal dialog with proper ARIA -->
<div
  data-testid="success-modal"
  role="dialog"
  aria-modal="true"
  aria-label="Success confirmation"
>
  <h2>Success!</h2>
  <p data-testid="success-message">Your order has been placed.</p>

  <button data-testid="close-button">Close</button>
  <button data-testid="confirm-button">Confirm</button>
</div>
```

**Test:**

```typescript
// ✅ BEST: Use data-testid
await expect(page.getByTestId('success-modal')).toBeVisible();
await page.getByTestId('confirm-button').click();

// ✅ GOOD: Use semantic role
await expect(page.getByRole('dialog')).toBeVisible();
await page.getByRole('button', { name: 'Close' }).click();

// ⚠️ Using text (less ideal)
await page.getByText('Confirm').click();
```

---

## Adding data-testid to Your Components

### If Component Doesn't Have data-testid

**Step 1: Identify the element in your test**
```typescript
// This fails because data-testid doesn't exist
await page.getByTestId('email-input').fill('test@example.com');
// Error: No element with data-testid="email-input"
```

**Step 2: Add data-testid to the component**

**React:**
```jsx
export function LoginForm() {
  return (
    <input
      data-testid="email-input"
      type="email"
    />
  );
}
```

**Vue:**
```vue
<template>
  <input
    data-testid="email-input"
    type="email"
  />
</template>
```

**Angular:**
```html
<input
  data-testid="email-input"
  type="email"
/>
```

**Svelte:**
```svelte
<input
  data-testid="email-input"
  type="email"
/>
```

**Step 3: Run test again - should pass ✅**

---

## Selector Naming Conventions

### ✅ DO: Semantic, kebab-case names

```html
<!-- Interactive elements -->
<button data-testid="submit-button">Submit</button>
<button data-testid="cancel-button">Cancel</button>
<a data-testid="logout-link">Logout</a>
<input data-testid="email-input" />

<!-- Form fields -->
<input data-testid="first-name-input" />
<input data-testid="phone-number-input" />
<select data-testid="country-select" />

<!-- Containers -->
<div data-testid="success-message">Success!</div>
<div data-testid="error-alert">Error occurred</div>

<!-- Lists with IDs -->
<li data-testid="product-item-123">Product Name</li>
<li data-testid="order-item-456">Order #456</li>

<!-- Complex components -->
<div data-testid="user-profile-card">
  <img data-testid="user-avatar" />
  <h2 data-testid="user-name">John Doe</h2>
  <button data-testid="edit-profile-button">Edit</button>
</div>
```

### ❌ DON'T: Generic or unclear names

```html
<!-- Too generic -->
<button data-testid="btn">Submit</button>  <!-- Which button? -->
<div data-testid="div-1">Content</div>     <!-- What is this? -->
<input data-testid="input">                <!-- Which input? -->

<!-- Unclear scope -->
<button data-testid="clickable">Submit</button>
<div data-testid="container">Content</div>

<!-- Redundant with HTML -->
<button data-testid="button-element">Submit</button>
<input data-testid="input-field" />

<!-- Technical jargon -->
<button data-testid="btn-primary-md">Submit</button>
<div data-testid="flex-container-row">Content</div>
```

---

## Debugging Selector Issues

### Issue: Selector Works Locally, Fails in CI

```typescript
// ❌ PROBLEM: Depends on exact text
await page.getByText('Load More').click();

// CI environment has different language/content:
// "Charger plus" (French) vs "Load More" (English)
// Test fails in CI only!

// ✅ SOLUTION: Use data-testid
await page.getByTestId('load-more-button').click();
```

### Issue: Selector Sometimes Fails

```typescript
// ❌ PROBLEM: Waits for element, but element re-renders
await page.locator('[class*="loading"]').waitFor({ state: 'hidden' });
await page.locator('button').click();  // Element might be recreated

// ✅ SOLUTION: Use data-testid which survives re-renders
await page.getByTestId('loading-spinner').waitFor({ state: 'hidden' });
await page.getByTestId('action-button').click();
```

### Issue: Selector Breaks After CSS Update

```typescript
// ❌ ORIGINAL: Depends on CSS classes
page.locator('.btn.btn-primary')

// ❌ AFTER CSS REFACTOR: CSS classes changed
// .btn-primary → .button-primary
// Test now FAILS

// ✅ SOLUTION: Use data-testid (unaffected by CSS)
page.getByTestId('submit-button')
```

---

## Testing Best Practices with Selectors

**Rule 1: Use data-testid first, everything else is fallback**
```typescript
// Try in this order:
1. page.getByTestId('button-name')
2. page.getByRole('button', { name: 'Submit' })
3. page.getByLabel('Label Text')
4. page.getByText('User visible text')
5. Avoid CSS/XPath
```

**Rule 2: data-testid should be in the HTML**
```typescript
// ✅ GOOD: Test can find it
<button data-testid="submit">Submit</button>
await page.getByTestId('submit').click();

// ❌ BAD: dynamically added (fragile)
button.setAttribute('data-testid', 'submit');
```

**Rule 3: Share data-testid naming conventions**
```typescript
// ✅ Team agrees on pattern:
// {action}-{element}: "submit-button", "close-dialog"
// {role}-{modifier}: "login-form", "error-message"

// ❌ Everyone names them differently:
// "btn", "submitBtn", "submit-btn", "button_submit"
```

**Rule 4: Don't add data-testid in production code**
```typescript
// These are TESTING concerns, OK to include:
<button data-testid="submit">Submit</button>  // ✅ OK

// Tree-shaking consideration (minimal impact):
// data-testid adds ~50 bytes per attribute
// Usually worth it for test reliability
```

---

## Summary

| Priority | Selector | When to Use | Stability |
|----------|----------|------------|-----------|
| 1 | `data-testid` | Always (if present) | ⭐⭐⭐⭐⭐ |
| 2 | `getByRole()` | Semantic HTML exists | ⭐⭐⭐⭐ |
| 3 | `getByLabel()` | Form fields | ⭐⭐⭐⭐ |
| 4 | `getByText()` | Stable text only | ⭐⭐⭐ |
| 5 | CSS/XPath | Only as last resort | ⭐⭐ |

**Remember:** If your app doesn't have `data-testid` attributes, add them first. It's the most important investment in E2E test reliability.
