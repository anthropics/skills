# Test Generation Patterns

## Pattern: Authentication Flow

```typescript
test.describe('Authentication', () => {
  test('should login with valid credentials', async ({ page }) => {
    await page.goto('/login');
    await page.getByLabel('Email').fill('user@example.com');
    await page.getByLabel('Password').fill('password123');
    await page.getByRole('button', { name: 'Sign in' }).click();
    await expect(page).toHaveURL('/dashboard');
    await expect(page.getByRole('heading', { name: 'Dashboard' })).toBeVisible();
  });

  test('should show error for invalid credentials', async ({ page }) => {
    await page.goto('/login');
    await page.getByLabel('Email').fill('wrong@example.com');
    await page.getByLabel('Password').fill('wrong');
    await page.getByRole('button', { name: 'Sign in' }).click();
    await expect(page.getByRole('alert')).toHaveText(/invalid/i);
    await expect(page).toHaveURL('/login');
  });
});
```

## Pattern: CRUD Operations

```typescript
test.describe('Items', () => {
  test('should create a new item', async ({ page }) => {
    await page.goto('/items');
    await page.getByRole('button', { name: 'Add item' }).click();
    await page.getByLabel('Name').fill('Test Item');
    await page.getByRole('button', { name: 'Save' }).click();
    await expect(page.getByText('Test Item')).toBeVisible();
  });

  test('should edit an existing item', async ({ page }) => {
    await page.goto('/items');
    await page.getByRole('row', { name: /Test Item/ })
      .getByRole('button', { name: 'Edit' }).click();
    await page.getByLabel('Name').clear();
    await page.getByLabel('Name').fill('Updated Item');
    await page.getByRole('button', { name: 'Save' }).click();
    await expect(page.getByText('Updated Item')).toBeVisible();
  });

  test('should delete an item with confirmation', async ({ page }) => {
    await page.goto('/items');
    await page.getByRole('row', { name: /Test Item/ })
      .getByRole('button', { name: 'Delete' }).click();
    await page.getByRole('button', { name: 'Confirm' }).click();
    await expect(page.getByText('Test Item')).not.toBeVisible();
  });
});
```

## Pattern: Form with Validation

```typescript
test.describe('Contact Form', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/contact');
  });

  test('should submit valid form', async ({ page }) => {
    await page.getByLabel('Name').fill('Jane Doe');
    await page.getByLabel('Email').fill('jane@example.com');
    await page.getByLabel('Message').fill('Hello, this is a test message.');
    await page.getByRole('button', { name: 'Send' }).click();
    await expect(page.getByText('Message sent')).toBeVisible();
  });

  test('should show validation errors for empty required fields', async ({ page }) => {
    await page.getByRole('button', { name: 'Send' }).click();
    await expect(page.getByText('Name is required')).toBeVisible();
    await expect(page.getByText('Email is required')).toBeVisible();
  });

  test('should validate email format', async ({ page }) => {
    await page.getByLabel('Email').fill('not-an-email');
    await page.getByRole('button', { name: 'Send' }).click();
    await expect(page.getByText('Invalid email')).toBeVisible();
  });
});
```

## Pattern: Search and Filter

```typescript
test.describe('Product Search', () => {
  test('should return results for valid query', async ({ page }) => {
    await page.goto('/products');
    await page.getByPlaceholder('Search products').fill('laptop');
    await page.getByRole('button', { name: 'Search' }).click();
    await expect(page.getByRole('list')).toBeVisible();
    const results = page.getByRole('listitem');
    await expect(results).not.toHaveCount(0);
  });

  test('should show empty state for no results', async ({ page }) => {
    await page.goto('/products');
    await page.getByPlaceholder('Search products').fill('xyznonexistent');
    await page.getByRole('button', { name: 'Search' }).click();
    await expect(page.getByText('No products found')).toBeVisible();
  });

  test('should filter by category', async ({ page }) => {
    await page.goto('/products');
    await page.getByRole('combobox', { name: 'Category' }).selectOption('Electronics');
    await expect(page.getByRole('listitem')).not.toHaveCount(0);
  });
});
```

## Pattern: Navigation and Layout

```typescript
test.describe('Navigation', () => {
  test('should navigate between pages', async ({ page }) => {
    await page.goto('/');
    await page.getByRole('link', { name: 'About' }).click();
    await expect(page).toHaveURL('/about');
    await expect(page.getByRole('heading', { level: 1 })).toHaveText('About');
  });

  test('should show mobile menu on small screens', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto('/');
    await expect(page.getByRole('navigation')).not.toBeVisible();
    await page.getByRole('button', { name: 'Menu' }).click();
    await expect(page.getByRole('navigation')).toBeVisible();
  });
});
```

## Pattern: API Mocking

```typescript
test.describe('Dashboard with mocked API', () => {
  test('should display data from API', async ({ page }) => {
    await page.route('**/api/dashboard', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ revenue: 50000, users: 1200 }),
      });
    });
    await page.goto('/dashboard');
    await expect(page.getByText('$50,000')).toBeVisible();
    await expect(page.getByText('1,200')).toBeVisible();
  });

  test('should handle API errors gracefully', async ({ page }) => {
    await page.route('**/api/dashboard', (route) => {
      route.fulfill({ status: 500 });
    });
    await page.goto('/dashboard');
    await expect(page.getByText(/error|try again/i)).toBeVisible();
  });
});
```
