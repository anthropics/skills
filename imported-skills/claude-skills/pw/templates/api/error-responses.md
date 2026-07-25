# API Error Responses Template

Tests 400, 401, 403, 404, and 500 HTTP error handling.

## Prerequisites
- Valid auth token: `{{apiToken}}`
- API base: `{{apiBaseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

const validHeaders = {
  'Authorization': `Bearer {{apiToken}}`,
  'Content-Type': 'application/json',
};

test.describe('API Error Responses', () => {
  // 400 Bad Request
  test('POST with invalid body returns 400', async ({ request }) => {
    const res = await request.post('{{apiBaseUrl}}/{{entityName}}s', {
      headers: validHeaders,
      data: { name: '' }, // name too short / blank
    });
    expect(res.status()).toBe(400);
    const body = await res.json();
    expect(body.message ?? body.error).toMatch(/bad request|invalid/i);
    expect(body.errors ?? body.details).toBeDefined();
  });

  // 401 Unauthorized
  test('request without token returns 401', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s');
    expect(res.status()).toBe(401);
    const body = await res.json();
    expect(body.message ?? body.error).toMatch(/unauthorized|authentication/i);
  });

  // 403 Forbidden
  test('accessing admin endpoint as regular user returns 403', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/admin/users', {
      headers: { 'Authorization': `Bearer {{userToken}}` },
    });
    expect(res.status()).toBe(403);
    const body = await res.json();
    expect(body.message ?? body.error).toMatch(/forbidden|insufficient.*permission/i);
  });

  // 404 Not Found
  test('GET non-existent resource returns 404', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s/999999', { headers: validHeaders });
    expect(res.status()).toBe(404);
    const body = await res.json();
    expect(body.message ?? body.error).toMatch(/not found/i);
  });

  // 422 Unprocessable Entity
  test('POST with missing required field returns 422', async ({ request }) => {
    const res = await request.post('{{apiBaseUrl}}/{{entityName}}s', {
      headers: validHeaders,
      data: { description: 'no name provided' },
    });
    expect([422, 400]).toContain(res.status());
    const body = await res.json();
    expect(body.errors ?? body.details).toBeDefined();
  });

  // 429 Too Many Requests (handled in rate-limiting template — kept here for completeness)
  test('returns 429 when rate limit exceeded', async ({ request }) => {
    let lastStatus = 0;
    for (let i = 0; i < {{rateLimitThreshold}} + 1; i++) {
      const res = await request.get('{{apiBaseUrl}}/{{rateLimitedEndpoint}}', { headers: validHeaders });
      lastStatus = res.status();
      if (lastStatus === 429) break;
    }
    expect(lastStatus).toBe(429);
  });

  // 500 Internal Server Error
  test('server error returns 500 with error body', async ({ page }) => {
    await page.route('{{apiBaseUrl}}/{{entityName}}s', route =>
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'Internal Server Error' }) })
    );
    const res = await page.request.get('{{apiBaseUrl}}/{{entityName}}s', { headers: validHeaders });
    expect(res.status()).toBe(500);
    const body = await res.json();
    expect(body.error ?? body.message).toBeTruthy();
  });

  // Edge case: error response has consistent shape
  test('all errors return JSON with error field', async ({ request }) => {
    const endpoints = [
      { method: 'get' as const, url: '{{apiBaseUrl}}/{{entityName}}s/000000', headers: validHeaders },
      { method: 'get' as const, url: '{{apiBaseUrl}}/{{entityName}}s' },
    ];
    for (const ep of endpoints) {
      const res = await request[ep.method](ep.url, { headers: ep.headers });
      if (res.status() >= 400) {
        const body = await res.json();
        expect(body.error ?? body.message ?? body.errors).toBeDefined();
      }
    }
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

const headers = { 'Authorization': `Bearer {{apiToken}}`, 'Content-Type': 'application/json' };

test.describe('API Error Responses', () => {
  test('POST with invalid body returns 400', async ({ request }) => {
    const res = await request.post('{{apiBaseUrl}}/{{entityName}}s', {
      headers,
      data: { name: '' },
    });
    expect(res.status()).toBe(400);
  });

  test('no token returns 401', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s');
    expect(res.status()).toBe(401);
  });

  test('regular user on admin endpoint returns 403', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/admin/users', {
      headers: { 'Authorization': `Bearer {{userToken}}` },
    });
    expect(res.status()).toBe(403);
  });

  test('non-existent resource returns 404', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s/999999', { headers });
    expect(res.status()).toBe(404);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| 400 Bad Request | Invalid body → 400 + errors detail |
| 401 Unauthorized | No token → 401 |
| 403 Forbidden | Wrong role → 403 |
| 404 Not Found | Missing resource → 404 |
| 422 Unprocessable | Missing required field → 422/400 |
| 429 Rate Limit | Threshold exceeded → 429 |
| 500 Server Error | Mocked 500 → error body present |
| Consistent shape | All errors have error/message field |
