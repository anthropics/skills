# Auth Headers Template

Tests token authentication, expired token handling, and token refresh flow.

## Prerequisites
- Valid token: `{{apiToken}}`
- Expired token: `{{expiredApiToken}}`
- Refresh token: `{{refreshToken}}`
- API base: `{{apiBaseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('API Auth Headers', () => {
  // Happy path: valid Bearer token accepted
  test('accepts valid Bearer token', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer {{apiToken}}` },
    });
    expect(res.status()).toBe(200);
    const body = await res.json();
    expect(body.id).toBeTruthy();
  });

  // Happy path: API key in header accepted
  test('accepts API key header', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s', {
      headers: { 'X-API-Key': '{{apiKey}}' },
    });
    expect(res.status()).toBe(200);
  });

  // Error case: no auth header returns 401
  test('returns 401 without auth header', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me');
    expect(res.status()).toBe(401);
    const body = await res.json();
    expect(body.error ?? body.message).toMatch(/unauthorized|authentication required/i);
  });

  // Error case: expired token returns 401
  test('returns 401 for expired token', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer {{expiredApiToken}}` },
    });
    expect(res.status()).toBe(401);
    const body = await res.json();
    expect(body.error ?? body.code).toMatch(/token.*expired|expired_token/i);
  });

  // Happy path: refresh token obtains new access token
  test('refreshes expired token and retries request', async ({ request }) => {
    // Step 1: refresh
    const refresh = await request.post('{{apiBaseUrl}}/auth/refresh', {
      data: { refresh_token: '{{refreshToken}}' },
    });
    expect(refresh.status()).toBe(200);
    const { access_token } = await refresh.json();
    expect(access_token).toBeTruthy();

    // Step 2: use new token
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer ${access_token}` },
    });
    expect(res.status()).toBe(200);
  });

  // Error case: invalid token format returns 401
  test('returns 401 for malformed token', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': 'Bearer not.a.jwt' },
    });
    expect(res.status()).toBe(401);
  });

  // Edge case: token in cookie vs header
  test('accepts session cookie as auth alternative', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Cookie': `{{sessionCookieName}}={{sessionCookieValue}}` },
    });
    expect(res.status()).toBe(200);
  });

  // Edge case: revoked token returns 401
  test('returns 401 for revoked token', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer {{revokedApiToken}}` },
    });
    expect(res.status()).toBe(401);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('API Auth Headers', () => {
  test('accepts valid Bearer token', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer {{apiToken}}` },
    });
    expect(res.status()).toBe(200);
  });

  test('returns 401 without auth header', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me');
    expect(res.status()).toBe(401);
  });

  test('returns 401 for expired token', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer {{expiredApiToken}}` },
    });
    expect(res.status()).toBe(401);
  });

  test('refreshes token and retries', async ({ request }) => {
    const refresh = await request.post('{{apiBaseUrl}}/auth/refresh', {
      data: { refresh_token: '{{refreshToken}}' },
    });
    const { access_token } = await refresh.json();
    const res = await request.get('{{apiBaseUrl}}/me', {
      headers: { 'Authorization': `Bearer ${access_token}` },
    });
    expect(res.status()).toBe(200);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Valid Bearer | 200 with user data |
| API key | X-API-Key header accepted |
| No auth | 401 + error message |
| Expired token | 401 + expired error code |
| Token refresh | New token from refresh endpoint |
| Malformed token | 401 for non-JWT |
| Cookie auth | Session cookie accepted |
| Revoked token | 401 for revoked token |
