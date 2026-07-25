# Rate Limiting Template

Tests rate limit headers, 429 response, and Retry-After handling.

## Prerequisites
- Valid auth token: `{{apiToken}}`
- Rate-limited endpoint: `{{rateLimitedEndpoint}}`
- Rate limit: `{{rateLimit}}` requests per `{{rateLimitWindow}}`
- API base: `{{apiBaseUrl}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

const headers = {
  'Authorization': `Bearer {{apiToken}}`,
  'Content-Type': 'application/json',
};

test.describe('Rate Limiting', () => {
  // Happy path: rate limit headers present on normal requests
  test('includes rate limit headers on success response', async ({ request }) => {
    const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    expect(res.status()).toBe(200);
    expect(res.headers()['x-ratelimit-limit']).toBeTruthy();
    expect(res.headers()['x-ratelimit-remaining']).toBeTruthy();
    expect(Number(res.headers()['x-ratelimit-limit'])).toBe({{rateLimit}});
  });

  // Happy path: remaining count decrements
  test('x-ratelimit-remaining decrements with each request', async ({ request }) => {
    const first = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    const second = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    const remaining1 = Number(first.headers()['x-ratelimit-remaining']);
    const remaining2 = Number(second.headers()['x-ratelimit-remaining']);
    expect(remaining2).toBeLessThan(remaining1);
  });

  // Error case: 429 when limit exceeded
  test('returns 429 when rate limit exceeded', async ({ request }) => {
    let lastStatus = 200;
    let retryAfter: string | undefined;
    for (let i = 0; i <= {{rateLimit}}; i++) {
      const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
      lastStatus = res.status();
      if (lastStatus === 429) {
        retryAfter = res.headers()['retry-after'];
        break;
      }
    }
    expect(lastStatus).toBe(429);
    expect(retryAfter).toBeTruthy();
  });

  // Error case: 429 body contains error message
  test('429 response body contains error and retry info', async ({ request }) => {
    // Exhaust limit
    for (let i = 0; i <= {{rateLimit}}; i++) {
      await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    }
    const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    if (res.status() === 429) {
      const body = await res.json();
      expect(body.error ?? body.message).toMatch(/rate limit|too many requests/i);
      expect(Number(res.headers()['retry-after'])).toBeGreaterThan(0);
    }
  });

  // Happy path: different users have separate rate limit buckets
  test('rate limit is per-user, not global', async ({ request }) => {
    // Exhaust limit for user 1
    for (let i = 0; i <= {{rateLimit}}; i++) {
      await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, {
        headers: { 'Authorization': `Bearer {{apiToken}}` },
      });
    }
    // User 2 should still succeed
    const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, {
      headers: { 'Authorization': `Bearer {{apiToken2}}` },
    });
    expect(res.status()).toBe(200);
  });

  // Edge case: reset after window expires
  test('rate limit resets after window expires', async ({ page, request }) => {
    // Exhaust limit
    for (let i = 0; i <= {{rateLimit}}; i++) {
      await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    }
    // Advance clock past the window
    await page.clock.install();
    await page.clock.fastForward({{rateLimitWindowMs}});
    // Should succeed again
    const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    expect(res.status()).toBe(200);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

const headers = { 'Authorization': `Bearer {{apiToken}}` };

test.describe('Rate Limiting', () => {
  test('includes rate limit headers on success', async ({ request }) => {
    const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    expect(res.status()).toBe(200);
    expect(res.headers()['x-ratelimit-limit']).toBeTruthy();
    expect(res.headers()['x-ratelimit-remaining']).toBeTruthy();
  });

  test('returns 429 with Retry-After when limit exceeded', async ({ request }) => {
    let lastStatus = 200;
    let retryAfter;
    for (let i = 0; i <= {{rateLimit}}; i++) {
      const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
      lastStatus = res.status();
      if (lastStatus === 429) { retryAfter = res.headers()['retry-after']; break; }
    }
    expect(lastStatus).toBe(429);
    expect(retryAfter).toBeTruthy();
  });

  test('per-user buckets: other user unaffected', async ({ request }) => {
    for (let i = 0; i <= {{rateLimit}}; i++) {
      await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, { headers });
    }
    const res = await request.get(`{{apiBaseUrl}}/{{rateLimitedEndpoint}}`, {
      headers: { 'Authorization': `Bearer {{apiToken2}}` },
    });
    expect(res.status()).toBe(200);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Headers present | x-ratelimit-limit and -remaining on 200 |
| Decrement | remaining decreases each request |
| 429 triggered | Limit exceeded → 429 + Retry-After |
| 429 body | Error message + retry info in body |
| Per-user bucket | Exhausted user doesn't affect others |
| Window reset | Clock advanced → limit resets |
