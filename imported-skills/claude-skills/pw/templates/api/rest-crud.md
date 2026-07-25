# REST CRUD API Template

Tests GET, POST, PUT, and DELETE API endpoints directly via Playwright's request API.

## Prerequisites
- Valid auth token: `{{apiToken}}`
- Base API URL: `{{apiBaseUrl}}`
- Test entity endpoint: `/{{entityName}}s`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('REST CRUD — /{{entityName}}s', () => {
  let createdId: string;

  const headers = {
    'Authorization': `Bearer {{apiToken}}`,
    'Content-Type': 'application/json',
  };

  // Happy path: GET list
  test('GET /{{entityName}}s returns list', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s', { headers });
    expect(res.status()).toBe(200);
    const body = await res.json();
    expect(Array.isArray(body.data ?? body)).toBe(true);
  });

  // Happy path: POST creates entity
  test('POST /{{entityName}}s creates new entity', async ({ request }) => {
    const res = await request.post('{{apiBaseUrl}}/{{entityName}}s', {
      headers,
      data: { name: '{{testEntityName}}', description: '{{testDescription}}' },
    });
    expect(res.status()).toBe(201);
    const body = await res.json();
    expect(body.id).toBeTruthy();
    expect(body.name).toBe('{{testEntityName}}');
    createdId = body.id;
  });

  // Happy path: GET single entity
  test('GET /{{entityName}}s/:id returns entity', async ({ request }) => {
    const res = await request.get(`{{apiBaseUrl}}/{{entityName}}s/{{existingEntityId}}`, { headers });
    expect(res.status()).toBe(200);
    const body = await res.json();
    expect(body.id).toBe('{{existingEntityId}}');
    expect(body.name).toBeTruthy();
  });

  // Happy path: PUT updates entity
  test('PUT /{{entityName}}s/:id updates entity', async ({ request }) => {
    const res = await request.put(`{{apiBaseUrl}}/{{entityName}}s/{{existingEntityId}}`, {
      headers,
      data: { name: '{{updatedEntityName}}' },
    });
    expect(res.status()).toBe(200);
    const body = await res.json();
    expect(body.name).toBe('{{updatedEntityName}}');
  });

  // Happy path: PATCH partial update
  test('PATCH /{{entityName}}s/:id partially updates entity', async ({ request }) => {
    const res = await request.patch(`{{apiBaseUrl}}/{{entityName}}s/{{existingEntityId}}`, {
      headers,
      data: { description: '{{patchedDescription}}' },
    });
    expect(res.status()).toBe(200);
    const body = await res.json();
    expect(body.description).toBe('{{patchedDescription}}');
  });

  // Happy path: DELETE removes entity
  test('DELETE /{{entityName}}s/:id deletes entity', async ({ request }) => {
    const del = await request.delete(`{{apiBaseUrl}}/{{entityName}}s/{{deletableEntityId}}`, { headers });
    expect(del.status()).toBe(204);
    // Verify gone
    const get = await request.get(`{{apiBaseUrl}}/{{entityName}}s/{{deletableEntityId}}`, { headers });
    expect(get.status()).toBe(404);
  });

  // Error case: POST with missing required field returns 422
  test('POST with missing required field returns 422', async ({ request }) => {
    const res = await request.post('{{apiBaseUrl}}/{{entityName}}s', {
      headers,
      data: {},
    });
    expect(res.status()).toBe(422);
    const body = await res.json();
    expect(body.errors).toBeTruthy();
  });

  // Error case: GET non-existent entity returns 404
  test('GET non-existent entity returns 404', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s/999999', { headers });
    expect(res.status()).toBe(404);
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

const headers = {
  'Authorization': `Bearer {{apiToken}}`,
  'Content-Type': 'application/json',
};

test.describe('REST CRUD — /{{entityName}}s', () => {
  test('GET list returns 200 and array', async ({ request }) => {
    const res = await request.get('{{apiBaseUrl}}/{{entityName}}s', { headers });
    expect(res.status()).toBe(200);
    const body = await res.json();
    expect(Array.isArray(body.data ?? body)).toBe(true);
  });

  test('POST creates entity and returns 201', async ({ request }) => {
    const res = await request.post('{{apiBaseUrl}}/{{entityName}}s', {
      headers,
      data: { name: '{{testEntityName}}' },
    });
    expect(res.status()).toBe(201);
    expect((await res.json()).id).toBeTruthy();
  });

  test('DELETE removes entity, GET returns 404', async ({ request }) => {
    await request.delete(`{{apiBaseUrl}}/{{entityName}}s/{{deletableEntityId}}`, { headers });
    const res = await request.get(`{{apiBaseUrl}}/{{entityName}}s/{{deletableEntityId}}`, { headers });
    expect(res.status()).toBe(404);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| GET list | 200 + array body |
| POST create | 201 + id in response |
| GET single | 200 + correct entity body |
| PUT update | 200 + updated field in response |
| PATCH partial | 200 + patched field only changed |
| DELETE | 204 → subsequent GET returns 404 |
| POST validation | Missing field → 422 + errors |
| GET 404 | Non-existent ID → 404 |
