# GraphQL API Template

Tests query, mutation, and subscription via Playwright's request API.

## Prerequisites
- Valid auth token: `{{apiToken}}`
- GraphQL endpoint: `{{graphqlEndpoint}}`
- WebSocket endpoint for subscriptions: `{{graphqlWsEndpoint}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

const GQL_URL = '{{graphqlEndpoint}}';
const headers = {
  'Authorization': `Bearer {{apiToken}}`,
  'Content-Type': 'application/json',
};

async function gql(request: any, query: string, variables = {}) {
  const res = await request.post(GQL_URL, { headers, data: { query, variables } });
  const body = await res.json();
  expect(body.errors).toBeUndefined();
  return body.data;
}

test.describe('GraphQL API', () => {
  // Happy path: query
  test('query fetches {{entityName}} list', async ({ request }) => {
    const data = await gql(request, `
      query Get{{EntityName}}s($limit: Int) {
        {{entityName}}s(limit: $limit) { id name createdAt }
      }
    `, { limit: 10 });
    expect(Array.isArray(data.{{entityName}}s)).toBe(true);
    expect(data.{{entityName}}s.length).toBeLessThanOrEqual(10);
  });

  // Happy path: query single entity
  test('query fetches single {{entityName}} by id', async ({ request }) => {
    const data = await gql(request, `
      query Get{{EntityName}}($id: ID!) {
        {{entityName}}(id: $id) { id name description }
      }
    `, { id: '{{existingEntityId}}' });
    expect(data.{{entityName}}.id).toBe('{{existingEntityId}}');
  });

  // Happy path: mutation creates entity
  test('mutation creates {{entityName}}', async ({ request }) => {
    const data = await gql(request, `
      mutation Create{{EntityName}}($input: {{EntityName}}Input!) {
        create{{EntityName}}(input: $input) { id name }
      }
    `, { input: { name: '{{testEntityName}}', description: '{{testDescription}}' } });
    expect(data.create{{EntityName}}.id).toBeTruthy();
    expect(data.create{{EntityName}}.name).toBe('{{testEntityName}}');
  });

  // Happy path: mutation updates entity
  test('mutation updates {{entityName}}', async ({ request }) => {
    const data = await gql(request, `
      mutation Update{{EntityName}}($id: ID!, $input: {{EntityName}}Input!) {
        update{{EntityName}}(id: $id, input: $input) { id name }
      }
    `, { id: '{{existingEntityId}}', input: { name: '{{updatedName}}' } });
    expect(data.update{{EntityName}}.name).toBe('{{updatedName}}');
  });

  // Happy path: mutation deletes entity
  test('mutation deletes {{entityName}}', async ({ request }) => {
    const data = await gql(request, `
      mutation Delete{{EntityName}}($id: ID!) {
        delete{{EntityName}}(id: $id) { success }
      }
    `, { id: '{{deletableEntityId}}' });
    expect(data.delete{{EntityName}}.success).toBe(true);
  });

  // Error case: invalid query returns errors array
  test('invalid query returns errors', async ({ request }) => {
    const res = await request.post(GQL_URL, {
      headers,
      data: { query: '{ invalidField }' },
    });
    const body = await res.json();
    expect(body.errors).toBeDefined();
    expect(body.errors.length).toBeGreaterThan(0);
  });

  // Error case: unauthorized query
  test('query without auth returns unauthorized error', async ({ request }) => {
    const res = await request.post(GQL_URL, {
      headers: { 'Content-Type': 'application/json' }, // No auth
      data: { query: '{ {{entityName}}s { id } }' },
    });
    const body = await res.json();
    expect(body.errors?.[0]?.extensions?.code).toMatch(/UNAUTHENTICATED|UNAUTHORIZED/);
  });

  // Edge case: subscription via page WebSocket
  test('subscription receives real-time update', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    const received: any[] = [];
    await page.evaluate(() => {
      const ws = new WebSocket('{{graphqlWsEndpoint}}');
      ws.onmessage = e => (window as any).__gqlMsg = JSON.parse(e.data);
    });
    // Trigger mutation to fire subscription
    await page.request.post(GQL_URL, {
      headers,
      data: { query: 'mutation { trigger{{EntityName}}Event { id } }' },
    });
    const msg = await page.evaluate(() => (window as any).__gqlMsg);
    expect(msg?.type).toBe('data');
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

const headers = { 'Authorization': `Bearer {{apiToken}}`, 'Content-Type': 'application/json' };

async function gql(request, query, variables = {}) {
  const res = await request.post('{{graphqlEndpoint}}', { headers, data: { query, variables } });
  const body = await res.json();
  expect(body.errors).toBeUndefined();
  return body.data;
}

test.describe('GraphQL API', () => {
  test('query fetches entity list', async ({ request }) => {
    const data = await gql(request, '{ {{entityName}}s { id name } }');
    expect(Array.isArray(data.{{entityName}}s)).toBe(true);
  });

  test('mutation creates entity', async ({ request }) => {
    const data = await gql(request,
      'mutation($input: {{EntityName}}Input!) { create{{EntityName}}(input: $input) { id } }',
      { input: { name: '{{testEntityName}}' } }
    );
    expect(data.create{{EntityName}}.id).toBeTruthy();
  });

  test('invalid query returns errors array', async ({ request }) => {
    const res = await request.post('{{graphqlEndpoint}}', {
      headers,
      data: { query: '{ nonExistentField }' },
    });
    const body = await res.json();
    expect(body.errors?.length).toBeGreaterThan(0);
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| List query | Returns array of entities |
| Single query | Returns entity by ID |
| Create mutation | Returns new entity with ID |
| Update mutation | Returns updated field value |
| Delete mutation | Returns success: true |
| Invalid query | errors[] defined in response |
| Unauthenticated | UNAUTHENTICATED extension code |
| Subscription | Real-time message via WebSocket |
