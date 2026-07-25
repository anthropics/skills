# api-test-suite-builder reference

## Example Test Files

### Example 1 — Node.js: Vitest + Supertest (Next.js API Route)

```typescript
// tests/api/users.test.ts
import { describe, it, expect, beforeAll, afterAll } from 'vitest'
import request from 'supertest'
import { createServer } from '@/test/helpers/server'
import { generateJWT, generateExpiredJWT } from '@/test/helpers/auth'
import { createTestUser, cleanupTestUsers } from '@/test/helpers/db'

const app = createServer()

describe('GET /api/users/:id', () => {
  let validToken: string
  let adminToken: string
  let testUserId: string

  beforeAll(async () => {
    const user = await createTestUser({ role: 'user' })
    const admin = await createTestUser({ role: 'admin' })
    testUserId = user.id
    validToken = generateJWT(user)
    adminToken = generateJWT(admin)
  })

  afterAll(async () => {
    await cleanupTestUsers()
  })

  // --- Auth tests ---
  it('returns 401 with no auth header', async () => {
    const res = await request(app).get(`/api/users/${testUserId}`)
    expect(res.status).toBe(401)
    expect(res.body).toHaveProperty('error')
  })

  it('returns 401 with malformed token', async () => {
    const res = await request(app)
      .get(`/api/users/${testUserId}`)
      .set('Authorization', 'Bearer not-a-real-jwt')
    expect(res.status).toBe(401)
  })

  it('returns 401 with expired token', async () => {
    const expiredToken = generateExpiredJWT({ id: testUserId })
    const res = await request(app)
      .get(`/api/users/${testUserId}`)
      .set('Authorization', `Bearer ${expiredToken}`)
    expect(res.status).toBe(401)
    expect(res.body.error).toMatch(/expired/i)
  })

  it('returns 403 when accessing another user\'s profile without admin', async () => {
    const otherUser = await createTestUser({ role: 'user' })
    const otherToken = generateJWT(otherUser)
    const res = await request(app)
      .get(`/api/users/${testUserId}`)
      .set('Authorization', `Bearer ${otherToken}`)
    expect(res.status).toBe(403)
    await cleanupTestUsers([otherUser.id])
  })

  it('returns 200 with valid token for own profile', async () => {
    const res = await request(app)
      .get(`/api/users/${testUserId}`)
      .set('Authorization', `Bearer ${validToken}`)
    expect(res.status).toBe(200)
    expect(res.body).toMatchObject({ id: testUserId })
    expect(res.body).not.toHaveProperty('password')
    expect(res.body).not.toHaveProperty('hashedPassword')
  })

  it('returns 404 for non-existent user', async () => {
    const res = await request(app)
      .get('/api/users/00000000-0000-0000-0000-000000000000')
      .set('Authorization', `Bearer ${adminToken}`)
    expect(res.status).toBe(404)
  })

  // --- Input validation ---
  it('returns 400 for invalid UUID format', async () => {
    const res = await request(app)
      .get('/api/users/not-a-uuid')
      .set('Authorization', `Bearer ${adminToken}`)
    expect(res.status).toBe(400)
  })
})

describe('POST /api/users', () => {
  let adminToken: string

  beforeAll(async () => {
    const admin = await createTestUser({ role: 'admin' })
    adminToken = generateJWT(admin)
  })

  afterAll(cleanupTestUsers)

  // --- Input validation ---
  it('returns 422 when body is empty', async () => {
    const res = await request(app)
      .post('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
      .send({})
    expect(res.status).toBe(422)
    expect(res.body.errors).toBeDefined()
  })

  it('returns 422 when email is missing', async () => {
    const res = await request(app)
      .post('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
      .send({ name: "test-user", role: 'user' })
    expect(res.status).toBe(422)
    expect(res.body.errors).toContainEqual(
      expect.objectContaining({ field: 'email' })
    )
  })

  it('returns 422 for invalid email format', async () => {
    const res = await request(app)
      .post('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
      .send({ email: 'not-an-email', name: "test", role: 'user' })
    expect(res.status).toBe(422)
  })

  it('returns 422 for SQL injection attempt in email field', async () => {
    const res = await request(app)
      .post('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
      .send({ email: "' OR '1'='1", name: "hacker", role: 'user' })
    expect(res.status).toBe(422)
  })

  it('returns 409 when email already exists', async () => {
    const existing = await createTestUser({ role: 'user' })
    const res = await request(app)
      .post('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
      .send({ email: existing.email, name: "duplicate", role: 'user' })
    expect(res.status).toBe(409)
  })

  it('creates user successfully with valid data', async () => {
    const res = await request(app)
      .post('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
      .send({ email: 'newuser@example.com', name: "new-user", role: 'user' })
    expect(res.status).toBe(201)
    expect(res.body).toHaveProperty('id')
    expect(res.body.email).toBe('newuser@example.com')
    expect(res.body).not.toHaveProperty('password')
  })
})

describe('GET /api/users (pagination)', () => {
  let adminToken: string

  beforeAll(async () => {
    const admin = await createTestUser({ role: 'admin' })
    adminToken = generateJWT(admin)
    // Create 15 test users for pagination
    await Promise.all(Array.from({ length: 15 }, (_, i) =>
      createTestUser({ email: `pagtest${i}@example.com` })
    ))
  })

  afterAll(cleanupTestUsers)

  it('returns first page with default limit', async () => {
    const res = await request(app)
      .get('/api/users')
      .set('Authorization', `Bearer ${adminToken}`)
    expect(res.status).toBe(200)
    expect(res.body.data).toBeInstanceOf(Array)
    expect(res.body).toHaveProperty('total')
    expect(res.body).toHaveProperty('page')
    expect(res.body).toHaveProperty('pageSize')
  })

  it('returns empty array for page beyond total', async () => {
    const res = await request(app)
      .get('/api/users?page=9999')
      .set('Authorization', `Bearer ${adminToken}`)
    expect(res.status).toBe(200)
    expect(res.body.data).toHaveLength(0)
  })

  it('returns 400 for negative page number', async () => {
    const res = await request(app)
      .get('/api/users?page=-1')
      .set('Authorization', `Bearer ${adminToken}`)
    expect(res.status).toBe(400)
  })

  it('caps pageSize at maximum allowed value', async () => {
    const res = await request(app)
      .get('/api/users?pageSize=9999')
      .set('Authorization', `Bearer ${adminToken}`)
    expect(res.status).toBe(200)
    expect(res.body.data.length).toBeLessThanOrEqual(100)
  })
})
```

---

### Example 2 — Node.js: File Upload Tests

```typescript
// tests/api/uploads.test.ts
import { describe, it, expect } from 'vitest'
import request from 'supertest'
import path from 'path'
import fs from 'fs'
import { createServer } from '@/test/helpers/server'
import { generateJWT } from '@/test/helpers/auth'
import { createTestUser } from '@/test/helpers/db'

const app = createServer()

describe('POST /api/upload', () => {
  let validToken: string

  beforeAll(async () => {
    const user = await createTestUser({ role: 'user' })
    validToken = generateJWT(user)
  })

  it('returns 401 without authentication', async () => {
    const res = await request(app)
      .post('/api/upload')
      .attach('file', Buffer.from('test'), 'test.pdf')
    expect(res.status).toBe(401)
  })

  it('returns 400 when no file attached', async () => {
    const res = await request(app)
      .post('/api/upload')
      .set('Authorization', `Bearer ${validToken}`)
    expect(res.status).toBe(400)
    expect(res.body.error).toMatch(/file/i)
  })

  it('returns 400 for unsupported file type (exe)', async () => {
    const res = await request(app)
      .post('/api/upload')
      .set('Authorization', `Bearer ${validToken}`)
      .attach('file', Buffer.from('MZ fake exe'), { filename: "virusexe", contentType: 'application/octet-stream' })
    expect(res.status).toBe(400)
    expect(res.body.error).toMatch(/type|format|allowed/i)
  })

  it('returns 413 for oversized file (>10MB)', async () => {
    const largeBuf = Buffer.alloc(11 * 1024 * 1024) // 11MB
    const res = await request(app)
      .post('/api/upload')
      .set('Authorization', `Bearer ${validToken}`)
      .attach('file', largeBuf, { filename: "largepdf", contentType: 'application/pdf' })
    expect(res.status).toBe(413)
  })

  it('returns 400 for empty file (0 bytes)', async () => {
    const res = await request(app)
      .post('/api/upload')
      .set('Authorization', `Bearer ${validToken}`)
      .attach('file', Buffer.alloc(0), { filename: "emptypdf", contentType: 'application/pdf' })
    expect(res.status).toBe(400)
  })

  it('rejects MIME type spoofing (pdf extension but exe content)', async () => {
    // Real malicious file: exe magic bytes but pdf extension
    const fakeExe = Buffer.from('4D5A9000', 'hex') // MZ header
    const res = await request(app)
      .post('/api/upload')
      .set('Authorization', `Bearer ${validToken}`)
      .attach('file', fakeExe, { filename: "documentpdf", contentType: 'application/pdf' })
    // Should detect magic bytes mismatch
    expect([400, 415]).toContain(res.status)
  })

  it('accepts valid PDF file', async () => {
    const pdfHeader = Buffer.from('%PDF-1.4 test content')
    const res = await request(app)
      .post('/api/upload')
      .set('Authorization', `Bearer ${validToken}`)
      .attach('file', pdfHeader, { filename: "validpdf", contentType: 'application/pdf' })
    expect(res.status).toBe(200)
    expect(res.body).toHaveProperty('url')
    expect(res.body).toHaveProperty('id')
  })
})
```

---

### Example 3 — Python: Pytest + httpx (FastAPI)

```python
# tests/api/test_items.py
import pytest
import httpx
from datetime import datetime, timedelta
import jwt

BASE_URL = "http://localhost:8000"
JWT_SECRET = "test-secret"  # use test config, never production secret


def make_token(user_id: str, role: str = "user", expired: bool = False) -> str:
    exp = datetime.utcnow() + (timedelta(hours=-1) if expired else timedelta(hours=1))
    return jwt.encode(
        {"sub": user_id, "role": role, "exp": exp},
        JWT_SECRET,
        algorithm="HS256",
    )


@pytest.fixture
def client():
    with httpx.Client(base_url=BASE_URL) as c:
        yield c


@pytest.fixture
def valid_token():
    return make_token("user-123", role="user")


@pytest.fixture
def admin_token():
    return make_token("admin-456", role="admin")


@pytest.fixture
def expired_token():
    return make_token("user-123", expired=True)


class TestGetItem:
    def test_returns_401_without_auth(self, client):
        res = client.get("/api/items/1")
        assert res.status_code == 401

    def test_returns_401_with_invalid_token(self, client):
        res = client.get("/api/items/1", headers={"Authorization": "Bearer garbage"})
        assert res.status_code == 401

    def test_returns_401_with_expired_token(self, client, expired_token):
        res = client.get("/api/items/1", headers={"Authorization": f"Bearer {expired_token}"})
        assert res.status_code == 401
        assert "expired" in res.json().get("detail", "").lower()

    def test_returns_404_for_nonexistent_item(self, client, valid_token):
        res = client.get(
            "/api/items/99999999",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 404

    def test_returns_400_for_invalid_id_format(self, client, valid_token):
        res = client.get(
            "/api/items/not-a-number",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code in (400, 422)

    def test_returns_200_with_valid_auth(self, client, valid_token, test_item):
        res = client.get(
            f"/api/items/{test_item['id']}",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 200
        data = res.json()
        assert data["id"] == test_item["id"]
        assert "password" not in data


class TestCreateItem:
    def test_returns_422_with_empty_body(self, client, admin_token):
        res = client.post(
            "/api/items",
            json={},
            headers={"Authorization": f"Bearer {admin_token}"},
        )
        assert res.status_code == 422
        errors = res.json()["detail"]
        assert len(errors) > 0

    def test_returns_422_with_missing_required_field(self, client, admin_token):
        res = client.post(
            "/api/items",
            json={"description": "no name field"},
            headers={"Authorization": f"Bearer {admin_token}"},
        )
        assert res.status_code == 422
        fields = [e["loc"][-1] for e in res.json()["detail"]]
        assert "name" in fields

    def test_returns_422_with_wrong_type(self, client, admin_token):
        res = client.post(
            "/api/items",
            json={"name": "test", "price": "not-a-number"},
            headers={"Authorization": f"Bearer {admin_token}"},
        )
        assert res.status_code == 422

    @pytest.mark.parametrize("price", [-1, -0.01])
    def test_returns_422_for_negative_price(self, client, admin_token, price):
        res = client.post(
            "/api/items",
            json={"name": "test", "price": price},
            headers={"Authorization": f"Bearer {admin_token}"},
        )
        assert res.status_code == 422

    def test_returns_422_for_price_exceeding_max(self, client, admin_token):
        res = client.post(
            "/api/items",
            json={"name": "test", "price": 1_000_001},
            headers={"Authorization": f"Bearer {admin_token}"},
        )
        assert res.status_code == 422

    def test_creates_item_successfully(self, client, admin_token):
        res = client.post(
            "/api/items",
            json={"name": "New Widget", "price": 9.99, "category": "tools"},
            headers={"Authorization": f"Bearer {admin_token}"},
        )
        assert res.status_code == 201
        data = res.json()
        assert "id" in data
        assert data["name"] == "New Widget"

    def test_returns_403_for_non_admin(self, client, valid_token):
        res = client.post(
            "/api/items",
            json={"name": "test", "price": 1.0},
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 403


class TestPagination:
    def test_returns_paginated_response(self, client, valid_token):
        res = client.get(
            "/api/items?page=1&size=10",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 200
        data = res.json()
        assert "items" in data
        assert "total" in data
        assert "page" in data
        assert len(data["items"]) <= 10

    def test_empty_result_for_out_of_range_page(self, client, valid_token):
        res = client.get(
            "/api/items?page=99999",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 200
        assert res.json()["items"] == []

    def test_returns_422_for_page_zero(self, client, valid_token):
        res = client.get(
            "/api/items?page=0",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 422

    def test_caps_page_size_at_maximum(self, client, valid_token):
        res = client.get(
            "/api/items?size=9999",
            headers={"Authorization": f"Bearer {valid_token}"},
        )
        assert res.status_code == 200
        assert len(res.json()["items"]) <= 100  # max page size


class TestRateLimiting:
    def test_rate_limit_after_burst(self, client, valid_token):
        responses = []
        for _ in range(60):  # exceed typical 50/min limit
            res = client.get(
                "/api/items",
                headers={"Authorization": f"Bearer {valid_token}"},
            )
            responses.append(res.status_code)
            if res.status_code == 429:
                break
        assert 429 in responses, "Rate limit was not triggered"

    def test_rate_limit_response_has_retry_after(self, client, valid_token):
        for _ in range(60):
            res = client.get("/api/items", headers={"Authorization": f"Bearer {valid_token}"})
            if res.status_code == 429:
                assert "Retry-After" in res.headers or "retry_after" in res.json()
                break
```

---
