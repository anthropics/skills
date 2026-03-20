# API Design Patterns

## Pagination

Always paginate list endpoints. Use cursor-based for large datasets, offset for simple UIs.

### Offset pagination (simple)
```
GET /api/posts?page=1&limit=20

Response:
{
  "data": [...],
  "pagination": {
    "page": 1,
    "limit": 20,
    "total": 143,
    "totalPages": 8,
    "hasNext": true,
    "hasPrev": false
  }
}
```

### Cursor pagination (scalable)
```
GET /api/posts?cursor=<last-id>&limit=20

Response:
{
  "data": [...],
  "nextCursor": "clx9...",
  "hasMore": true
}
```

Use cursor pagination when: the dataset may be millions of rows, or the user scrolls infinitely.

---

## Filtering and Sorting

```
GET /api/posts?status=published&author=user123&sort=createdAt&order=desc

// Parse in handler:
const { status, author, sort = 'createdAt', order = 'desc' } = req.query
```

Whitelist allowed sort fields to prevent injection:
```typescript
const ALLOWED_SORT = ['createdAt', 'title', 'updatedAt'] as const
const sortField = ALLOWED_SORT.includes(sort as any) ? sort : 'createdAt'
```

---

## Standard Error Format

All errors must return this shape:
```json
{
  "error": "SNAKE_CASE_ERROR_CODE",
  "message": "Human-readable explanation",
  "details": {}  // optional: field-level validation errors
}
```

Common error codes:
| Code | HTTP Status | When |
|---|---|---|
| `UNAUTHORIZED` | 401 | Missing or invalid auth token |
| `FORBIDDEN` | 403 | Authenticated but not allowed |
| `NOT_FOUND` | 404 | Resource doesn't exist |
| `VALIDATION_ERROR` | 422 | Invalid input (include `details` with field errors) |
| `CONFLICT` | 409 | Duplicate unique value |
| `RATE_LIMITED` | 429 | Too many requests |
| `INTERNAL_ERROR` | 500 | Unexpected server error |

Field-level validation errors:
```json
{
  "error": "VALIDATION_ERROR",
  "message": "Invalid input",
  "details": {
    "email": "Must be a valid email address",
    "password": "Must be at least 8 characters"
  }
}
```

---

## Input Validation (Zod)

```typescript
import { z } from 'zod'

const CreatePostSchema = z.object({
  title: z.string().min(1).max(200),
  body: z.string().min(1),
  published: z.boolean().optional().default(false),
  tags: z.array(z.string()).max(10).optional(),
})

// In handler:
const result = CreatePostSchema.safeParse(req.body)
if (!result.success) {
  return res.status(422).json({
    error: 'VALIDATION_ERROR',
    message: 'Invalid input',
    details: result.error.flatten().fieldErrors,
  })
}
const data = result.data
```

---

## Rate Limiting

```typescript
import rateLimit from 'express-rate-limit'

// Strict limit for auth endpoints
export const authLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15 min
  max: 10,
  message: { error: 'RATE_LIMITED', message: 'Too many attempts, try again in 15 minutes' },
})

// General API limit
export const apiLimiter = rateLimit({
  windowMs: 60 * 1000, // 1 min
  max: 100,
})

app.use('/api/auth', authLimiter)
app.use('/api', apiLimiter)
```

---

## Async Handler Wrapper

Avoid try/catch boilerplate in every route:
```typescript
export const asyncHandler = (fn: Function) => (req: Request, res: Response, next: NextFunction) =>
  Promise.resolve(fn(req, res, next)).catch(next)

// Usage:
router.get('/', asyncHandler(async (req, res) => {
  const posts = await db.post.findMany()
  res.json({ data: posts })
}))
```

---

## File Uploads

Use `multer` for multipart, pre-signed URLs for large files:

```typescript
// Small files (< 5MB): multer + store in S3
import multer from 'multer'
const upload = multer({ storage: multer.memoryStorage(), limits: { fileSize: 5 * 1024 * 1024 } })

router.post('/upload', requireAuth, upload.single('file'), asyncHandler(async (req, res) => {
  const { originalname, buffer, mimetype } = req.file!
  const key = `uploads/${req.userId}/${Date.now()}-${originalname}`
  await s3.putObject({ Bucket: process.env.S3_BUCKET!, Key: key, Body: buffer, ContentType: mimetype })
  res.json({ url: `https://${process.env.S3_BUCKET}.s3.amazonaws.com/${key}` })
}))

// Large files: return pre-signed upload URL
router.post('/upload-url', requireAuth, asyncHandler(async (req, res) => {
  const { filename, contentType } = req.body
  const key = `uploads/${req.userId}/${Date.now()}-${filename}`
  const url = await getSignedUrl(s3Client, new PutObjectCommand({
    Bucket: process.env.S3_BUCKET!,
    Key: key,
    ContentType: contentType,
  }), { expiresIn: 300 })
  res.json({ uploadUrl: url, key })
}))
```
