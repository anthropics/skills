# Backend Security Practices

Security patterns and OWASP Top 10 mitigations for Node.js/Express applications.

## Guide Index

1. [OWASP Top 10 Mitigations](#1-owasp-top-10-mitigations)
2. [Input Validation](#2-input-validation)
3. [SQL Injection Prevention](#3-sql-injection-prevention)
4. [XSS Prevention](#4-xss-prevention)
5. [Authentication Security](#5-authentication-security)
6. [Authorization Patterns](#6-authorization-patterns)
7. [Security Headers](#7-security-headers)
8. [Secrets Management](#8-secrets-management)
9. [Logging and Monitoring](#9-logging-and-monitoring)

---

## 1. OWASP Top 10 Mitigations

### A01: Broken Access Control

```typescript
// BAD: Direct object reference
app.get('/users/:id/profile', async (req, res) => {
  const user = await db.users.findById(req.params.id);
  res.json(user); // Anyone can access any user!
});

// GOOD: Verify ownership
app.get('/users/:id/profile', authenticate, async (req, res) => {
  const userId = req.params.id;

  // Verify user can only access their own data
  if (req.user.id !== userId && !req.user.roles.includes('admin')) {
    return res.status(403).json({ error: { code: 'FORBIDDEN' } });
  }

  const user = await db.users.findById(userId);
  res.json(user);
});
```

### A02: Cryptographic Failures

```typescript
// BAD: Weak hashing
const hash = crypto.createHash('md5').update(password).digest('hex');

// GOOD: bcrypt with appropriate cost factor
import bcrypt from 'bcrypt';

const SALT_ROUNDS = 12; // Adjust based on hardware

async function hashPassword(password: string): Promise<string> {
  return bcrypt.hash(password, SALT_ROUNDS);
}

async function verifyPassword(password: string, hash: string): Promise<boolean> {
  return bcrypt.compare(password, hash);
}
```

### A03: Injection

```typescript
// BAD: String concatenation in SQL
const query = `SELECT * FROM users WHERE email = '${email}'`;

// GOOD: Parameterized queries
const result = await db.query(
  'SELECT * FROM users WHERE email = $1',
  [email]
);
```

### A04: Insecure Design

```typescript
// BAD: No rate limiting on sensitive operations
app.post('/forgot-password', async (req, res) => {
  await sendResetEmail(req.body.email);
  res.json({ message: 'If email exists, reset link sent' });
});

// GOOD: Rate limit + consistent response time
import rateLimit from 'express-rate-limit';

const passwordResetLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 3, // 3 attempts per 15 minutes
  skipSuccessfulRequests: false,
});

app.post('/forgot-password', passwordResetLimiter, async (req, res) => {
  const startTime = Date.now();

  try {
    const user = await db.users.findByEmail(req.body.email);
    if (user) {
      await sendResetEmail(user.email);
    }
  } catch (err) {
    logger.error(err);
  }

  // Consistent response time prevents timing attacks
  const elapsed = Date.now() - startTime;
  const minDelay = 500;
  if (elapsed < minDelay) {
    await sleep(minDelay - elapsed);
  }

  // Same response regardless of email existence
  res.json({ message: 'If email exists, reset link sent' });
});
```

### A05: Security Misconfiguration

```typescript
// BAD: Detailed errors in production
app.use((err, req, res, next) => {
  res.status(500).json({
    error: err.message,
    stack: err.stack, // Exposes internals!
  });
});

// GOOD: Environment-aware error handling
app.use((err: Error, req: Request, res: Response, next: NextFunction) => {
  const requestId = req.id;

  // Always log full error internally
  logger.error({ err, requestId }, 'Unhandled error');

  // Return safe response
  res.status(500).json({
    error: {
      code: 'INTERNAL_ERROR',
      message: process.env.NODE_ENV === 'development'
        ? err.message
        : 'An unexpected error occurred',
      requestId,
    },
  });
});
```

### A06: Vulnerable Components

```bash
# Check for vulnerabilities
npm audit

# Fix automatically where possible
npm audit fix

# Check specific package
npm audit --package-lock-only

# Use Snyk for deeper analysis
npx snyk test
```

```typescript
// Automated dependency updates (package.json)
{
  "scripts": {
    "security:audit": "npm audit --audit-level=high",
    "security:check": "snyk test",
    "preinstall": "npm audit"
  }
}
```

### A07: Authentication Failures

```typescript
// BAD: Weak session management
app.post('/login', async (req, res) => {
  const user = await authenticate(req.body);
  req.session.userId = user.id; // Session fixation risk
  res.json({ success: true });
});

// GOOD: Regenerate session on authentication
app.post('/login', async (req, res) => {
  const user = await authenticate(req.body);

  // Regenerate session to prevent fixation
  req.session.regenerate((err) => {
    if (err) return next(err);

    req.session.userId = user.id;
    req.session.createdAt = Date.now();

    req.session.save((err) => {
      if (err) return next(err);
      res.json({ success: true });
    });
  });
});
```

### A08: Software and Data Integrity Failures

```typescript
// Verify webhook signatures (e.g., Stripe)
import Stripe from 'stripe';

app.post('/webhooks/stripe',
  express.raw({ type: 'application/json' }),
  async (req, res) => {
    const sig = req.headers['stripe-signature'] as string;
    const endpointSecret = process.env.STRIPE_WEBHOOK_SECRET!;

    let event: Stripe.Event;

    try {
      event = stripe.webhooks.constructEvent(
        req.body,
        sig,
        endpointSecret
      );
    } catch (err) {
      logger.warn({ err }, 'Webhook signature verification failed');
      return res.status(400).json({ error: 'Invalid signature' });
    }

    // Process verified event
    await handleStripeEvent(event);
    res.json({ received: true });
  }
);
```

### A09: Security Logging Failures

```typescript
// Comprehensive security logging
import pino from 'pino';

const logger = pino({
  level: process.env.LOG_LEVEL || 'info',
  redact: ['req.headers.authorization', 'req.body.password'], // Redact sensitive
});

// Log security events
function logSecurityEvent(event: {
  type: 'LOGIN_SUCCESS' | 'LOGIN_FAILURE' | 'ACCESS_DENIED' | 'SUSPICIOUS_ACTIVITY';
  userId?: string;
  ip: string;
  userAgent: string;
  details?: Record<string, unknown>;
}) {
  logger.info({
    security: true,
    ...event,
    timestamp: new Date().toISOString(),
  }, `Security event: ${event.type}`);
}

// Usage
app.post('/login', async (req, res) => {
  try {
    const user = await authenticate(req.body);
    logSecurityEvent({
      type: 'LOGIN_SUCCESS',
      userId: user.id,
      ip: req.ip,
      userAgent: req.headers['user-agent'] || '',
    });
    // ...
  } catch (err) {
    logSecurityEvent({
      type: 'LOGIN_FAILURE',
      ip: req.ip,
      userAgent: req.headers['user-agent'] || '',
      details: { email: req.body.email },
    });
    // ...
  }
});
```

### A10: Server-Side Request Forgery (SSRF)

```typescript
// BAD: Unvalidated URL fetch
app.post('/fetch-url', async (req, res) => {
  const response = await fetch(req.body.url); // SSRF vulnerability!
  res.json({ data: await response.text() });
});

// GOOD: URL allowlist and validation
import { URL } from 'url';

const ALLOWED_HOSTS = ['api.example.com', 'cdn.example.com'];

function isAllowedUrl(urlString: string): boolean {
  try {
    const url = new URL(urlString);

    // Block internal IPs
    const blockedPatterns = [
      /^localhost$/i,
      /^127\./,
      /^10\./,
      /^172\.(1[6-9]|2[0-9]|3[0-1])\./,
      /^192\.168\./,
      /^0\./,
      /^169\.254\./,
      /^\[::1\]$/,
      /^metadata\.google\.internal$/,
      /^169\.254\.169\.254$/,
    ];

    if (blockedPatterns.some(p => p.test(url.hostname))) {
      return false;
    }

    // Only allow HTTPS
    if (url.protocol !== 'https:') {
      return false;
    }

    // Check allowlist
    return ALLOWED_HOSTS.includes(url.hostname);
  } catch {
    return false;
  }
}

app.post('/fetch-url', async (req, res) => {
  const { url } = req.body;

  if (!isAllowedUrl(url)) {
    return res.status(400).json({ error: { code: 'INVALID_URL' } });
  }

  const response = await fetch(url, {
    timeout: 5000,
    follow: 0, // Don't follow redirects
  });

  res.json({ data: await response.text() });
});
```

---

## 2. Input Validation

### Schema Validation with Zod

```typescript
import { z } from 'zod';

// Define schemas
const CreateUserSchema = z.object({
  email: z.string().email().max(255).toLowerCase(),
  password: z.string()
    .min(8, 'Password must be at least 8 characters')
    .max(72, 'Password must be at most 72 characters') // bcrypt limit
    .regex(/[A-Z]/, 'Password must contain uppercase letter')
    .regex(/[a-z]/, 'Password must contain lowercase letter')
    .regex(/[0-9]/, 'Password must contain number'),
  name: z.string().min(1).max(100).trim(),
  age: z.number().int().min(18).max(120).optional(),
});

const PaginationSchema = z.object({
  limit: z.coerce.number().int().min(1).max(100).default(20),
  offset: z.coerce.number().int().min(0).default(0),
  sort: z.enum(['asc', 'desc']).default('desc'),
});

// Validation middleware
function validate<T>(schema: z.ZodSchema<T>) {
  return (req: Request, res: Response, next: NextFunction) => {
    const result = schema.safeParse(req.body);

    if (!result.success) {
      const details = result.error.errors.map(err => ({
        field: err.path.join('.'),
        code: err.code,
        message: err.message,
      }));

      return res.status(400).json({
        error: {
          code: 'VALIDATION_ERROR',
          message: 'Request validation failed',
          details,
        },
      });
    }

    req.body = result.data;
    next();
  };
}

// Usage
app.post('/users', validate(CreateUserSchema), async (req, res) => {
  // req.body is now typed and validated
  const user = await userService.create(req.body);
  res.status(201).json(user);
});
```

### Sanitization

```typescript
import DOMPurify from 'isomorphic-dompurify';
import xss from 'xss';

// HTML sanitization for rich text fields
function sanitizeHtml(dirty: string): string {
  return DOMPurify.sanitize(dirty, {
    ALLOWED_TAGS: ['b', 'i', 'em', 'strong', 'a', 'p', 'br'],
    ALLOWED_ATTR: ['href'],
  });
}

// Plain text sanitization (strip all HTML)
function sanitizePlainText(dirty: string): string {
  return xss(dirty, {
    whiteList: {},
    stripIgnoreTag: true,
    stripIgnoreTagBody: ['script'],
  });
}

// File path sanitization
import path from 'path';

function sanitizePath(userPath: string, baseDir: string): string | null {
  const resolved = path.resolve(baseDir, userPath);

  // Prevent directory traversal
  if (!resolved.startsWith(baseDir)) {
    return null;
  }

  return resolved;
}
```

---

## 3. SQL Injection Prevention

### Parameterized Queries

```typescript
// BAD: String interpolation
const email = "'; DROP TABLE users; --";
db.query(`SELECT * FROM users WHERE email = '${email}'`);

// GOOD: Parameterized query (pg)
const result = await db.query(
  'SELECT * FROM users WHERE email = $1',
  [email]
);

// GOOD: Parameterized query (mysql2)
const [rows] = await connection.execute(
  'SELECT * FROM users WHERE email = ?',
  [email]
);
```

### Query Builders

```typescript
// Using Knex.js
const users = await knex('users')
  .where('email', email) // Automatically parameterized
  .andWhere('status', 'active')
  .select('id', 'name', 'email');

// Dynamic WHERE with safe column names
const ALLOWED_COLUMNS = ['name', 'email', 'created_at'] as const;

function buildUserQuery(filters: Record<string, string>) {
  let query = knex('users').select('id', 'name', 'email');

  for (const [column, value] of Object.entries(filters)) {
    // Validate column name against allowlist
    if (ALLOWED_COLUMNS.includes(column as any)) {
      query = query.where(column, value);
    }
  }

  return query;
}
```

### ORM Safety

```typescript
// Prisma (safe by default)
const user = await prisma.user.findUnique({
  where: { email }, // Automatically escaped
});

// TypeORM (safe by default)
const user = await userRepository.findOne({
  where: { email }, // Automatically escaped
});

// DANGER: Raw queries still require parameterization
// BAD
await prisma.$queryRawUnsafe(`SELECT * FROM users WHERE email = '${email}'`);

// GOOD
await prisma.$queryRaw`SELECT * FROM users WHERE email = ${email}`;
```

---

## 4. XSS Prevention

### Output Encoding

```typescript
// Server-side template rendering (EJS)
// In template: <%= userInput %> (escaped)
// NOT: <%- userInput %> (raw, dangerous)

// Manual HTML encoding
function escapeHtml(str: string): string {
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}

// JSON response (automatically safe in modern frameworks)
res.json({ message: userInput }); // JSON.stringify escapes by default
```

### Content Security Policy

```typescript
import helmet from 'helmet';

app.use(helmet.contentSecurityPolicy({
  directives: {
    defaultSrc: ["'self'"],
    scriptSrc: ["'self'", "'strict-dynamic'"],
    styleSrc: ["'self'", "'unsafe-inline'"], // Consider using nonces
    imgSrc: ["'self'", "data:", "https:"],
    fontSrc: ["'self'"],
    objectSrc: ["'none'"],
    frameAncestors: ["'none'"],
    baseUri: ["'self'"],
    formAction: ["'self'"],
    upgradeInsecureRequests: [],
  },
}));
```

### API Response Safety

```typescript
// Set correct Content-Type for JSON APIs
app.use((req, res, next) => {
  res.setHeader('Content-Type', 'application/json; charset=utf-8');
  res.setHeader('X-Content-Type-Options', 'nosniff');
  next();
});

// Disable JSONP (if not needed)
// Don't implement callback parameter handling

// Safe JSON response
res.json({
  data: sanitizedData,
  // Never reflect raw user input
});
```

---

## 5. Authentication Security

### Password Storage

```typescript
import bcrypt from 'bcrypt';
import { randomBytes } from 'crypto';

const SALT_ROUNDS = 12;

async function hashPassword(password: string): Promise<string> {
  return bcrypt.hash(password, SALT_ROUNDS);
}

async function verifyPassword(password: string, hash: string): Promise<boolean> {
  return bcrypt.compare(password, hash);
}

// For password reset tokens
function generateSecureToken(): string {
  return randomBytes(32).toString('hex');
}

// Token expiration (store in DB)
interface PasswordResetToken {
  token: string; // Hashed
  userId: string;
  expiresAt: Date; // 1 hour from creation
}
```

### JWT Best Practices

```typescript
import jwt from 'jsonwebtoken';

// Use asymmetric keys in production
const PRIVATE_KEY = process.env.JWT_PRIVATE_KEY!;
const PUBLIC_KEY = process.env.JWT_PUBLIC_KEY!;

interface AccessTokenPayload {
  sub: string; // User ID
  email: string;
  roles: string[];
  iat: number;
  exp: number;
}

function generateAccessToken(user: User): string {
  const payload: Omit<AccessTokenPayload, 'iat' | 'exp'> = {
    sub: user.id,
    email: user.email,
    roles: user.roles,
  };

  return jwt.sign(payload, PRIVATE_KEY, {
    algorithm: 'RS256',
    expiresIn: '15m',
    issuer: 'api.example.com',
    audience: 'example.com',
  });
}

function verifyAccessToken(token: string): AccessTokenPayload {
  return jwt.verify(token, PUBLIC_KEY, {
    algorithms: ['RS256'],
    issuer: 'api.example.com',
    audience: 'example.com',
  }) as AccessTokenPayload;
}

// Refresh tokens should be stored in DB and rotated
interface RefreshToken {
  id: string;
  token: string; // Hashed
  userId: string;
  expiresAt: Date;
  family: string; // For rotation detection
  isRevoked: boolean;
}
```

### Session Management

```typescript
import session from 'express-session';
import RedisStore from 'connect-redis';
import { createClient } from 'redis';

const redisClient = createClient({ url: process.env.REDIS_URL });

app.use(session({
  store: new RedisStore({ client: redisClient }),
  name: 'sessionId', // Don't use default 'connect.sid'
  secret: process.env.SESSION_SECRET!,
  resave: false,
  saveUninitialized: false,
  cookie: {
    secure: process.env.NODE_ENV === 'production',
    httpOnly: true,
    sameSite: 'strict',
    maxAge: 24 * 60 * 60 * 1000, // 24 hours
    domain: process.env.COOKIE_DOMAIN,
  },
}));

// Regenerate session on privilege change
async function elevateSession(req: Request): Promise<void> {
  return new Promise((resolve, reject) => {
    const userId = req.session.userId;
    req.session.regenerate((err) => {
      if (err) return reject(err);
      req.session.userId = userId;
      req.session.elevated = true;
      req.session.elevatedAt = Date.now();
      resolve();
    });
  });
}
```

---

## 6. Authorization Patterns

### Role-Based Access Control (RBAC)

```typescript
type Role = 'user' | 'moderator' | 'admin';
type Permission = 'read:users' | 'write:users' | 'delete:users' | 'read:admin';

const ROLE_PERMISSIONS: Record<Role, Permission[]> = {
  user: ['read:users'],
  moderator: ['read:users', 'write:users'],
  admin: ['read:users', 'write:users', 'delete:users', 'read:admin'],
};

function hasPermission(userRoles: Role[], required: Permission): boolean {
  return userRoles.some(role =>
    ROLE_PERMISSIONS[role]?.includes(required)
  );
}

// Middleware
function requirePermission(permission: Permission) {
  return (req: Request, res: Response, next: NextFunction) => {
    if (!hasPermission(req.user.roles, permission)) {
      return res.status(403).json({
        error: { code: 'FORBIDDEN', message: 'Insufficient permissions' },
      });
    }
    next();
  };
}

// Usage
app.delete('/users/:id',
  authenticate,
  requirePermission('delete:users'),
  deleteUserHandler
);
```

### Attribute-Based Access Control (ABAC)

```typescript
interface AccessContext {
  user: { id: string; roles: string[]; department: string };
  resource: { ownerId: string; department: string; sensitivity: string };
  action: 'read' | 'write' | 'delete';
  environment: { time: Date; ip: string };
}

interface Policy {
  name: string;
  condition: (ctx: AccessContext) => boolean;
}

const policies: Policy[] = [
  {
    name: 'owner-full-access',
    condition: (ctx) => ctx.resource.ownerId === ctx.user.id,
  },
  {
    name: 'same-department-read',
    condition: (ctx) =>
      ctx.action === 'read' &&
      ctx.resource.department === ctx.user.department,
  },
  {
    name: 'admin-override',
    condition: (ctx) => ctx.user.roles.includes('admin'),
  },
  {
    name: 'no-sensitive-outside-hours',
    condition: (ctx) => {
      const hour = ctx.environment.time.getHours();
      return ctx.resource.sensitivity !== 'high' || (hour >= 9 && hour <= 17);
    },
  },
];

function evaluateAccess(ctx: AccessContext): boolean {
  return policies.some(policy => policy.condition(ctx));
}
```

---

## 7. Security Headers

### Complete Helmet Configuration

```typescript
import helmet from 'helmet';

app.use(helmet({
  // Content Security Policy
  contentSecurityPolicy: {
    directives: {
      defaultSrc: ["'self'"],
      scriptSrc: ["'self'"],
      styleSrc: ["'self'", "'unsafe-inline'"],
      imgSrc: ["'self'", "data:", "https:"],
      connectSrc: ["'self'", "https://api.example.com"],
      fontSrc: ["'self'"],
      objectSrc: ["'none'"],
      mediaSrc: ["'none'"],
      frameSrc: ["'none'"],
    },
  },
  // Strict Transport Security
  hsts: {
    maxAge: 31536000,
    includeSubDomains: true,
    preload: true,
  },
  // Prevent clickjacking
  frameguard: { action: 'deny' },
  // Prevent MIME sniffing
  noSniff: true,
  // XSS filter (legacy browsers)
  xssFilter: true,
  // Hide X-Powered-By
  hidePoweredBy: true,
  // Referrer policy
  referrerPolicy: { policy: 'strict-origin-when-cross-origin' },
  // Cross-origin policies
  crossOriginEmbedderPolicy: false, // Enable if using SharedArrayBuffer
  crossOriginOpenerPolicy: { policy: 'same-origin' },
  crossOriginResourcePolicy: { policy: 'same-origin' },
}));

// CORS configuration
import cors from 'cors';

app.use(cors({
  origin: ['https://example.com', 'https://app.example.com'],
  methods: ['GET', 'POST', 'PUT', 'DELETE', 'PATCH'],
  allowedHeaders: ['Content-Type', 'Authorization'],
  credentials: true,
  maxAge: 86400, // 24 hours
}));
```

### Header Reference

| Header | Purpose | Value |
|--------|---------|-------|
| `Strict-Transport-Security` | Force HTTPS | `max-age=31536000; includeSubDomains; preload` |
| `Content-Security-Policy` | Prevent XSS | See above |
| `X-Content-Type-Options` | Prevent MIME sniffing | `nosniff` |
| `X-Frame-Options` | Prevent clickjacking | `DENY` |
| `Referrer-Policy` | Control referrer info | `strict-origin-when-cross-origin` |
| `Permissions-Policy` | Feature restrictions | `geolocation=(), microphone=()` |

---

## 8. Secrets Management

### Environment Variables

```typescript
// config/secrets.ts
import { z } from 'zod';

const SecretsSchema = z.object({
  DATABASE_URL: z.string().url(),
  JWT_SECRET: z.string().min(32),
  JWT_PRIVATE_KEY: z.string(),
  JWT_PUBLIC_KEY: z.string(),
  REDIS_URL: z.string().url(),
  STRIPE_SECRET_KEY: z.string().startsWith('sk_'),
  STRIPE_WEBHOOK_SECRET: z.string().startsWith('whsec_'),
});

// Validate on startup
export const secrets = SecretsSchema.parse(process.env);

// NEVER log secrets
console.log('Config loaded:', {
  database: secrets.DATABASE_URL.replace(/\/\/.*@/, '//***@'),
  redis: 'configured',
  stripe: 'configured',
});
```

### Secret Rotation

```typescript
// Support multiple keys during rotation
const JWT_SECRETS = [
  process.env.JWT_SECRET_CURRENT!,
  process.env.JWT_SECRET_PREVIOUS!, // Keep for grace period
].filter(Boolean);

function verifyTokenWithRotation(token: string): TokenPayload | null {
  for (const secret of JWT_SECRETS) {
    try {
      return jwt.verify(token, secret) as TokenPayload;
    } catch {
      continue;
    }
  }
  return null;
}
```

### Vault Integration

```typescript
import Vault from 'node-vault';

const vault = Vault({
  endpoint: process.env.VAULT_ADDR,
  token: process.env.VAULT_TOKEN,
});

async function getSecret(path: string): Promise<string> {
  const result = await vault.read(`secret/data/${path}`);
  return result.data.data.value;
}

// Cache secrets with TTL
const secretsCache = new Map<string, { value: string; expiresAt: number }>();
const CACHE_TTL = 5 * 60 * 1000; // 5 minutes

async function getCachedSecret(path: string): Promise<string> {
  const cached = secretsCache.get(path);
  if (cached && cached.expiresAt > Date.now()) {
    return cached.value;
  }

  const value = await getSecret(path);
  secretsCache.set(path, { value, expiresAt: Date.now() + CACHE_TTL });
  return value;
}
```

---

## 9. Logging and Monitoring

### Security Event Logging

```typescript
import pino from 'pino';

const logger = pino({
  level: 'info',
  redact: {
    paths: [
      'req.headers.authorization',
      'req.headers.cookie',
      'req.body.password',
      'req.body.token',
      '*.password',
      '*.secret',
      '*.apiKey',
    ],
    censor: '[REDACTED]',
  },
});

// Security event types
type SecurityEventType =
  | 'AUTH_SUCCESS'
  | 'AUTH_FAILURE'
  | 'AUTH_LOCKOUT'
  | 'PASSWORD_CHANGED'
  | 'PASSWORD_RESET_REQUEST'
  | 'PERMISSION_DENIED'
  | 'RATE_LIMIT_EXCEEDED'
  | 'SUSPICIOUS_ACTIVITY'
  | 'TOKEN_REVOKED';

interface SecurityEvent {
  type: SecurityEventType;
  userId?: string;
  ip: string;
  userAgent: string;
  path: string;
  details?: Record<string, unknown>;
}

function logSecurityEvent(event: SecurityEvent): void {
  logger.info({
    security: true,
    ...event,
    timestamp: new Date().toISOString(),
  }, `Security: ${event.type}`);
}
```

### Request Logging

```typescript
import pinoHttp from 'pino-http';

app.use(pinoHttp({
  logger,
  genReqId: (req) => req.headers['x-request-id'] || crypto.randomUUID(),
  serializers: {
    req: (req) => ({
      id: req.id,
      method: req.method,
      url: req.url,
      remoteAddress: req.remoteAddress,
      // Don't log headers by default (may contain sensitive data)
    }),
    res: (res) => ({
      statusCode: res.statusCode,
    }),
  },
  customLogLevel: (req, res, err) => {
    if (res.statusCode >= 500 || err) return 'error';
    if (res.statusCode >= 400) return 'warn';
    return 'info';
  },
}));
```

### Alerting Thresholds

| Metric | Warning | Critical |
|--------|---------|----------|
| Failed logins per IP (15 min) | > 5 | > 10 |
| Failed logins per account (1 hour) | > 3 | > 5 |
| 403 responses per IP (5 min) | > 10 | > 50 |
| 500 errors (5 min) | > 5 | > 20 |
| Request rate per IP (1 min) | > 100 | > 500 |

---

## Quick Reference: Security Checklist

### Authentication
- [ ] bcrypt with cost >= 12 for password hashing
- [ ] JWT with RS256, short expiry (15-30 min)
- [ ] Refresh token rotation with family detection
- [ ] Session regeneration on login
- [ ] Secure cookie flags (httpOnly, secure, sameSite)

### Input Validation
- [ ] Schema validation on all inputs (Zod)
- [ ] Parameterized queries (never string concat)
- [ ] File path sanitization
- [ ] Content-Type validation

### Headers
- [ ] Strict-Transport-Security
- [ ] Content-Security-Policy
- [ ] X-Content-Type-Options: nosniff
- [ ] X-Frame-Options: DENY
- [ ] CORS with specific origins

### Logging
- [ ] Redact sensitive fields
- [ ] Log security events
- [ ] Include request IDs
- [ ] Alert on anomalies

### Dependencies
- [ ] npm audit in CI
- [ ] Automated dependency updates
- [ ] Lock file committed
