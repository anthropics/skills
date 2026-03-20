# Tech Stack Reference

## Next.js (App Router) — Recommended for most SaaS

### Setup
```bash
npx create-next-app@latest my-app --typescript --tailwind --eslint --app
cd my-app
npm install prisma @prisma/client better-auth zod
npx prisma init
```

### Key patterns

**Server Actions for mutations:**
```typescript
// app/actions/post.ts
'use server'
import { db } from '@/lib/db'
import { revalidatePath } from 'next/cache'

export async function createPost(data: { title: string; body: string }, userId: string) {
  const post = await db.post.create({ data: { ...data, userId } })
  revalidatePath('/dashboard')
  return post
}
```

**Route Handler for API:**
```typescript
// app/api/posts/route.ts
import { NextRequest, NextResponse } from 'next/server'
import { db } from '@/lib/db'

export async function GET(req: NextRequest) {
  const { searchParams } = new URL(req.url)
  const page = parseInt(searchParams.get('page') ?? '1')
  const limit = parseInt(searchParams.get('limit') ?? '20')
  const posts = await db.post.findMany({
    skip: (page - 1) * limit,
    take: limit,
    orderBy: { createdAt: 'desc' },
  })
  return NextResponse.json({ posts, page, limit })
}
```

**Prisma schema template:**
```prisma
generator client {
  provider = "prisma-client-js"
}

datasource db {
  provider = "postgresql"
  url      = env("DATABASE_URL")
}

model User {
  id        String   @id @default(cuid())
  email     String   @unique
  name      String?
  password  String
  createdAt DateTime @default(now())
  updatedAt DateTime @updatedAt
  posts     Post[]
}

model Post {
  id        String   @id @default(cuid())
  title     String
  body      String
  published Boolean  @default(false)
  createdAt DateTime @default(now())
  updatedAt DateTime @updatedAt
  user      User     @relation(fields: [userId], references: [id], onDelete: Cascade)
  userId    String

  @@index([userId])
  @@index([createdAt])
}
```

---

## React + Express (Decoupled SPA)

### Setup
```bash
# Frontend
npm create vite@latest client -- --template react-ts
cd client && npm install axios react-router-dom @tanstack/react-query

# Backend
mkdir server && cd server
npm init -y
npm install express cors helmet dotenv bcryptjs jsonwebtoken zod prisma @prisma/client
npm install -D typescript @types/express @types/node ts-node nodemon
```

### Express app structure
```typescript
// server/src/index.ts
import express from 'express'
import cors from 'cors'
import helmet from 'helmet'
import { errorHandler } from './middleware/errorHandler'
import authRoutes from './routes/auth'
import postRoutes from './routes/posts'

const app = express()
app.use(helmet())
app.use(cors({ origin: process.env.CLIENT_URL, credentials: true }))
app.use(express.json())

app.use('/api/auth', authRoutes)
app.use('/api/posts', postRoutes)
app.use(errorHandler)

app.listen(process.env.PORT ?? 3001, () => {
  console.log(`Server running on port ${process.env.PORT ?? 3001}`)
})
```

### JWT middleware
```typescript
// server/src/middleware/auth.ts
import { Request, Response, NextFunction } from 'express'
import jwt from 'jsonwebtoken'

export interface AuthRequest extends Request {
  userId?: string
}

export function requireAuth(req: AuthRequest, res: Response, next: NextFunction) {
  const token = req.headers.authorization?.split(' ')[1]
  if (!token) return res.status(401).json({ error: 'UNAUTHORIZED', message: 'No token provided' })
  try {
    const payload = jwt.verify(token, process.env.JWT_SECRET!) as { userId: string }
    req.userId = payload.userId
    next()
  } catch {
    res.status(401).json({ error: 'UNAUTHORIZED', message: 'Invalid token' })
  }
}
```

### Centralized error handler
```typescript
// server/src/middleware/errorHandler.ts
import { Request, Response, NextFunction } from 'express'

export class AppError extends Error {
  constructor(public statusCode: number, public code: string, message: string) {
    super(message)
  }
}

export function errorHandler(err: Error, req: Request, res: Response, next: NextFunction) {
  if (err instanceof AppError) {
    return res.status(err.statusCode).json({ error: err.code, message: err.message })
  }
  console.error(err)
  res.status(500).json({ error: 'INTERNAL_ERROR', message: 'Something went wrong' })
}
```

---

## FastAPI (Python)

### Setup
```bash
pip install fastapi uvicorn sqlalchemy alembic pydantic-settings python-jose[cryptography] passlib[bcrypt] python-dotenv psycopg2-binary
```

### App structure
```python
# main.py
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from app.routers import auth, posts
from app.database import engine
from app import models

models.Base.metadata.create_all(bind=engine)

app = FastAPI(title="My App")
app.add_middleware(
    CORSMiddleware,
    allow_origins=[settings.CLIENT_URL],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)
app.include_router(auth.router, prefix="/api/auth", tags=["auth"])
app.include_router(posts.router, prefix="/api/posts", tags=["posts"])
```

### SQLAlchemy model template
```python
# app/models.py
from sqlalchemy import Column, String, DateTime, Boolean, ForeignKey, func
from sqlalchemy.orm import relationship
from sqlalchemy.dialects.postgresql import UUID
import uuid
from app.database import Base

class User(Base):
    __tablename__ = "users"
    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    email = Column(String, unique=True, nullable=False, index=True)
    hashed_password = Column(String, nullable=False)
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    posts = relationship("Post", back_populates="author", cascade="all, delete")

class Post(Base):
    __tablename__ = "posts"
    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    title = Column(String, nullable=False)
    body = Column(String, nullable=False)
    published = Column(Boolean, default=False)
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    user_id = Column(UUID(as_uuid=True), ForeignKey("users.id", ondelete="CASCADE"), nullable=False)
    author = relationship("User", back_populates="posts")
```

---

## Static / Astro

### Setup
```bash
npm create astro@latest my-site -- --template minimal
cd my-site
npx astro add tailwind
```

### No backend needed — use:
- Netlify Forms for contact forms
- Supabase or PocketBase for lightweight data
- Stripe Checkout (hosted) for payments

---

## Environment Variables Template

```env
# Database
DATABASE_URL=postgresql://user:password@localhost:5432/myapp

# Auth
JWT_SECRET=your-super-secret-key-min-32-chars
JWT_EXPIRES_IN=15m
REFRESH_TOKEN_SECRET=another-secret-key
REFRESH_EXPIRES_IN=7d

# App
NODE_ENV=development
PORT=3001
CLIENT_URL=http://localhost:5173

# Optional: email
SMTP_HOST=smtp.example.com
SMTP_PORT=587
SMTP_USER=noreply@example.com
SMTP_PASS=your-smtp-password

# Optional: storage
S3_BUCKET=my-bucket
S3_REGION=us-east-1
AWS_ACCESS_KEY_ID=your-key
AWS_SECRET_ACCESS_KEY=your-secret
```
