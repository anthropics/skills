---
name: fullstack-website-designer
description: Design and build complete full-stack websites and web applications from scratch, covering frontend UI, backend API, database schema, and deployment configuration. Use this skill whenever a user wants to create a website, web app, SaaS product, portfolio, e-commerce site, dashboard, or any web project requiring both a user interface and server-side logic — even if they say "just make me a website" or "build me an app". Also use when the user asks to add a backend to an existing frontend, design an API, choose a tech stack, or scaffold a new web project. This skill produces production-ready, well-architected code with a clear aesthetic vision for the UI and a solid backend foundation.
---

# Full-Stack Website Designer

Design and build complete web applications: from UI aesthetics and component architecture through API design, data modeling, and deployment-ready configuration.

---

## Phase 1: Discovery

Before writing any code, clarify the scope. Ask (or infer from context) the following:

- **Purpose**: What does this site/app do? Who uses it?
- **Core features**: What are the 3–5 must-have features for V1?
- **Auth**: Do users need to log in? (yes/no/optional)
- **Data**: What needs to be stored? Will there be user-generated content?
- **Scale expectation**: Is this a personal project, startup MVP, or production system?
- **Constraints**: Preferred languages/frameworks? Hosting preference (Vercel, Railway, AWS, self-hosted)? Budget?

If the user gives a quick prompt like "build me a recipe sharing site", make reasonable assumptions and state them clearly at the start — don't interrogate before producing anything.

---

## Phase 2: Architecture Decision

Based on discovery, choose the stack. Explain the choice briefly.

### Recommended Stacks

**Lightweight / Portfolio / Marketing site:**
- Frontend: Vanilla HTML/CSS/JS or Astro
- Backend: None (static) or lightweight Edge functions
- Hosting: Vercel, Netlify, GitHub Pages

**Modern SPA / Dashboard / SaaS MVP:**
- Frontend: React + TypeScript + Vite + Tailwind CSS
- Backend: Node.js + Express (or Hono/Fastify) + TypeScript
- Database: PostgreSQL (via Prisma ORM) or SQLite for local-first
- Auth: JWT or session-based; use `better-auth` or `lucia` for quick setup
- Hosting: Vercel (frontend) + Railway or Render (backend + DB)

**Python-native / Data-heavy / AI-integrated:**
- Frontend: React or HTMX
- Backend: FastAPI (Python) + SQLAlchemy + Alembic
- Database: PostgreSQL
- Hosting: Railway, Fly.io, or Docker on any VPS

**Full-stack framework (optimal for teams and fast iteration):**
- Next.js (App Router) + TypeScript + Prisma + PostgreSQL
- Auth: NextAuth.js / Auth.js
- Hosting: Vercel

State the chosen stack and justify it in 1–3 sentences. Then proceed.

---

## Phase 3: UI/UX Design

Design the interface with genuine aesthetic intent. Follow these principles:

### Design Philosophy

Pick a clear, opinionated visual direction BEFORE writing CSS. Options include:
- Editorial / magazine-style (high contrast, expressive type)
- Refined minimal (whitespace-driven, premium feel)
- Bold brutalist (raw grid, heavy type, deliberate clashing)
- Playful / product (rounded, colorful, animated)
- Dark / technical (terminal-inspired, developer tool aesthetic)
- Warm / organic (earthy palette, soft shapes, handcrafted feel)

State your chosen direction in a single line: *"I'm going for a [direction] aesthetic because [reason tied to context]."*

### Typography
- Select two fonts from Google Fonts, Bunny Fonts, or system stacks that fit the aesthetic. Pair a display font (headings) with a text font (body).
- NEVER default to Inter, Roboto, Arial, or generic system-ui for display.
- Define font scale in CSS custom properties.

### Color
- Build a 5-token color system: `--color-bg`, `--color-surface`, `--color-text`, `--color-accent`, `--color-muted`.
- Commit to a palette — dominant neutral + 1–2 accent colors. Avoid purple gradients on white.
- Support dark mode if the aesthetic calls for it (use `prefers-color-scheme` or a toggle).

### Layout
- Use CSS Grid for page structure; Flexbox for component internals.
- Consider unexpected spatial moves: asymmetric hero sections, overlapping elements, generous whitespace OR controlled density.
- Design for mobile-first; all layouts must be responsive.

### Component Design

For each major UI section (header/nav, hero, content areas, cards, forms, footer), define the component structure, then implement it. Include:
- Hover and focus states
- Loading/skeleton states where data is async
- Empty states for lists/tables
- Error states for forms

---

## Phase 4: Backend Architecture

### API Design

Design REST endpoints (or GraphQL schema) that cover all the required features. Follow these conventions:

```
GET    /api/resource          → list (paginated)
POST   /api/resource          → create
GET    /api/resource/:id      → get one
PUT    /api/resource/:id      → full update
PATCH  /api/resource/:id      → partial update
DELETE /api/resource/:id      → delete
```

For each endpoint, document:
- Request body / query params
- Response shape
- Auth requirement (public / authenticated / owner-only)
- Errors that can be returned

### Database Schema

Design tables/collections that reflect the data model. For relational DBs:

```sql
-- Example: always include these fields on user-owned records
id          UUID PRIMARY KEY DEFAULT gen_random_uuid()
created_at  TIMESTAMP WITH TIME ZONE DEFAULT now()
updated_at  TIMESTAMP WITH TIME ZONE DEFAULT now()
user_id     UUID REFERENCES users(id) ON DELETE CASCADE
```

Apply normalization where it matters (avoid JSON blobs for queryable data). Denormalize intentionally for read-heavy paths.

Provide:
1. Full schema as SQL (or Prisma schema)
2. Indexes for common query patterns
3. Seed data for development

### Authentication (if needed)

Implement stateless JWT auth unless sessions are explicitly needed:
- `POST /api/auth/register` — hash password with bcrypt (cost 12+)
- `POST /api/auth/login` — return access token (15m) + refresh token (7d)
- `POST /api/auth/refresh` — rotate refresh token
- Middleware to validate JWT on protected routes

Store refresh tokens in httpOnly cookies. Never store tokens in localStorage.

### Backend Code Quality

- Centralized error handler with consistent JSON error format:
  ```json
  { "error": "RESOURCE_NOT_FOUND", "message": "Post with id X does not exist" }
  ```
- Input validation on all endpoints (use `zod` for TypeScript, `pydantic` for Python)
- Rate limiting on auth endpoints
- CORS configured for the frontend origin
- Environment variables for all secrets (never hardcoded)

---

## Phase 5: Project Scaffold

Generate the complete file structure and all key files. Produce real, runnable code — not pseudocode or placeholders.

### File Structure (example for Next.js)

```
my-app/
├── app/
│   ├── (auth)/
│   │   ├── login/page.tsx
│   │   └── register/page.tsx
│   ├── (dashboard)/
│   │   └── dashboard/page.tsx
│   ├── api/
│   │   └── [...route]/route.ts
│   ├── globals.css
│   ├── layout.tsx
│   └── page.tsx
├── components/
│   ├── ui/           ← shared primitives
│   └── features/     ← domain-specific
├── lib/
│   ├── db.ts
│   ├── auth.ts
│   └── utils.ts
├── prisma/
│   └── schema.prisma
├── public/
├── .env.example
├── package.json
└── README.md
```

Adapt structure to the chosen stack.

### Deliverables

Always produce:
1. **All source files** — fully implemented, not stub files
2. **`.env.example`** — all required env vars listed with descriptions
3. **`package.json` / `requirements.txt` / `pyproject.toml`** — with all dependencies pinned
4. **`README.md`** — setup instructions: clone → install → configure env → run dev → run prod

Optionally produce:
- `docker-compose.yml` if DB needs local setup
- `Dockerfile` if containerization is requested
- CI/CD config (GitHub Actions) for auto-deploy

---

## Phase 6: Code Quality Checklist

Before presenting the final output, verify:

- [ ] All API routes have input validation
- [ ] Auth middleware applied to all protected routes
- [ ] No secrets in source code (only env vars)
- [ ] Database queries use parameterized statements (no SQL injection risk)
- [ ] Passwords hashed with bcrypt or argon2
- [ ] CORS restricted to expected origins
- [ ] Frontend forms have client-side + server-side validation
- [ ] All images have `alt` text; interactive elements are keyboard accessible
- [ ] HTTP errors return consistent JSON (not HTML stack traces)
- [ ] `.env.example` covers every secret / config value used

---

## Output Format

Structure your response as:

1. **Stack choice + rationale** (2–3 sentences)
2. **Aesthetic direction** (1 sentence + color/font decisions)
3. **Architecture overview** (API endpoints table, DB schema summary)
4. **Full code** — organized by file, using markdown code blocks with file paths as headers:
   ```
   // src/app/page.tsx
   [code]
   ```
5. **Setup instructions** — minimal steps to get it running locally
6. **Next steps** — 3–5 recommended enhancements for V2

---

## Reference Files

Load these as needed during implementation:

- **[Tech Stack Details](./references/stacks.md)** — detailed setup patterns for each stack variant
- **[API Design Patterns](./references/api-patterns.md)** — pagination, filtering, error handling conventions
- **[Database Patterns](./references/db-patterns.md)** — schema templates, migration patterns, indexing strategy
