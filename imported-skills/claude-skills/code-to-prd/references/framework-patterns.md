# Framework-Specific Patterns

Quick reference for identifying routes, components, state, and APIs across frontend and backend frameworks.

## React (CRA / Vite)

| Aspect | Where to Look |
|--------|--------------|
| Routes | `react-router-dom` — `<Route path="...">` or `createBrowserRouter` |
| Components | `.tsx` / `.jsx` files, default exports |
| State | Redux (`store/`), Zustand, Jotai, Recoil, React Context |
| API | `axios`, `fetch`, TanStack Query (`useQuery`), SWR (`useSWR`) |
| Forms | React Hook Form, Formik, Ant Design Form, custom `useState` |
| i18n | `react-i18next`, `react-intl` |

## Next.js (App Router)

| Aspect | Where to Look |
|--------|--------------|
| Routes | `app/` directory — `page.tsx` = route, folders = segments |
| Layouts | `layout.tsx` per directory |
| Loading | `loading.tsx`, `error.tsx`, `not-found.tsx` |
| API routes | `app/api/` or `pages/api/` (Pages Router) |
| Server actions | `"use server"` directive |
| Middleware | `middleware.ts` at root |

## Next.js (Pages Router)

| Aspect | Where to Look |
|--------|--------------|
| Routes | `pages/` directory — filename = route |
| Data fetching | `getServerSideProps`, `getStaticProps`, `getStaticPaths` |
| API routes | `pages/api/` |

## Vue 3

| Aspect | Where to Look |
|--------|--------------|
| Routes | `vue-router` — `routes` array in `router/index.ts` |
| Components | `.vue` SFCs (`<template>`, `<script setup>`, `<style>`) |
| State | Pinia (`stores/`), Vuex (`store/`) |
| API | `axios`, `fetch`, VueQuery |
| Forms | VeeValidate, FormKit, custom `ref()` / `reactive()` |
| i18n | `vue-i18n` |

## Nuxt 3

| Aspect | Where to Look |
|--------|--------------|
| Routes | `pages/` directory (file-system routing) |
| Layouts | `layouts/` |
| API routes | `server/api/` |
| Data fetching | `useFetch`, `useAsyncData`, `$fetch` |
| State | `useState`, Pinia |
| Middleware | `middleware/` |

## Angular

| Aspect | Where to Look |
|--------|--------------|
| Routes | `app-routing.module.ts` or `Routes` array |
| Components | `@Component` decorator, `*.component.ts` |
| State | NgRx (`store/`), services with `BehaviorSubject` |
| API | `HttpClient` in services |
| Forms | Reactive Forms (`FormGroup`), Template-driven forms |
| i18n | `@angular/localize`, `ngx-translate` |
| Guards | `CanActivate`, `CanDeactivate` |

## Svelte / SvelteKit

| Aspect | Where to Look |
|--------|--------------|
| Routes | `src/routes/` (file-system routing with `+page.svelte`) |
| Layouts | `+layout.svelte` |
| Data loading | `+page.ts` / `+page.server.ts` (`load` function) |
| API routes | `+server.ts` |
| State | Svelte stores (`writable`, `readable`, `derived`) |

## NestJS

| Aspect | Where to Look |
|--------|--------------|
| Routes | `@Controller('prefix')` + `@Get()/@Post()/@Put()/@Delete()` decorators |
| Modules | `*.module.ts` — `@Module({ controllers, providers, imports })` |
| Services | `*.service.ts` — injected via constructor, contains business logic |
| DTOs | `*.dto.ts` — `class-validator` decorators define validation rules |
| Entities | `*.entity.ts` — TypeORM `@Entity()` / Prisma schemas |
| Auth | `@UseGuards(AuthGuard)`, `@Roles('admin')`, Passport strategies |
| Middleware | `*.middleware.ts`, registered in module `configure()` |
| Pipes | `ValidationPipe`, `ParseIntPipe` — input transformation |
| Config | `ConfigModule`, `.env` files, `config/` directory |

## Express / Fastify

| Aspect | Where to Look |
|--------|--------------|
| Routes | `router.get('/path', handler)`, `app.post('/path', ...)` |
| Middleware | `app.use(...)`, `router.use(...)` |
| Controllers | Route handler files in `routes/`, `controllers/` |
| Models | Mongoose schemas (`*.model.ts`), Sequelize models, Prisma |
| Auth | `passport`, `jsonwebtoken`, middleware auth checks |
| Validation | `express-validator`, `joi`, `zod`, custom middleware |

## Django

| Aspect | Where to Look |
|--------|--------------|
| Routes | `urls.py` — `urlpatterns = [path('...', view)]` |
| Views | `views.py` — function-based or class-based views (`APIView`, `ViewSet`) |
| Models | `models.py` — `class MyModel(models.Model)` with field definitions |
| Forms | `forms.py` — `ModelForm`, `Form` with validation |
| Serializers | `serializers.py` (DRF) — `ModelSerializer`, field-level validation |
| Admin | `admin.py` — `@admin.register`, `list_display`, `search_fields`, `list_filter` |
| Templates | `templates/` — Jinja2/Django template HTML files |
| Middleware | `MIDDLEWARE` in `settings.py` |
| Auth | `django.contrib.auth`, `rest_framework.permissions`, `@login_required` |
| Signals | `signals.py` — `post_save`, `pre_delete` hooks (hidden business logic) |
| Management commands | `management/commands/` — CLI operations |
| Celery tasks | `tasks.py` — async/background operations |

## Django REST Framework (DRF)

| Aspect | Where to Look |
|--------|--------------|
| Endpoints | `router.register('prefix', ViewSet)` in `urls.py` |
| ViewSets | `viewsets.py` — `ModelViewSet` (full CRUD), `ReadOnlyModelViewSet` |
| Serializers | `serializers.py` — field types, validators, nested relations |
| Permissions | `permission_classes = [IsAuthenticated, IsAdminUser]` |
| Filtering | `django-filter`, `search_fields`, `ordering_fields` |
| Pagination | `DEFAULT_PAGINATION_CLASS` in settings, per-view override |
| Throttling | `DEFAULT_THROTTLE_CLASSES`, per-view `throttle_classes` |

## FastAPI

| Aspect | Where to Look |
|--------|--------------|
| Routes | `@app.get('/path')`, `@router.post('/path')` decorators |
| Models | Pydantic `BaseModel` classes — request/response schemas |
| Dependencies | `Depends(...)` — auth, DB sessions, shared logic |
| DB | SQLAlchemy models, Tortoise ORM, or raw SQL |
| Auth | `OAuth2PasswordBearer`, JWT middleware, `Depends(get_current_user)` |
| Background | `BackgroundTasks`, Celery integration |

## Common Patterns Across Frameworks

### Mock Detection
```
# Likely mock
setTimeout(() => resolve(data), 500)
Promise.resolve(mockData)
import { data } from './fixtures'
faker.name.firstName()

# Likely real
axios.get('/api/users')
fetch('/api/data')
httpClient.post(url, body)
useSWR('/api/resource')
```

### Permission Patterns
```
# React
{hasPermission('admin') && <Button>Delete</Button>}
<ProtectedRoute roles={['admin', 'manager']}>

# Vue
v-if="user.role === 'admin'"
v-permission="'user:delete'"

# Angular
*ngIf="authService.hasRole('admin')"
canActivate: [AuthGuard]
```

### Form Validation
```
# React Hook Form
{ required: 'Name is required', maxLength: { value: 50, message: 'Too long' } }

# VeeValidate (Vue)
rules="required|email|max:100"

# Angular Reactive Forms
Validators.required, Validators.minLength(3), Validators.pattern(...)

# NestJS (class-validator)
@IsString() @IsNotEmpty() @MaxLength(50) name: string;
@IsEmail() email: string;
@IsEnum(UserRole) role: UserRole;

# Django Forms
name = forms.CharField(max_length=50, required=True)
email = forms.EmailField()

# DRF Serializers
name = serializers.CharField(max_length=50)
email = serializers.EmailField(required=True)

# FastAPI (Pydantic)
name: str = Field(max_length=50)
email: EmailStr
```

### Database Model Patterns
```
# Django
class Order(models.Model):
    status = models.CharField(max_length=20, choices=STATUS_CHOICES)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    total = models.DecimalField(max_digits=10, decimal_places=2)

# TypeORM (NestJS)
@Entity()
export class Order {
    @Column({ type: 'enum', enum: OrderStatus })
    status: OrderStatus;
    @ManyToOne(() => User)
    user: User;
}

# Prisma
model Order {
    status  OrderStatus
    user    User @relation(fields: [userId], references: [id])
    total   Decimal
}
```
