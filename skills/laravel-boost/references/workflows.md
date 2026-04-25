# Development Workflows

Expanded step-by-step workflows with concrete examples, tool call sequences, and decision points.

---

## Table of Contents

1. [Feature Development Workflow](#feature-development-workflow)
2. [Debugging Workflow](#debugging-workflow)
3. [Database Work Workflow](#database-work-workflow)
4. [Testing Workflow](#testing-workflow)

---

## Feature Development Workflow

Use when the user wants to build something new: an endpoint, page, component, or feature.

### Step 1: Gather Context

Call these Boost MCP tools:

1. **`application-info`** → get installed packages, models, PHP/Laravel versions
2. **`database-schema`** → understand existing tables and relationships
3. **`list-artisan-commands`** → know available generators

From these results, answer:
- What models already exist that relate to this feature?
- What tables exist that this feature will read from or write to?
- What generators are available for scaffolding?

### Step 2: Research

Call **`search-docs`** for any Laravel APIs relevant to the feature. Examples:
- Building a REST API → search "API resources", "apiResource routes"
- Adding authentication → search "authentication guards", "Sanctum"
- File uploads → search "file storage", "file validation"
- Notifications → search "notification channels", "mail notifications"

### Step 3: Plan the Implementation

Based on gathered context, plan these layers (skip any that don't apply):

```
1. Database     → migration(s) + model(s) + factory/seeder
2. Logic        → service class or model methods
3. Validation   → form request class(es)
4. Controller   → controller + routes
5. Views/Pages  → Blade, Livewire component, or Inertia page
6. Tests        → feature + unit tests
```

### Step 4: Scaffold with Artisan

Use artisan generators — don't create files manually:

```bash
# Model with migration, factory, seeder, and controller
php artisan make:model Post -mfsc

# Form request
php artisan make:request StorePostRequest

# API resource
php artisan make:resource PostResource

# Pest test
php artisan make:test PostTest --pest
```

### Step 5: Implement

Follow this order to avoid dependency issues:

**Migration first:**
```php
Schema::create('posts', function (Blueprint $table) {
    $table->id();
    $table->foreignId('user_id')->constrained()->cascadeOnDelete();
    $table->string('title');
    $table->text('body');
    $table->string('status')->default('draft'); // use enum casting in model
    $table->timestamps();
});
```

**Model with relationships and casts:**
```php
class Post extends Model
{
    protected $fillable = ['user_id', 'title', 'body', 'status'];

    protected $casts = [
        'status' => PostStatus::class, // backed enum
    ];

    public function user(): BelongsTo
    {
        return $this->belongsTo(User::class);
    }
}
```

**Form request:**
```php
class StorePostRequest extends FormRequest
{
    public function authorize(): bool
    {
        return true;
    }

    public function rules(): array
    {
        return [
            'title' => ['required', 'string', 'max:255'],
            'body' => ['required', 'string'],
            'status' => ['sometimes', new Enum(PostStatus::class)],
        ];
    }
}
```

**Controller (invokable for single-action, resource for CRUD):**
```php
// Resource controller for full CRUD
class PostController extends Controller
{
    public function store(StorePostRequest $request): PostResource
    {
        $post = $request->user()->posts()->create($request->validated());

        return new PostResource($post);
    }
}
```

**Routes:**
```php
// API routes
Route::apiResource('posts', PostController::class);

// Web routes
Route::resource('posts', PostController::class);
```

### Step 6: Adapt to Detected Stack

**If Livewire detected:**
```php
// Use Livewire components instead of traditional controllers for interactive UI
php artisan make:livewire CreatePost

// Or with Volt for single-file components
php artisan make:volt create-post
```

**If Inertia (React) detected:**
```php
// Controller returns Inertia response
public function create(): \Inertia\Response
{
    return Inertia::render('Posts/Create', [
        'categories' => Category::all(),
    ]);
}
```

**If Inertia (Vue) detected:**
```php
// Same controller pattern, different frontend component
return Inertia::render('Posts/Create', [
    'categories' => Category::all(),
]);
```

### Step 7: Write Tests

See [Testing Workflow](#testing-workflow) for details.

---

## Debugging Workflow

Use when something is broken, erroring, or behaving unexpectedly.

### Step 1: Read the Error

Call tools in this order — stop as soon as you have enough information:

1. **`last-error`** → get the exception class, message, and stack trace
2. **`read-log-entries`** (20-50 entries) → get context around the error
3. **`browser-logs`** → check for frontend errors (if UI-related)

### Step 2: Classify the Error

| Exception Type | Next Step |
|---|---|
| `QueryException` | → Call `database-schema`, check column/table names |
| `ModelNotFoundException` | → Call `database-query` to verify the record exists |
| `ValidationException` | → Review form request rules, check request payload |
| `AuthenticationException` | → Check middleware, guards, token validity |
| `MethodNotAllowedHttpException` | → Check route definitions, HTTP methods |
| `ViewException` | → Check Blade/Livewire template syntax |
| `ReflectionException` | → Check class names, namespaces, service container bindings |
| JavaScript error (from browser-logs) | → Check Livewire/Inertia/Alpine integration |

### Step 3: Gather Diagnostic Data

Based on the error class:

**Database errors:**
```
database-schema → verify table/column exists
database-query → SELECT to check data state
search-docs → confirm correct Eloquent syntax
```

**Route/controller errors:**
```
search-docs → verify route definition syntax
application-info → check middleware packages
```

**Package errors:**
```
application-info → verify package version
search-docs → look up correct API for installed version
```

### Step 4: Fix and Verify

1. Make the fix
2. Call `last-error` again to verify no new errors
3. If the fix involved a migration, call `database-schema` to verify the schema change
4. If frontend-related, check `browser-logs` for resolved state

### Common Debugging Patterns

**"Column not found" errors:**
```
last-error → see the bad column name
database-schema → find the correct column name or confirm it's missing
→ Fix: correct the column name in code, or create a migration to add it
```

**"Class not found" errors:**
```
last-error → see the missing class
→ Check: was artisan make:* used? Is the namespace correct? Was composer dump-autoload needed?
```

**"Route not defined" errors:**
```
last-error → see the route name attempted
search-docs → "named routes" to verify syntax
→ Fix: add ->name() to route, or correct the route name in code
```

---

## Database Work Workflow

Use when creating or modifying schema, migrations, models, or relationships.

### Step 1: Understand Current State

1. **`database-connections`** → identify default connection and engine
2. **`database-schema`** → get full current schema

Review the schema carefully:
- What tables exist?
- What are the existing relationships (foreign keys)?
- What indexes are in place?
- Are there columns that will conflict with the planned change?

### Step 2: Plan the Migration

Call **`search-docs`** for any migration methods you're unsure about:
- Column modifiers: `->nullable()`, `->default()`, `->after()`, `->change()`
- Index types: `->index()`, `->unique()`, `->fullText()`
- Foreign keys: `->constrained()`, `->cascadeOnDelete()`, `->nullOnDelete()`

### Step 3: Create Migration

```bash
# New table
php artisan make:migration create_posts_table

# Add column to existing table
php artisan make:migration add_status_to_posts_table

# Modify column
php artisan make:migration change_status_column_in_posts_table
```

**Migration conventions:**
- Table names: plural snake_case (`blog_posts`, `user_profiles`)
- Column names: singular snake_case (`user_id`, `created_at`)
- Foreign keys: `{singular_table}_id` (`user_id`, `post_id`)
- Pivot tables: alphabetical singular (`post_tag`, not `tag_post`)
- Always include `$table->timestamps()` on new tables
- Use `->constrained()` for foreign keys — it infers table and column

### Step 4: Update Models

After creating the migration, update the corresponding Eloquent models:

**Relationships:**
```php
// One-to-Many
public function posts(): HasMany
{
    return $this->hasMany(Post::class);
}

// Belongs-To
public function user(): BelongsTo
{
    return $this->belongsTo(User::class);
}

// Many-to-Many
public function tags(): BelongsToMany
{
    return $this->belongsToMany(Tag::class);
}

// Many-to-Many with pivot data
public function roles(): BelongsToMany
{
    return $this->belongsToMany(Role::class)->withPivot('assigned_at')->withTimestamps();
}
```

**Always define both sides of the relationship.**

**Casts:**
```php
protected $casts = [
    'published_at' => 'datetime',
    'metadata' => 'array',
    'is_active' => 'boolean',
    'status' => PostStatus::class,  // backed enum
    'price' => 'decimal:2',
];
```

### Step 5: Run and Verify

```bash
php artisan migrate
```

After migrating, call **`database-schema`** again to verify:
- New table/columns exist
- Foreign keys are correctly defined
- Indexes are in place

If needed, call **`database-query`** to verify seed data:
```sql
SELECT COUNT(*) FROM posts;
SELECT * FROM posts LIMIT 5;
```

---

## Testing Workflow

Use when writing new tests or fixing failing tests.

### Step 1: Detect Framework

Call **`application-info`** and check for `pestphp/pest`:
- **Pest found** → use Pest syntax (`it()`, `expect()`, `describe()`)
- **No Pest** → use PHPUnit syntax (`test methods`, `$this->assert*()`)

### Step 2: Understand What to Test

Call **`database-schema`** to understand data structures for:
- Factory definitions
- Assertion values
- Relationship testing

Call **`search-docs`** for testing helpers:
- "Pest expectations" or "PHPUnit assertions"
- "HTTP testing" for endpoint tests
- "database testing" for model/migration tests
- "mocking" for external service tests

### Step 3: Write Tests

**Feature test (Pest) — testing an endpoint:**
```php
use App\Models\User;
use App\Models\Post;

describe('POST /api/posts', function () {
    it('creates a post for authenticated users', function () {
        $user = User::factory()->create();

        $response = $this->actingAs($user)->postJson('/api/posts', [
            'title' => 'My Post',
            'body' => 'Post content here.',
        ]);

        $response->assertCreated()
            ->assertJsonPath('data.title', 'My Post');

        $this->assertDatabaseHas('posts', [
            'user_id' => $user->id,
            'title' => 'My Post',
        ]);
    });

    it('rejects unauthenticated requests', function () {
        $this->postJson('/api/posts', [
            'title' => 'My Post',
            'body' => 'Content.',
        ])->assertUnauthorized();
    });

    it('validates required fields', function () {
        $user = User::factory()->create();

        $this->actingAs($user)
            ->postJson('/api/posts', [])
            ->assertUnprocessable()
            ->assertJsonValidationErrors(['title', 'body']);
    });
});
```

**Feature test (PHPUnit):**
```php
class PostControllerTest extends TestCase
{
    use RefreshDatabase;

    public function test_authenticated_user_can_create_post(): void
    {
        $user = User::factory()->create();

        $response = $this->actingAs($user)->postJson('/api/posts', [
            'title' => 'My Post',
            'body' => 'Post content here.',
        ]);

        $response->assertCreated();
        $this->assertDatabaseHas('posts', [
            'user_id' => $user->id,
            'title' => 'My Post',
        ]);
    }
}
```

**Unit test (Pest):**
```php
use App\Models\Post;
use App\Enums\PostStatus;

it('has draft status by default', function () {
    $post = Post::factory()->create();

    expect($post->status)->toBe(PostStatus::Draft);
});

it('belongs to a user', function () {
    $post = Post::factory()->create();

    expect($post->user)->toBeInstanceOf(User::class);
});
```

**Pest architecture tests:**
```php
arch('models extend base model')
    ->expect('App\Models')
    ->toExtend('Illuminate\Database\Eloquent\Model');

arch('controllers have no public properties')
    ->expect('App\Http\Controllers')
    ->not->toHavePublicProperties();
```

### Step 4: Run and Iterate

```bash
# Run all tests
php artisan test

# Run specific test file
php artisan test --filter=PostControllerTest

# Run with coverage (if configured)
php artisan test --coverage
```

If tests fail:
1. Read the failure message carefully
2. Call `last-error` if the failure involves an application error
3. Call `database-schema` if the failure involves database state
4. Fix and re-run

### Testing Checklist

For any new feature, ensure you test:
- [ ] Happy path (expected usage works)
- [ ] Validation (bad input is rejected with proper errors)
- [ ] Authorization (unauthenticated/unauthorized users are blocked)
- [ ] Edge cases (empty strings, nulls, max lengths, duplicates)
- [ ] Database state (records created/updated/deleted correctly)
- [ ] Response structure (correct status code, JSON shape, redirects)
