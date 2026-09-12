# Codebase Patterns for Agent-First Development

Agents work best with codebases that have clear boundaries, explicit interfaces, and minimal hidden coupling. This guide covers structural patterns that make repositories agent-friendly.

## Table of Contents

- [Module Boundaries](#module-boundaries)
- [Typed Interfaces](#typed-interfaces)
- [Reducing Hidden Coupling](#reducing-hidden-coupling)
- [Making Tools Agent-Accessible](#making-tools-agent-accessible)
- [CI/CD for Agent Workflows](#cicd-for-agent-workflows)

---

## Module Boundaries

### The Blast Radius Principle

A change in one module should not require understanding every other module. Agents work on focused tasks — if modifying a payment module requires reading the notification system, the auth layer, and the logging framework, the agent's context window fills up and quality drops.

### Define Public APIs Explicitly

Every major module should export a clear public API and keep internals private.

**Python:**
```python
# payments/__init__.py — this IS the public API
from .service import process_payment, refund_payment
from .models import Payment, PaymentStatus

# Everything else in payments/ is an implementation detail
```

**TypeScript:**
```typescript
// payments/index.ts — barrel export
export { processPayment, refundPayment } from './service';
export type { Payment, PaymentStatus } from './models';
```

**Go:**
```go
// Only exported (capitalized) identifiers are part of the public API
// Internal packages can enforce this further:
// internal/payments/ is not importable from outside the module
```

### Directory Structure Patterns

**Feature-based (recommended for most projects):**
```
src/
├── auth/          # Everything related to authentication
│   ├── routes.py
│   ├── service.py
│   ├── models.py
│   └── tests/
├── payments/      # Everything related to payments
│   ├── routes.py
│   ├── service.py
│   ├── models.py
│   └── tests/
└── shared/        # Truly shared utilities (logging, errors, config)
```

**Layer-based (acceptable for small projects):**
```
src/
├── routes/        # All HTTP handlers
├── services/      # All business logic
├── models/        # All data models
└── utils/         # Shared utilities
```

Feature-based is preferred because an agent working on payments only needs to read `src/payments/`, not scan across three top-level directories.

---

## Typed Interfaces

Types at module boundaries let agents understand contracts without reading implementations.

### Function Signatures

```python
# Bad: agent must read implementation to understand behavior
def process(data, options=None):
    ...

# Good: contract is clear from the signature
def process_payment(
    amount: Decimal,
    currency: str,
    customer_id: str,
    idempotency_key: str | None = None,
) -> PaymentResult:
    ...
```

### Data Transfer Objects

Use typed objects for data crossing module boundaries:

```python
@dataclass
class PaymentRequest:
    amount: Decimal
    currency: str
    customer_id: str
    idempotency_key: str | None = None

@dataclass
class PaymentResult:
    payment_id: str
    status: PaymentStatus
    created_at: datetime
```

### Schema Validation at Boundaries

Validate data at system entry points (API routes, CLI arguments, file parsing), not inside business logic:

```python
# Route handler validates input
@app.post("/payments")
def create_payment(request: PaymentRequest):  # Pydantic validates here
    return service.process_payment(request)    # Service trusts the input

# Service does NOT re-validate
def process_payment(request: PaymentRequest) -> PaymentResult:
    # Business logic only, no validation
    ...
```

---

## Reducing Hidden Coupling

### Environment Variable Access

**Problem**: Environment variables read anywhere make it impossible for an agent to know what configuration a module needs.

**Fix**: Read environment variables once at startup, pass configuration explicitly.

```python
# Bad: scattered env reads
class PaymentService:
    def process(self):
        api_key = os.environ["STRIPE_KEY"]    # Hidden dependency
        timeout = int(os.environ.get("TIMEOUT", "30"))
        ...

# Good: explicit configuration
@dataclass
class PaymentConfig:
    api_key: str
    timeout: int = 30

class PaymentService:
    def __init__(self, config: PaymentConfig):
        self.config = config

# Read env once at app startup
config = PaymentConfig(
    api_key=os.environ["STRIPE_KEY"],
    timeout=int(os.environ.get("TIMEOUT", "30")),
)
service = PaymentService(config)
```

### Global State

**Problem**: Mutable global state (singletons, module-level variables) creates invisible dependencies between modules.

**Fix**: Use dependency injection. Pass dependencies explicitly.

```python
# Bad: global singleton
db = Database.get_instance()

class UserService:
    def get_user(self, id):
        return db.query(User, id)  # Hidden dependency on global

# Good: injected dependency
class UserService:
    def __init__(self, db: Database):
        self.db = db

    def get_user(self, id: str) -> User:
        return self.db.query(User, id)
```

### Import Side Effects

**Problem**: Importing a module triggers side effects (database connections, file reads, network calls).

**Fix**: Move side effects to explicit initialization functions.

```python
# Bad: importing this module connects to the database
# db.py
engine = create_engine(os.environ["DATABASE_URL"])  # Runs on import!
Session = sessionmaker(bind=engine)

# Good: explicit initialization
# db.py
engine = None
Session = None

def init_db(database_url: str):
    global engine, Session
    engine = create_engine(database_url)
    Session = sessionmaker(bind=engine)
```

---

## Making Tools Agent-Accessible

### CLI Wrapper Checklist

When wrapping internal tools for agent access, ensure:

1. **`--help` works** — Every command and subcommand has a help message.
2. **Structured output** — Support `--format json` for machine-readable output.
3. **Non-zero exit codes** — Errors return non-zero exit codes with a message on stderr.
4. **Idempotent operations** — Running the same command twice produces the same result.
5. **No interactive prompts** — Support `--yes` or `--no-input` flags. Agents cannot answer prompts.
6. **Clear argument names** — `--customer-id` not `--cid`.

```bash
# Good CLI design
$ mytool deploy --service api --env staging --format json
{"status": "deployed", "version": "1.2.3", "url": "https://staging.example.com"}

$ mytool deploy --service api --env staging --dry-run
Would deploy api v1.2.3 to staging

$ mytool deploy --help
Deploy a service to the specified environment.

Usage: mytool deploy [OPTIONS]

Options:
  --service TEXT   Service name (required)
  --env TEXT       Target environment (required)
  --version TEXT   Version to deploy (default: latest)
  --dry-run        Show what would happen without executing
  --format TEXT    Output format: text, json (default: text)
  --yes            Skip confirmation prompts
```

### MCP Server Considerations

For tools that benefit from richer interaction (stateful sessions, streaming output, complex queries), consider creating an MCP server instead of a CLI. See the `mcp-builder` skill for implementation guidance.

Good MCP candidates:
- Database query tools (complex queries, result exploration)
- Monitoring dashboards (streaming metrics, alert management)
- Document management systems (search, retrieval, indexing)

---

## CI/CD for Agent Workflows

### Pre-commit Hooks

Configure pre-commit hooks that agents can run:

```yaml
# .pre-commit-config.yaml
repos:
  - repo: local
    hooks:
      - id: lint
        name: lint
        entry: make lint
        language: system
      - id: typecheck
        name: typecheck
        entry: make typecheck
        language: system
```

### CI Pipeline Optimization

Structure CI so agents get fast feedback:

1. **Fast checks first**: Linting, formatting, type checking (< 1 minute)
2. **Unit tests second**: Fast, isolated tests (< 3 minutes)
3. **Integration tests third**: Tests requiring services (< 10 minutes)
4. **Slow tests last**: E2E, performance, security scans

### Branch Protection for Agent PRs

Apply the same branch protection rules to agent-created PRs:
- Required reviews from human team members
- All CI checks must pass
- No force pushes
- Require up-to-date branches before merging
