# Anti-Patterns Gallery

Before/after examples for each of the 4 Karpathy principles. Use these to calibrate your reviews.

## Principle #1 — Think Before Coding

### Silent assumption: scope

**Request:** "Add a feature to export user data"

**Bad:** Immediately writes a function that exports ALL users as JSON to disk, picks column names, and adds CSV support.

**Good:**
```
Before implementing, I need to clarify:
1. Which users — all? current tenant? filtered?
2. Which fields — some may be sensitive (PII)
3. Format — JSON, CSV, or API endpoint?
4. Destination — file download, S3, or API response?

Simplest: add an API endpoint returning paginated JSON for authenticated admins.
Want me to go with that, or do you need something different?
```

### Silent assumption: interpretation

**Request:** "Make the search faster"

**Bad:** Adds Redis caching, async queries, AND database indexes in one commit.

**Good:**
```
"Faster" could mean:
- Lower latency per query (add indexes, ~2h)
- Higher throughput under load (add async, ~4h)
- Faster perceived speed (progressive loading, ~3h)

Current: ~500ms p50. Which dimension matters most?
```

## Principle #2 — Simplicity First

### Over-abstraction

**Request:** "Add a function to calculate discount"

**Bad (150 lines):**
```python
class DiscountStrategy(ABC):
    @abstractmethod
    def calculate(self, amount: float) -> float: ...

class PercentageDiscount(DiscountStrategy): ...
class FixedDiscount(DiscountStrategy): ...

@dataclass
class DiscountConfig:
    strategy: DiscountStrategy
    min_purchase: float = 0.0
    max_discount: float = float('inf')

class DiscountCalculator:
    def __init__(self, config: DiscountConfig): ...
    def apply_discount(self, amount: float) -> float: ...
```

**Good (3 lines):**
```python
def calculate_discount(amount: float, percent: float) -> float:
    return amount * (percent / 100)
```

Add the Strategy pattern when you actually have multiple discount types. Not before.

### Speculative features

**Request:** "Save user preferences to database"

**Bad:** Adds caching, validation, merge mode, notification system, and a `PreferenceManager` class.

**Good:**
```python
def save_preferences(db, user_id: int, preferences: dict):
    db.execute("UPDATE users SET preferences = ? WHERE id = ?",
               (json.dumps(preferences), user_id))
```

## Principle #3 — Surgical Changes

### Drive-by refactoring

**Request:** "Fix the bug where empty emails crash the validator"

**Bad diff (touches 15 lines, only 2 fix the bug):**
```diff
  def validate_user(user_data):
-     # Check email format
+     """Validate user data."""           # ← docstring added (not asked)
+     email = user_data.get('email', '').strip()
      ...
+     if len(username) < 3:               # ← username validation (not asked)
+         raise ValueError("Username too short")
```

**Good diff (touches 3 lines, all fix the bug):**
```diff
  def validate_user(user_data):
-     if not user_data.get('email'):
+     email = user_data.get('email', '')
+     if not email or not email.strip():
          raise ValueError("Email required")
-     if '@' not in user_data['email']:
+     if '@' not in email:
```

### Style drift

**Request:** "Add logging to the upload function"

**Bad:** Changes quote style, adds type hints, adds docstring, reformats boolean logic.

**Good:** Adds `import logging`, `logger = logging.getLogger(__name__)`, and 3 `logger.info/error` calls. Matches existing single-quote style. Doesn't touch anything else.

## Principle #4 — Goal-Driven Execution

### Vague vs concrete

**Request:** "Fix the authentication system"

**Bad plan:**
```
1. Review the code
2. Identify issues
3. Make improvements
4. Test the changes
```

**Good plan:**
```
Specific issue: users stay logged in after password change.

1. Write test: change password → old session should be invalid
   verify: test fails (reproduces bug)
2. Invalidate all sessions on password change
   verify: test passes
3. Check edge: multiple active sessions, concurrent changes
   verify: additional tests pass
4. Run full auth test suite
   verify: all green, no regressions
```

### Missing final verification

**Bad:** "I've added rate limiting. It should work."

**Good:** "Rate limiting added. Verified: sent 11 requests → first 10 got 200, 11th got 429. Existing tests still pass."

## Quick-reference decision table

| Situation | Principle | Action |
|---|---|---|
| Ambiguous requirement | #1 Think | List interpretations, ask |
| "I need a class for this" | #2 Simplicity | Can it be a function? |
| "While I'm here, I'll fix this too" | #3 Surgical | Mention it, don't fix it |
| "This should work" | #4 Goals | What test proves it? |
| User explicitly asked for abstraction | #2 relaxed | Build the abstraction |
| User said "refactor this file" | #3 relaxed | Broader changes are OK |
| One-liner fix, obvious correctness | all relaxed | Use judgment |
