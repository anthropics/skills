# Type Hints Guide for Python

A comprehensive guide to Python type hinting based on Guido van Rossum's guidance and modern best practices.

## Guido's Type Hints Philosophy

**Key insight from Guido**: Type hints are essential for mission-critical applications once projects reach approximately **10,000 lines of code**. Below that threshold, type hints offer diminishing returns. Above it, code quality becomes difficult to maintain without them.

**When to use type hints**:
- Projects >10,000 lines
- Team collaborations
- Library/API development
- Long-term maintenance projects
- Code with complex data flows

**When type hints are optional**:
- Scripts <1,000 lines
- Prototype code
- Internal utilities
- One-off analysis scripts

## Basic Type Hints

### Simple Types

```python
# Built-in types
name: str = "Alice"
age: int = 30
height: float = 5.8
is_active: bool = True

# Function signatures
def greet(name: str) -> str:
    """Greet someone by name."""
    return f"Hello, {name}!"

def add(a: int, b: int) -> int:
    """Add two integers."""
    return a + b

def process_data(data: str) -> None:
    """Process data without returning anything."""
    print(data)
```

### Collections

```python
from typing import List, Dict, Set, Tuple

# Lists
names: List[str] = ["Alice", "Bob", "Charlie"]
numbers: List[int] = [1, 2, 3, 4, 5]

# Dictionaries
user_ages: Dict[str, int] = {"Alice": 30, "Bob": 25}
config: Dict[str, Any] = {"timeout": 30, "retries": 3}

# Sets
unique_ids: Set[int] = {1, 2, 3, 4, 5}

# Tuples (fixed size)
coordinates: Tuple[float, float] = (10.5, 20.3)
rgb: Tuple[int, int, int] = (255, 128, 0)

# Tuples (variable size)
numbers: Tuple[int, ...] = (1, 2, 3, 4, 5)
```

### Modern Collection Types (Python 3.9+)

```python
# Python 3.9+ - can use built-in types directly
names: list[str] = ["Alice", "Bob"]
user_ages: dict[str, int] = {"Alice": 30}
unique_ids: set[int] = {1, 2, 3}
coordinates: tuple[float, float] = (10.5, 20.3)

# This is preferred in modern Python (3.9+)
def process_items(items: list[str]) -> dict[str, int]:
    """Process items and return counts."""
    return {item: len(item) for item in items}
```

## Optional and Union Types

### Optional Values

```python
from typing import Optional

# Optional means "value or None"
def find_user(user_id: int) -> Optional[str]:
    """Find user by ID, return name or None if not found."""
    users = {1: "Alice", 2: "Bob"}
    return users.get(user_id)

# Optional[str] is equivalent to Union[str, None]
name: Optional[str] = None
name = "Alice"  # Valid
name = None     # Valid
```

### Union Types

```python
from typing import Union

# Union allows multiple types
def process_input(data: Union[str, int, float]) -> str:
    """Process various input types."""
    return str(data)

# Python 3.10+ - use | operator (preferred)
def process_input(data: str | int | float) -> str:
    """Process various input types."""
    return str(data)

# Multiple possibilities
Result = Union[int, str, None]

def get_result() -> Result:
    """Return an int, str, or None."""
    # Implementation
    pass
```

## Advanced Type Hints

### Type Aliases

```python
from typing import List, Dict, Tuple

# Create readable aliases for complex types
UserId = int
UserName = str
UserData = Dict[str, Union[str, int]]

def get_user(user_id: UserId) -> UserName:
    """Get username by ID."""
    pass

# Complex nested types
Coordinates = Tuple[float, float]
Route = List[Coordinates]
RouteMap = Dict[str, Route]

def calculate_distance(route: Route) -> float:
    """Calculate total distance for a route."""
    pass
```

### Callable Types

```python
from typing import Callable

# Function that takes int, str and returns bool
Validator = Callable[[int, str], bool]

def validate_user(user_id: int, name: str) -> bool:
    """Example validator function."""
    return user_id > 0 and len(name) > 0

def apply_validation(validator: Validator, user_id: int, name: str) -> bool:
    """Apply a validator function."""
    return validator(user_id, name)

# Callback with no arguments
Callback = Callable[[], None]

def on_complete() -> None:
    print("Done!")

def run_task(callback: Callback) -> None:
    """Run task and call callback when done."""
    # Do work...
    callback()
```

### Generic Types

```python
from typing import TypeVar, Generic, List

# Define a type variable
T = TypeVar('T')

def first_element(items: List[T]) -> T:
    """Get first element of a list."""
    return items[0]

# Generic class
class Stack(Generic[T]):
    """A generic stack data structure."""

    def __init__(self) -> None:
        self._items: List[T] = []

    def push(self, item: T) -> None:
        """Push item onto stack."""
        self._items.append(item)

    def pop(self) -> T:
        """Pop item from stack."""
        return self._items.pop()

# Usage
int_stack: Stack[int] = Stack()
int_stack.push(1)
int_stack.push(2)

str_stack: Stack[str] = Stack()
str_stack.push("hello")
```

### Protocol Types (Structural Subtyping)

```python
from typing import Protocol

# Define behavior without inheritance
class Drawable(Protocol):
    """Anything that can be drawn."""

    def draw(self) -> None:
        """Draw the object."""
        ...

    def get_position(self) -> tuple[float, float]:
        """Get object position."""
        ...

# Any class with these methods is considered Drawable
class Circle:
    def draw(self) -> None:
        print("Drawing circle")

    def get_position(self) -> tuple[float, float]:
        return (10.0, 20.0)

class Square:
    def draw(self) -> None:
        print("Drawing square")

    def get_position(self) -> tuple[float, float]:
        return (5.0, 15.0)

# Works with duck typing
def render(obj: Drawable) -> None:
    """Render any drawable object."""
    position = obj.get_position()
    print(f"Rendering at {position}")
    obj.draw()

render(Circle())  # Valid
render(Square())  # Valid
```

### Literal Types

```python
from typing import Literal

# Restrict to specific values
Mode = Literal["read", "write", "append"]

def open_file(path: str, mode: Mode) -> None:
    """Open file in specific mode."""
    pass

open_file("data.txt", "read")   # Valid
open_file("data.txt", "write")  # Valid
open_file("data.txt", "delete") # Type checker error!

# Multiple literals
Status = Literal["pending", "processing", "completed", "failed"]

def update_status(status: Status) -> None:
    """Update job status."""
    pass
```

### TypedDict

```python
from typing import TypedDict

# Define dictionary structure
class UserDict(TypedDict):
    """Typed dictionary for user data."""
    id: int
    name: str
    email: str
    age: int

def create_user(user: UserDict) -> None:
    """Create user from typed dict."""
    print(f"Creating user: {user['name']}")

# Usage
user: UserDict = {
    "id": 1,
    "name": "Alice",
    "email": "alice@example.com",
    "age": 30
}

create_user(user)

# Optional fields
class OptionalUserDict(TypedDict, total=False):
    """User dict with optional fields."""
    id: int
    name: str
    email: str  # Optional
    age: int    # Optional
```

### Any and Cast

```python
from typing import Any, cast

# Any - escape hatch for dynamic types
def process_dynamic_data(data: Any) -> Any:
    """Process data of unknown type."""
    # Can do anything with 'data'
    return data

# Cast - tell type checker to treat value as specific type
def get_config() -> Any:
    """Get config from external source."""
    return {"timeout": 30}

config = cast(Dict[str, int], get_config())
# Type checker now treats config as Dict[str, int]

# Use Any sparingly - it defeats the purpose of type checking!
```

## Class Type Hints

### Basic Class Annotations

```python
from typing import ClassVar, List
from dataclasses import dataclass

class User:
    """User class with type hints."""

    # Class variable
    total_users: ClassVar[int] = 0

    def __init__(self, name: str, age: int):
        self.name: str = name
        self.age: int = age
        User.total_users += 1

    def greet(self) -> str:
        """Return greeting message."""
        return f"Hello, I'm {self.name}"

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> 'User':
        """Create user from dictionary."""
        return cls(data['name'], data['age'])

    @staticmethod
    def is_valid_age(age: int) -> bool:
        """Check if age is valid."""
        return 0 < age < 150
```

### Dataclasses with Type Hints

```python
from dataclasses import dataclass, field
from typing import List, Optional
from datetime import datetime

@dataclass
class User:
    """User data class."""
    id: int
    name: str
    email: str
    created_at: datetime = field(default_factory=datetime.now)
    tags: List[str] = field(default_factory=list)
    is_active: bool = True

@dataclass
class Team:
    """Team data class."""
    name: str
    members: List[User] = field(default_factory=list)
    leader: Optional[User] = None

    def add_member(self, user: User) -> None:
        """Add user to team."""
        self.members.append(user)
```

## Async Type Hints

```python
from typing import Coroutine, AsyncIterator
import asyncio

# Async function
async def fetch_data(url: str) -> dict[str, Any]:
    """Fetch data asynchronously."""
    # Implementation
    await asyncio.sleep(1)
    return {"status": "ok"}

# Async generator
async def generate_numbers() -> AsyncIterator[int]:
    """Generate numbers asynchronously."""
    for i in range(10):
        await asyncio.sleep(0.1)
        yield i

# Async context manager
from typing import AsyncContextManager

async def database_session() -> AsyncContextManager[Database]:
    """Provide async database session."""
    # Implementation
    pass
```

## MyPy Configuration

### pyproject.toml Configuration

```toml
[tool.mypy]
# Specify Python version
python_version = "3.11"

# Strictness
strict = true
warn_return_any = true
warn_unused_configs = true
disallow_untyped_defs = true
disallow_any_generics = true
disallow_subclassing_any = true
disallow_untyped_calls = true
disallow_untyped_decorators = true
disallow_incomplete_defs = true
check_untyped_defs = true
no_implicit_optional = true

# Warnings
warn_redundant_casts = true
warn_unused_ignores = true
warn_no_return = true
warn_unreachable = true

# Error messages
show_error_context = true
show_column_numbers = true
show_error_codes = true
pretty = true

# Miscellaneous
strict_equality = true
strict_concatenate = true

# Per-module options
[[tool.mypy.overrides]]
module = "tests.*"
disallow_untyped_defs = false

[[tool.mypy.overrides]]
module = "third_party_lib.*"
ignore_missing_imports = true
```

### Progressive Typing

When adding types to existing codebase:

**Step 1: Start with strict mode disabled**
```toml
[tool.mypy]
python_version = "3.11"
warn_return_any = true
warn_unused_configs = true
# Don't require type hints everywhere yet
```

**Step 2: Add type hints module by module**
```python
# mypy: disallow-untyped-defs
"""This module has complete type coverage."""

def process_data(data: list[int]) -> int:
    return sum(data)
```

**Step 3: Gradually increase strictness**
```toml
[tool.mypy]
python_version = "3.11"
strict = false  # Not yet!

# Enable specific checks
disallow_untyped_defs = true
warn_return_any = true
warn_unused_configs = true
no_implicit_optional = true
```

**Step 4: Enable strict mode when ready**
```toml
[tool.mypy]
python_version = "3.11"
strict = true
```

## Common Patterns

### Builder Pattern with Types

```python
from typing import TypeVar, Generic, Optional
from dataclasses import dataclass

T = TypeVar('T')

@dataclass
class QueryBuilder(Generic[T]):
    """Type-safe query builder."""

    _table: str
    _filters: list[str] = field(default_factory=list)
    _limit: Optional[int] = None

    def filter(self, condition: str) -> 'QueryBuilder[T]':
        """Add filter condition."""
        self._filters.append(condition)
        return self

    def limit(self, n: int) -> 'QueryBuilder[T]':
        """Add limit."""
        self._limit = n
        return self

    def execute(self) -> list[T]:
        """Execute query and return results."""
        # Build and execute query
        pass

# Usage
users: list[User] = (
    QueryBuilder[User]("users")
    .filter("age > 18")
    .filter("is_active = true")
    .limit(10)
    .execute()
)
```

### Factory Pattern with Types

```python
from typing import Type, TypeVar, Protocol

class Serializable(Protocol):
    """Protocol for serializable objects."""
    def to_dict(self) -> dict[str, Any]: ...
    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> 'Serializable': ...

T = TypeVar('T', bound=Serializable)

class Factory(Generic[T]):
    """Generic factory for creating serializable objects."""

    def __init__(self, cls: Type[T]):
        self.cls = cls

    def create(self, **kwargs: Any) -> T:
        """Create instance from keyword arguments."""
        return self.cls.from_dict(kwargs)

    def create_batch(self, data: list[dict[str, Any]]) -> list[T]:
        """Create multiple instances."""
        return [self.cls.from_dict(item) for item in data]

# Usage
user_factory = Factory(User)
user = user_factory.create(id=1, name="Alice", email="alice@example.com")
```

### Decorator with Type Hints

```python
from typing import TypeVar, Callable, ParamSpec

P = ParamSpec('P')
R = TypeVar('R')

def log_calls(func: Callable[P, R]) -> Callable[P, R]:
    """Decorator that logs function calls."""
    def wrapper(*args: P.args, **kwargs: P.kwargs) -> R:
        print(f"Calling {func.__name__}")
        result = func(*args, **kwargs)
        print(f"Finished {func.__name__}")
        return result
    return wrapper

@log_calls
def add(a: int, b: int) -> int:
    """Add two numbers."""
    return a + b

# Type checker knows add returns int
result: int = add(1, 2)
```

## Type Checking Workflow

### Running MyPy

```bash
# Check entire project
mypy src/

# Check specific file
mypy src/myproject/core.py

# Show error codes
mypy --show-error-codes src/

# Generate HTML report
mypy --html-report mypy-report src/
```

### Inline Type Comments

```python
# For Python 3.5+ variable annotations
from typing import List

# Variable annotation
numbers: List[int] = []

# Type comment for older syntax
numbers = []  # type: List[int]

# Function signature (older syntax)
def add(a, b):
    # type: (int, int) -> int
    return a + b
```

### Type Ignores

```python
# Ignore type checking on specific line
result = some_untyped_library.function()  # type: ignore

# Ignore with reason
result = legacy_code.process()  # type: ignore[attr-defined]

# Ignore entire file
# mypy: ignore-errors
```

## Best Practices

### 1. Start Gradually
Don't try to add type hints to everything at once. Start with:
- Public APIs
- Critical business logic
- Complex data transformations

### 2. Use Type Aliases for Readability
```python
# Bad - hard to read
def process_users(
    data: Dict[str, List[Tuple[int, str, float]]]
) -> List[Dict[str, Union[int, str]]]:
    pass

# Good - clear intent
UserId = int
UserName = str
UserScore = float
UserRecord = Tuple[UserId, UserName, UserScore]
UserData = Dict[str, List[UserRecord]]
ProcessedUser = Dict[str, Union[int, str]]

def process_users(data: UserData) -> List[ProcessedUser]:
    pass
```

### 3. Use Protocols for Duck Typing
```python
# More Pythonic than abstract base classes
from typing import Protocol

class SupportsClose(Protocol):
    def close(self) -> None: ...

def close_resource(resource: SupportsClose) -> None:
    resource.close()
```

### 4. Avoid Overusing Any
```python
# Bad - defeats purpose of type hints
def process(data: Any) -> Any:
    pass

# Better - be specific
def process(data: Union[str, int, list[str]]) -> dict[str, Any]:
    pass
```

### 5. Document Complex Types
```python
# Complex return type - needs documentation
def analyze_data(
    data: list[dict[str, Any]]
) -> dict[str, Union[int, float, list[str]]]:
    """Analyze data and return statistics.

    Returns:
        Dictionary containing:
        - 'count': Number of records (int)
        - 'average': Average value (float)
        - 'categories': List of unique categories (list[str])
    """
    pass
```

## Summary

Type hints make Python code more maintainable, especially for large projects. Follow Guido's guidance:
- Use them for projects >10,000 lines
- Add them gradually
- Focus on public APIs first
- Use mypy in CI/CD
- Balance strictness with pragmatism

Remember: Type hints are optional at runtime but invaluable for development and maintenance.
