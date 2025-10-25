---
name: python-architect
description: Expert guidance on Python project architecture, structure, and idiomatic code design inspired by Guido van Rossum's philosophy. Use this skill when designing Python projects, setting up new Python codebases, architecting modules, refactoring for better structure, or seeking guidance on Pythonic patterns and best practices. Ideal for projects of any size from small scripts to large-scale applications.
---

# Python Architect

## Overview

Channel the wisdom and experience of Guido van Rossum, Python's creator, to guide Python project architecture, design, and implementation. This skill embodies Guido's core philosophy: **code is read far more often than it is written**. Every architectural decision prioritizes human understanding, maintainability, and the elegance of simplicity.

This skill provides both high-level architectural guidance and hands-on coding assistance, grounded in the principles that have made Python one of the world's most beloved programming languages.

## The Foundation: Guido's Design Philosophy

### Core Principles

Guido van Rossum's design philosophy centers on a simple but profound insight: **programmer time is more valuable than computer time**. This human-centered approach influences every aspect of Python design.

**The Zen of Python** (access via `import this`) captures these principles:

1. **Beautiful is better than ugly** - Aesthetic code is maintainable code
2. **Explicit is better than implicit** - Clarity over cleverness
3. **Simple is better than complex** - Favor straightforward solutions
4. **Complex is better than complicated** - When complexity is necessary, keep it organized
5. **Readability counts** - Code communicates with humans first, machines second
6. **There should be one-- and preferably only one --obvious way to do it** - Reduce cognitive load
7. **If the implementation is hard to explain, it's a bad idea** - Simplicity as a design constraint

### Guido's Practical Wisdom

- **"Good enough" over perfect**: Early Python succeeded because it worked well enough for real needs, not by striving for theoretical perfection
- **Human-first design**: Write code primarily to communicate with other developers, secondarily to direct the computer
- **Extensibility over bloat**: Small core language + large standard library + easy extensions
- **Progressive disclosure**: Start simple, add complexity only when needed

## Project Architecture Guidance

### When Starting a New Python Project

Follow this decision tree to structure projects appropriately:

#### 1. Assess Project Scope

**For simple scripts (<500 lines, single purpose):**
```
my_script.py
README.md
requirements.txt (if dependencies needed)
```

Keep it simple. Don't over-engineer what doesn't need structure.

**For small projects (500-5,000 lines):**
```
project_name/
├── README.md
├── pyproject.toml or setup.py
├── requirements.txt
├── src/
│   └── project_name/
│       ├── __init__.py
│       ├── main.py
│       └── core.py
├── tests/
│   ├── __init__.py
│   └── test_core.py
└── docs/ (optional)
```

**For medium-to-large projects (>5,000 lines):**
```
project_name/
├── README.md
├── pyproject.toml
├── requirements.txt
├── requirements-dev.txt
├── .gitignore
├── src/
│   └── project_name/
│       ├── __init__.py
│       ├── __main__.py
│       ├── cli.py
│       ├── config.py
│       ├── core/
│       │   ├── __init__.py
│       │   ├── module1.py
│       │   └── module2.py
│       ├── utils/
│       │   ├── __init__.py
│       │   └── helpers.py
│       └── exceptions.py
├── tests/
│   ├── __init__.py
│   ├── conftest.py
│   ├── test_core/
│   └── test_integration/
├── docs/
│   ├── conf.py
│   └── index.rst
└── scripts/ (optional automation scripts)
```

#### 2. Type Hints Decision Point

**Guido's guidance**: Type hints are essential for mission-critical applications once projects reach approximately **10,000 lines of code**. Below that threshold, type hints offer diminishing returns. Above it, code quality becomes difficult to maintain without them.

**When to use type hints:**
- Projects >10,000 lines
- Team collaborations
- Library/API development
- Long-term maintenance projects

**Modern type hint setup:**
```python
# pyproject.toml
[tool.mypy]
python_version = "3.12"
warn_return_any = true
warn_unused_configs = true
disallow_untyped_defs = true

[tool.pylint.messages_control]
enable = ["all"]
disable = ["missing-docstring"]  # adjust as needed
```

#### 3. Choose Packaging Approach

**Modern Python (3.6+) - Use pyproject.toml:**
```toml
[build-system]
requires = ["setuptools>=61.0", "wheel"]
build-backend = "setuptools.build_meta"

[project]
name = "project-name"
version = "0.1.0"
description = "Brief description"
readme = "README.md"
requires-python = ">=3.9"
dependencies = [
    "requests>=2.28.0",
]

[project.optional-dependencies]
dev = [
    "pytest>=7.0",
    "mypy>=1.0",
    "pylint>=2.15",
]
```

This is the modern, preferred approach. It eliminates the need for separate setup.py files in most cases.

### Module Design Principles

#### Guido's Module Philosophy

Python was designed to be **highly extensible via modules** rather than building everything into the core. This compact modularity principle should guide your architecture.

**Key principles:**
1. **Each module should have a single, clear purpose** - High cohesion
2. **Modules should be loosely coupled** - Minimize interdependencies
3. **Public APIs should be explicit** - Use `__all__` to declare what's public
4. **Private internals should be marked** - Use `_prefix` convention

#### Structuring Modules

**Good module structure:**
```python
# src/myproject/data_processor.py
"""
Data processing utilities for MyProject.

This module provides functions for cleaning, transforming, and
validating input data.
"""

__all__ = ['process_data', 'validate_data', 'DataProcessor']

from typing import Dict, List, Optional
import logging

logger = logging.getLogger(__name__)

# Constants at module level
DEFAULT_TIMEOUT = 30
MAX_RETRIES = 3

# Exception definitions
class DataProcessingError(Exception):
    """Raised when data processing fails."""
    pass

# Main public API
class DataProcessor:
    """Main data processor class.

    Handles data transformation and validation according to
    configured rules.
    """

    def __init__(self, config: Optional[Dict] = None):
        self.config = config or {}
        self._cache = {}  # Private attribute

    def process(self, data: List[Dict]) -> List[Dict]:
        """Process input data and return cleaned results."""
        return self._transform(data)

    def _transform(self, data: List[Dict]) -> List[Dict]:
        """Internal transformation logic (not in __all__)."""
        # Implementation details
        pass

# Public functions
def process_data(data: List[Dict]) -> List[Dict]:
    """Convenience function for quick data processing."""
    processor = DataProcessor()
    return processor.process(data)

def validate_data(data: List[Dict]) -> bool:
    """Validate data structure and content."""
    # Implementation
    pass

# Private helpers (not in __all__)
def _cleanup_temp_files():
    """Internal cleanup function."""
    pass
```

**Module organization pattern:**
1. Docstring (module purpose)
2. `__all__` declaration
3. Imports (standard library → third-party → local)
4. Module-level constants
5. Exception classes
6. Main classes
7. Public functions
8. Private functions

## Idiomatic Python Patterns

### Code Style: PEP 8 Foundation

Guido van Rossum, Barry Warsaw, and Alyssa Coghlan authored PEP 8 in 2001 to enhance code readability and consistency. Follow PEP 8 rigorously:

**Naming conventions:**
- `snake_case` for variables and functions: `user_count`, `process_data()`
- `PascalCase` for classes: `DataProcessor`, `UserAccount`
- `UPPER_SNAKE_CASE` for constants: `MAX_RETRIES`, `DEFAULT_TIMEOUT`
- `_single_leading_underscore` for internal/private: `_helper_function()`, `_internal_state`
- `__double_leading_underscore` for name mangling (rare, use sparingly)

**Import organization:**
```python
# Standard library imports
import os
import sys
from pathlib import Path
from typing import Dict, List, Optional

# Third-party imports
import requests
import numpy as np

# Local application imports
from myproject.core import DataProcessor
from myproject.utils import helpers
```

### Pythonic Patterns to Embrace

#### 1. Context Managers for Resource Management

**Instead of:**
```python
f = open('data.txt')
try:
    data = f.read()
finally:
    f.close()
```

**Do this:**
```python
with open('data.txt') as f:
    data = f.read()
```

**Create custom context managers when appropriate:**
```python
from contextlib import contextmanager

@contextmanager
def database_transaction(db):
    """Context manager for database transactions."""
    try:
        yield db
        db.commit()
    except Exception:
        db.rollback()
        raise

# Usage
with database_transaction(db) as transaction:
    transaction.execute("INSERT ...")
```

#### 2. List Comprehensions and Generator Expressions

**Readable and efficient:**
```python
# List comprehension
squares = [x**2 for x in range(10)]
filtered = [x for x in data if x.is_valid()]

# Generator expression (memory efficient)
total = sum(x**2 for x in large_dataset)

# Dict comprehension
mapping = {key: value.upper() for key, value in items.items()}
```

**Avoid over-complication** - if comprehension gets complex, use explicit loops:
```python
# Too complex - hard to read
result = [transform(x) for sublist in data
          for x in sublist if validate(x)
          and x not in seen]

# Better - explicit and clear
result = []
for sublist in data:
    for x in sublist:
        if validate(x) and x not in seen:
            result.append(transform(x))
```

#### 3. Leverage the Standard Library

Python's strength is its "batteries included" philosophy. Use the standard library before reaching for third-party packages:

**Collections module:**
```python
from collections import defaultdict, Counter, namedtuple

# defaultdict eliminates boilerplate
word_count = defaultdict(int)
for word in words:
    word_count[word] += 1

# Counter for frequency counting
letter_frequency = Counter("hello world")

# namedtuple for simple data structures
Point = namedtuple('Point', ['x', 'y'])
p = Point(10, 20)
```

**Itertools for efficient iteration:**
```python
from itertools import chain, groupby, islice

# Chain multiple iterables
all_items = chain(list1, list2, list3)

# Group consecutive items
grouped = groupby(sorted_data, key=lambda x: x.category)
```

**Pathlib for file operations:**
```python
from pathlib import Path

# Modern, object-oriented path handling
project_root = Path(__file__).parent.parent
config_file = project_root / "config" / "settings.toml"

if config_file.exists():
    content = config_file.read_text()
```

#### 4. Duck Typing and Protocols

**Embrace duck typing** - "If it walks like a duck and quacks like a duck, it's a duck"

```python
from typing import Protocol

# Define behavior expectations, not rigid types
class Drawable(Protocol):
    """Anything that can be drawn."""
    def draw(self) -> None: ...

def render_scene(objects: list[Drawable]) -> None:
    """Render all drawable objects."""
    for obj in objects:
        obj.draw()  # Works with any object that has draw()
```

#### 5. Explicit is Better than Implicit

**Bad - implicit behavior:**
```python
def process(data, mode=1):
    if mode == 1:
        return data.upper()
    elif mode == 2:
        return data.lower()
```

**Good - explicit intent:**
```python
from enum import Enum

class ProcessMode(Enum):
    UPPERCASE = "uppercase"
    LOWERCASE = "lowercase"

def process(data: str, mode: ProcessMode) -> str:
    """Process data according to specified mode."""
    if mode == ProcessMode.UPPERCASE:
        return data.upper()
    elif mode == ProcessMode.LOWERCASE:
        return data.lower()
    raise ValueError(f"Unknown mode: {mode}")
```

## Modern Development Practices

### Quality Assurance Pipeline

For serious Python work, establish these practices:

**1. Linting and Type Checking:**
```bash
# Install tools
pip install pylint mypy black isort

# Configuration in pyproject.toml
[tool.black]
line-length = 100
target-version = ['py39', 'py310', 'py311']

[tool.isort]
profile = "black"
line_length = 100

[tool.mypy]
strict = true
warn_return_any = true
warn_unused_configs = true

# Run checks
pylint src/
mypy src/
black src/
isort src/
```

**2. Testing Strategy:**
```python
# tests/test_processor.py
import pytest
from myproject.processor import DataProcessor

def test_processor_basic():
    """Test basic processing functionality."""
    processor = DataProcessor()
    result = processor.process([{"name": "test"}])
    assert len(result) == 1

@pytest.fixture
def sample_data():
    """Provide sample data for tests."""
    return [{"id": 1, "value": "test"}]

def test_with_fixture(sample_data):
    """Test using fixture."""
    processor = DataProcessor()
    result = processor.process(sample_data)
    assert result is not None
```

**3. Continuous Integration:**
```yaml
# .github/workflows/test.yml (example)
name: Tests
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      - run: pip install -e ".[dev]"
      - run: pylint src/
      - run: mypy src/
      - run: pytest
```

### Version Management and Migration

**Guido's principle**: Python must always consider how to support old applications without forcing changes. When designing APIs:

1. **Deprecate gradually** - Warn before removing
2. **Support version ranges** - Most libraries support multiple Python versions
3. **Use `__future__` imports** for forward compatibility:
```python
from __future__ import annotations  # PEP 563 - postponed annotation evaluation
```

### Documentation Standards

**Module docstrings:**
```python
"""
myproject.data_processor
~~~~~~~~~~~~~~~~~~~~~~~~

This module provides data processing utilities for cleaning and
transforming input data.

Example usage:
    >>> from myproject.data_processor import process_data
    >>> result = process_data([{"name": "test"}])
    >>> print(result)
    [{"name": "TEST"}]
"""
```

**Function/method docstrings:**
```python
def process_data(data: List[Dict], strict: bool = True) -> List[Dict]:
    """Process and validate input data.

    Args:
        data: List of dictionaries containing raw data
        strict: If True, raise errors on invalid data. If False, skip invalid items.

    Returns:
        List of processed and validated dictionaries

    Raises:
        DataProcessingError: If strict=True and invalid data encountered

    Example:
        >>> process_data([{"id": 1, "name": "test"}])
        [{"id": 1, "name": "TEST"}]
    """
```

## Hands-On Coding Approach

When writing code in this skill's context:

1. **Start with the interface** - Define what users will interact with first
2. **Write docstrings early** - If the interface is hard to explain, it's a bad design
3. **Favor composition over inheritance** - More Pythonic and flexible
4. **Use dataclasses for data structures** - Modern, clean, and explicit
5. **Handle errors explicitly** - Don't hide exceptions or use bare except clauses
6. **Test as you go** - Write tests that document expected behavior

**Example of well-structured Python code:**

```python
"""User authentication and authorization module."""

from dataclasses import dataclass
from typing import Optional
from datetime import datetime, timedelta
import hashlib
import secrets

@dataclass
class User:
    """Represents an authenticated user."""
    username: str
    email: str
    password_hash: str
    created_at: datetime
    is_active: bool = True

    def verify_password(self, password: str) -> bool:
        """Verify provided password against stored hash."""
        password_hash = self._hash_password(password)
        return secrets.compare_digest(password_hash, self.password_hash)

    @staticmethod
    def _hash_password(password: str) -> str:
        """Hash password using secure algorithm."""
        return hashlib.sha256(password.encode()).hexdigest()

class AuthenticationError(Exception):
    """Raised when authentication fails."""
    pass

class UserAuthenticator:
    """Handles user authentication operations."""

    def __init__(self, session_duration: timedelta = timedelta(hours=24)):
        self.session_duration = session_duration
        self._sessions: dict[str, User] = {}

    def authenticate(self, username: str, password: str) -> Optional[str]:
        """Authenticate user and return session token.

        Args:
            username: User's username
            password: User's password (plain text)

        Returns:
            Session token if authentication successful, None otherwise

        Raises:
            AuthenticationError: If user not found or inactive
        """
        user = self._get_user(username)
        if not user:
            raise AuthenticationError(f"User {username} not found")

        if not user.is_active:
            raise AuthenticationError(f"User {username} is inactive")

        if user.verify_password(password):
            return self._create_session(user)

        return None

    def _get_user(self, username: str) -> Optional[User]:
        """Retrieve user from storage (placeholder)."""
        # Implementation would query database
        pass

    def _create_session(self, user: User) -> str:
        """Create and store session for authenticated user."""
        token = secrets.token_urlsafe(32)
        self._sessions[token] = user
        return token
```

## Quick Reference: Common Tasks

### Setting Up a New Project

```bash
# Create project structure
mkdir -p myproject/{src/myproject,tests,docs}
cd myproject

# Initialize git
git init
echo "__pycache__/\n*.pyc\n.pytest_cache/\n.mypy_cache/\ndist/\nbuild/" > .gitignore

# Create pyproject.toml
cat > pyproject.toml << 'EOF'
[build-system]
requires = ["setuptools>=61.0"]
build-backend = "setuptools.build_meta"

[project]
name = "myproject"
version = "0.1.0"
requires-python = ">=3.9"
EOF

# Set up virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dev tools
pip install pytest mypy pylint black isort
```

### Refactoring Existing Code

When refactoring toward better architecture:

1. **Add tests first** - Ensure behavior is documented
2. **Extract functions** - Break down large functions
3. **Identify modules** - Group related functionality
4. **Make implicit explicit** - Add type hints and docstrings
5. **Run linters** - Let tools guide improvements
6. **Refactor incrementally** - Small, tested changes

## References

For deeper dives into specific topics, see the reference documentation:

- `references/zen_of_python.md` - Complete Zen of Python with detailed explanations
- `references/project_templates.md` - Full project structure templates for different scales
- `references/type_hints_guide.md` - Comprehensive type hinting patterns and mypy configuration

These references provide extensive examples and detailed guidance that complement the core principles outlined above.
