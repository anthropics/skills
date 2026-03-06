---
name: production-python
description: Apply production-grade Python coding conventions when writing or modifying any Python code. Use this skill for new modules, classes, functions, Pydantic models, SQLAlchemy models, or tests. Enforces module structure, section markers, type hints, Google docstrings, import organization, logging, naming, error handling, CHANGELOG, and README conventions.
---

Production-grade Python coding conventions for any project. Apply every rule below whenever writing or modifying Python code.

---

## 1. Module Header

Every `.py` file starts with a module docstring — no exceptions:

```python
"""
Module Name: filename.py

Description:
    Clear, concise description of the module's purpose and role
    in the overall system. Can span multiple lines.
"""
```

No author, date, or version — that belongs in version control.

---

## 2. Section Markers

Every logical section is wrapped in 77-character dash lines. Always add a blank line before and after each marker block:

```python
# --------------------------------------------------------------------------
# SECTION: Imports
# --------------------------------------------------------------------------

[imports here]

# --------------------------------------------------------------------------
# SECTION: Logger Initialization
# --------------------------------------------------------------------------

logger = setup_logger(__name__)

# --------------------------------------------------------------------------
# SECTION: Constants
# --------------------------------------------------------------------------

DEFAULT_VALUE = 100

# --------------------------------------------------------------------------
# SECTION: Main Class / Functions
# --------------------------------------------------------------------------

[code here]
```

Standard section order (include only what's needed):
`Imports` → `Logger Initialization` → `Constants` → `Type Aliases` → [content sections]

**Class internal sub-sections** use a shorter inline style:

```python
class ExampleClass:
    # --- Constructor ---
    def __init__(self, param: str) -> None: ...

    # --- Configuration ---
    def _load_config(self) -> Dict: ...

    # --- Public API ---
    def process(self, data: List[Dict]) -> pd.DataFrame: ...

    # --- Private Helpers ---
    def _validate(self) -> None: ...
```

---

## 3. End-of-Module Marker (mandatory)

The very last thing in every `.py` file — no code, comments, or blank lines after it:

```python
# --------------------------------------------------------------------------
# END OF MODULE
# --------------------------------------------------------------------------
```

---

## 4. Import Organization — 3 groups, always

```python
# Standard library imports
import logging
import os
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

# Third-party imports
import pandas as pd
from pydantic import BaseModel

# Local application imports
from src.logger import setup_logger
from src.utils.helpers import load_prompt
```

Rules:
- Sort **alphabetically within each group** — bare `import X` before `from X import Y`, then alphabetical
- Group multiple imports from the same module on one line: `from typing import Dict, List, Optional`
- One module per line when importing different modules: separate `import logging` from `import os`
- Absolute imports only — never `from .module import x` or `from ..utils import y`
- Never `import *`
- Include all three comment headers even if only one group has entries

---

## 5. Logger — Canonical `logger.py` Implementation

Every project needs a central `logger.py`. Reference implementation:

```python
"""
Module Name: logger.py

Description:
    Centralized logging configuration.
    Rotating file handler + console handler with noise suppression.
"""

# --------------------------------------------------------------------------
# SECTION: Imports
# --------------------------------------------------------------------------

# Standard library imports
import logging
import os
import sys
from logging.handlers import RotatingFileHandler

# --------------------------------------------------------------------------
# SECTION: Setup Logger
# --------------------------------------------------------------------------

def setup_logger(
    name: str,
    log_dir: str = "logs",
    log_file: str = "app.log",
    max_bytes: int = 5 * 1024 * 1024,
    backup_count: int = 5,
) -> logging.Logger:
    """
    Set up a logger with rotating file and console handlers.

    Args:
        name: Logger name — always pass __name__ from the calling module.
        log_dir: Directory to write log files (created if missing).
        log_file: Log file name.
        max_bytes: Max file size before rotation. Default: 5 MB.
        backup_count: Number of rotated files to retain.

    Returns:
        Configured Logger instance.
    """
    os.makedirs(log_dir, exist_ok=True)
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)

    formatter = logging.Formatter(
        "[%(asctime)s] %(levelname)s in %(name)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )

    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)

    file_handler = RotatingFileHandler(
        filename=os.path.join(log_dir, log_file),
        maxBytes=max_bytes,
        backupCount=backup_count,
    )
    file_handler.setLevel(logging.DEBUG)
    file_handler.setFormatter(formatter)

    if not logger.handlers:
        logger.addHandler(console_handler)
        logger.addHandler(file_handler)

    # Suppress noisy third-party library logs
    for noisy_lib in ("urllib3", "asyncio", "langchain", "httpx", "httpcore"):
        logging.getLogger(noisy_lib).setLevel(logging.CRITICAL)

    logger.propagate = False
    return logger

# --------------------------------------------------------------------------
# END OF MODULE
# --------------------------------------------------------------------------
```

**In every module** — one line, immediately after the Imports section:

```python
logger = setup_logger(__name__)
```

**Log level guide:**

```python
logger.debug(f"Chunk {i}/{total} processed — tokens: {tokens}")
logger.info(f"Processing complete — {count} records in {elapsed:.2f}s")
logger.warning(f"Unexpected mode '{mode}', falling back to default")
logger.error(f"Chain execution failed: {e}")
logger.critical("Database connection lost — shutting down")
```

Never use `print()` in production code. Always use `logger`.

---

## 6. Type Hints — Required Everywhere

**Simple functions:**

```python
def load_prompt(file_path: str) -> str: ...
def calculate_sum(a: int, b: int) -> int: ...
def process(items: List[str], limit: int = 10) -> Optional[Dict[str, int]]: ...
```

**Complex / multi-line signatures:**

```python
from typing import Any, Callable, Dict, List, Optional, Tuple

def process_chunks(
    chunks: List[Dict[str, Any]],
    prompts: List[Dict[str, str]],
    run_sequentially: bool = False,
    progress_callback: Optional[Callable] = None,
) -> Tuple[List[Dict[str, Any]], int, int]:
    """
    Returns:
        Tuple of (results, input_token_count, output_token_count).
    """
```

**Optional parameters:**

```python
def get_record(
    record_id: Optional[int] = None,
    record_code: Optional[str] = None,
) -> Optional[Record]: ...
```

**Class attributes** — document in the class docstring `Attributes:` section:

```python
class ProcessingPipeline:
    """
    Orchestrates the complete extraction workflow.

    Attributes:
        input_file_path (Path): Path to the input file.
        model_name (str): LLM model identifier.
        chunk_size (int): Size of data chunks for processing.
    """
```

Rules:
- `Optional[X]` not `X | None` (Python 3.9 compatibility)
- `List[X]`, `Dict[K, V]`, `Tuple[X, Y]` from `typing`
- Always annotate return type — even `-> None`
- Common types: `Dict[str, Any]`, `List[str]`, `Tuple[int, str]`, `Callable[[int, str], bool]`
- Use `Any` sparingly — only for truly dynamic types with no better option

---

## 7. Docstrings — Google Style on All Public APIs

**Module docstring** — top of every `.py` file (see Section 1 above).

**Class docstring** — on the class, never on `__init__`. Always include `Attributes:` when the class has instance state:

```python
class BaseAgent:
    """
    Base class providing shared methods for all LLM-based agents.

    Attributes:
        model_name (str): LLM model identifier.
        prompt_file (str): Path to the system prompt file.
        response_schema: Pydantic model for parsing model output.
    """
```

**Function/method docstring:**

```python
def fetch_data(source: str, timeout: int = 30) -> List[Dict]:
    """
    Fetch structured data from source.

    Args:
        source: URL or file path to fetch from.
        timeout: Request timeout in seconds (default: 30).

    Returns:
        List of record dicts. Empty list if nothing found.

    Raises:
        ValueError: If source is empty or malformed.
        TimeoutError: If the request exceeds timeout.
    """
```

**Pydantic field descriptions** — always use `Field(description=...)`:

```python
class DataRow(BaseModel):
    """Data model for a single extracted row."""

    row_index: int = Field(description="Row index in the original data as an integer.")
    value: str = Field(description="Extracted field value from the row.")
    confidence: float = Field(
        description="Confidence score between 0.0 and 1.0.",
        default=1.0,
    )
```

Rules:
- Class docstring on the class, not `__init__`
- One-liners acceptable for simple private helpers
- Include `Args`, `Returns`, `Raises` when applicable
- `Attributes:` format: `name (type): description`
- Don't restate the function name in the summary line

---

## 8. Naming Conventions

| Kind | Convention | Example |
|------|------------|---------|
| Variables, functions, modules | `snake_case` | `user_id`, `parse_resume()` |
| Private methods / attributes | `_prefix` | `_validate()`, `_cache` |
| Classes | `PascalCase` | `MatchResult`, `BaseAgent` |
| Constants | `UPPER_SNAKE_CASE` | `MAX_RETRIES`, `DEFAULT_TIMEOUT` |
| Type aliases | `PascalCase` | `ChunkType = Dict[str, Any]` |

Names must be **descriptive and unambiguous**. Avoid abbreviations except industry-standard ones (`url`, `id`, `db`, `api`). Avoid single-letter names except loop indices (`i`, `j`) and conventional math variables.

**Class naming patterns:**
- Agent classes: `[Domain]Agent` — `FieldAnalysisAgent`, `ProcessingAgent`
- Manager classes: `[Domain]Manager` — `ModelManager`, `ConnectionManager`
- Repository classes: `[Domain]Repository` — `JobRepository`, `CandidateRepository`
- Model classes: descriptive nouns — `Client`, `ExtractionConfig`

---

## 9. Strings & Paths

**f-strings exclusively** — never `.format()` or `%` interpolation:

```python
# ✅ Good
logger.info(f"Processing {count} records for job {job_id}")
raise ValueError(f"Invalid status: {status!r}")

# ❌ Bad
logger.info("Processing {} records".format(count))
logger.info("Processing %d records" % count)
```

**`pathlib.Path` always** — never raw string concatenation:

```python
# ✅ Good
output_path = Path(base_dir) / "results" / f"{job_id}.json"
log_file = Path("logs") / "app.log"

# ❌ Bad
output_path = base_dir + "/results/" + str(job_id) + ".json"
```

---

## 10. Error Handling

Always catch specific exceptions. Never use bare `except:`. Log before raising or returning:

```python
try:
    result = parse_document(file_path)
except FileNotFoundError:
    logger.error(f"File not found: {file_path}")
    raise
except ValueError as e:
    logger.warning(f"Parse failed for {file_path}: {e}")
    return None
```

Use custom exception classes for domain-specific errors:

```python
class ExtractionError(Exception):
    """Raised when the extraction pipeline fails."""
```

---

## 11. Pydantic Models

```python
class CandidateCreate(BaseModel):
    """Request schema for creating a candidate."""

    name: str
    email: str
    skills: List[str] = []
    experience_years: Optional[int] = None

    model_config = ConfigDict(str_strip_whitespace=True)
```

Rules:
- One model per logical concept — separate request and response models
- Use `ConfigDict` not the deprecated inner `class Config`
- Use `Field(description="...")` on all fields
- Response models always inherit from `BaseModel` — never expose ORM objects directly

---

## 12. SQLAlchemy Models (2.0 syntax)

```python
class Job(Base):
    """ORM model for the jobs table."""

    __tablename__ = "jobs"

    job_id: Mapped[uuid.UUID] = mapped_column(
        UUID(as_uuid=True), primary_key=True, default=uuid.uuid4
    )
    title: Mapped[str] = mapped_column(String(200), nullable=False)
    status: Mapped[str] = mapped_column(String(50), default="draft")
    created_at: Mapped[datetime] = mapped_column(
        DateTime(timezone=True), server_default=func.now()
    )
    updated_at: Mapped[Optional[datetime]] = mapped_column(
        DateTime(timezone=True), onupdate=func.now(), nullable=True
    )
```

Rules:
- Use `Mapped[T]` + `mapped_column()` syntax (SQLAlchemy 2.0) — never legacy `Column()`
- UUID primary keys with `default=uuid.uuid4`
- All timestamps with `timezone=True`
- `server_default=func.now()` for DB-managed timestamps
- No business logic in model classes — pure data containers only
- Never use `max()` on UUID columns in queries — use `row_number()` window functions instead

---

## 13. Anti-Patterns — Never Do These

```python
# ❌ Bare except — hides all bugs
try: ...
except: ...

# ❌ print() in production code — use logger
print("done")

# ❌ Mutable default argument — shared state bug
def add_item(items=[]):      # Bug: list is shared across all calls
    items.append(1)

# ❌ Wildcard import — pollutes namespace, breaks tooling
from module import *

# ❌ String path concatenation — use pathlib
path = "/base/" + subdir + "/file.txt"

# ❌ .format() or % strings — use f-strings
msg = "Hello %s" % name

# ❌ Relative imports — use absolute imports
from .utils import helper

# ❌ Logic in __init__.py — keep it to re-exports only

# ❌ God functions (> ~50 lines) — break into focused helpers

# ❌ Hardcoded credentials or environment-specific values in code
API_KEY = "sk-abc123"       # Use environment variables
```

---

## 14. Pre-Commit Checklist

Before marking any Python file complete, verify:

- [ ] Module docstring with `Module Name:` and `Description:`
- [ ] Section markers (77-dash lines) around every logical section, blank line before and after
- [ ] `# END OF MODULE` as the very last line
- [ ] Imports in 3 groups with comment headers, sorted alphabetically within each group
- [ ] `logger = setup_logger(__name__)` in Logger Initialization section
- [ ] All public functions have type hints on all args + return type
- [ ] All public functions and classes have Google-style docstrings
- [ ] No `print()` statements anywhere
- [ ] No bare `except:` — always catch specific exception types
- [ ] No mutable default arguments
- [ ] f-strings throughout — no `.format()` or `%`
- [ ] `pathlib.Path` for any file path operations

---

## 15. CHANGELOG.md Format

Follow [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) + [Semantic Versioning](https://semver.org/):

```markdown
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

---

## [1.2.0] — 2026-02-22

### Added
- New feature description (bullet points)
- Include file paths when relevant: `path/to/module.py`

### Changed
- Modifications to existing features; mark breaking changes clearly

### Fixed
- Bug fixes with enough context to understand the change

### Removed
- Previously deprecated features now gone

### Security
- Security updates; include CVE numbers when applicable
```

Rules:
- **Reverse chronological order** — newest release at top
- Dates always `YYYY-MM-DD` (ISO 8601)
- Only include sections that have content — omit empty `### Added` headings
- Semantic versioning:
  - MAJOR: breaking changes
  - MINOR: new backwards-compatible features
  - PATCH: backwards-compatible bug fixes

---

## 16. README.md Structure

Required sections in this order:

```markdown
# Project Title

One-sentence description of what the project does.

---

## Stack

| Layer | Technology |
|-------|------------|
| Backend | Python 3.12 · FastAPI |

---

## Architecture

Brief overview of key flows or design decisions (3–5 sentences or a diagram).

---

## Quick Start

### Prerequisites
- Requirement 1

### Setup
​```bash
# Numbered commands — keep it genuinely quick (< 5 steps to running state)
​```

---

## Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|

---

## Development

Hot reload notes, migration commands, test commands.

---

## Project Structure

​```
project/
├── src/         # Source code
├── tests/       # Tests
└── docs/        # Documentation
​```

---

## Docs

- [Architecture](docs/architecture.md)
- [Style Guide](docs/coding_style_guide.md)
```

Principles:
- Start broad (what + why), get specific (how)
- Features and architecture before implementation details
- Link to detailed docs — don't duplicate content in README
- Quick Start must be genuinely quick

---

## 17. Jupyter Notebooks

- All notebooks live in `notebooks/` organized by purpose
- File naming: `snake_case`, descriptive, **no dates** in filename — use git history
  - Good: `extraction_analysis.ipynb`, `db_setup.ipynb`
  - Bad: `analysis_2026_02_22.ipynb`
- Standard structure:
  1. Markdown title cell — state the notebook's purpose
  2. Imports cell — same 3-group import pattern as `.py` files
  3. Configuration cell — paths, constants, flags
  4. Processing cells
  5. Results / visualization cells
- Use `setup_logger(__name__)` in notebooks the same as in `.py` files
- Clear large outputs before committing (avoid bloating the repo)

---

## 18. Package Management with `uv`

Use `uv` for all Python dependency management — 10–100× faster than pip:

```bash
# Add dependency — auto-updates pyproject.toml + uv.lock
uv add fastapi
uv add pandas==2.2.3         # Pin exact version for production

# Add dev dependency
uv add --dev pytest ruff black

# Install from lock file (reproducible)
uv sync

# CI/CD — production only, never modifies the lock file
uv sync --no-dev --frozen

# Update dependencies
uv lock --upgrade && uv sync
```

`pyproject.toml` key rules:
- Pin exact versions in production: `"fastapi==0.115.12"`
- Always commit both `pyproject.toml` **and** `uv.lock`
- Dev tools go under `[project.optional-dependencies]`

Dockerfile pattern with `uv`:

```dockerfile
COPY --from=ghcr.io/astral-sh/uv:latest /uv /usr/local/bin/uv
COPY pyproject.toml uv.lock ./
RUN uv sync --system --no-dev --frozen
COPY . .
```
