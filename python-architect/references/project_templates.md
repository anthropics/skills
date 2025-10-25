# Python Project Structure Templates

This reference provides complete project structure templates for different project scales, from simple scripts to enterprise applications.

## Template Selection Guide

Choose a template based on:
- **Code size** (lines of code)
- **Team size** (solo vs. team)
- **Lifecycle** (throwaway script vs. long-term maintenance)
- **Distribution** (internal tool vs. published package)

## Template 1: Simple Script (<500 lines)

**Use when**: Single-purpose automation, data processing script, one-off tool

```
my_script/
├── script.py              # Main script
├── README.md              # Usage instructions
└── requirements.txt       # Dependencies (if any)
```

**Example structure**:
```python
# script.py
"""
Script to process log files and generate reports.

Usage:
    python script.py input.log output.csv
"""

import sys
import csv
from pathlib import Path
from typing import List, Dict

def parse_log_line(line: str) -> Dict[str, str]:
    """Parse a single log line into structured data."""
    # Implementation
    pass

def process_log_file(input_path: Path) -> List[Dict[str, str]]:
    """Process entire log file."""
    results = []
    with open(input_path) as f:
        for line in f:
            results.append(parse_log_line(line))
    return results

def write_csv(data: List[Dict[str, str]], output_path: Path):
    """Write processed data to CSV."""
    with open(output_path, 'w', newline='') as f:
        if not data:
            return
        writer = csv.DictWriter(f, fieldnames=data[0].keys())
        writer.writeheader()
        writer.writerows(data)

def main():
    """Main entry point."""
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)

    input_file = Path(sys.argv[1])
    output_file = Path(sys.argv[2])

    data = process_log_file(input_file)
    write_csv(data, output_file)
    print(f"Processed {len(data)} records to {output_file}")

if __name__ == "__main__":
    main()
```

**requirements.txt**:
```
# No external dependencies for this example
# Add dependencies as needed:
# requests>=2.28.0
# pandas>=1.5.0
```

**README.md**:
```markdown
# Log Processor

Processes server log files and generates CSV reports.

## Usage

python script.py input.log output.csv

## Requirements

Python 3.9+
```

## Template 2: Small Project (500-5,000 lines)

**Use when**: Small library, tool with multiple modules, team of 1-3 developers

```
project_name/
├── README.md
├── LICENSE
├── pyproject.toml
├── requirements.txt
├── .gitignore
├── src/
│   └── project_name/
│       ├── __init__.py
│       ├── __main__.py        # Optional: enables `python -m project_name`
│       ├── core.py            # Main functionality
│       ├── utils.py           # Utility functions
│       └── cli.py             # Command-line interface
├── tests/
│   ├── __init__.py
│   ├── test_core.py
│   └── test_utils.py
└── docs/
    └── usage.md
```

**Key files**:

**pyproject.toml**:
```toml
[build-system]
requires = ["setuptools>=61.0", "wheel"]
build-backend = "setuptools.build_meta"

[project]
name = "project-name"
version = "0.1.0"
description = "A brief description of the project"
readme = "README.md"
authors = [
    {name = "Your Name", email = "your.email@example.com"}
]
license = {text = "MIT"}
requires-python = ">=3.9"
classifiers = [
    "Programming Language :: Python :: 3",
    "License :: OSI Approved :: MIT License",
    "Operating System :: OS Independent",
]
dependencies = [
    "requests>=2.28.0",
]

[project.optional-dependencies]
dev = [
    "pytest>=7.0",
    "pytest-cov>=4.0",
    "black>=22.0",
    "isort>=5.10",
]

[project.scripts]
project-name = "project_name.cli:main"

[tool.black]
line-length = 100

[tool.isort]
profile = "black"
line_length = 100

[tool.pytest.ini_options]
testpaths = ["tests"]
python_files = ["test_*.py"]
```

**src/project_name/__init__.py**:
```python
"""
project-name: A brief description.

Example usage:
    from project_name import process_data

    result = process_data(input_data)
"""

__version__ = "0.1.0"

from .core import process_data, DataProcessor

__all__ = ["process_data", "DataProcessor", "__version__"]
```

**src/project_name/__main__.py**:
```python
"""Allow running as python -m project_name."""
from .cli import main

if __name__ == "__main__":
    main()
```

**src/project_name/cli.py**:
```python
"""Command-line interface for project-name."""
import argparse
import sys
from pathlib import Path

from . import __version__
from .core import process_data

def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Process data with project-name"
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"%(prog)s {__version__}"
    )
    parser.add_argument(
        "input",
        type=Path,
        help="Input file path"
    )
    parser.add_argument(
        "-o", "--output",
        type=Path,
        help="Output file path (default: stdout)"
    )

    args = parser.parse_args()

    try:
        result = process_data(args.input)
        if args.output:
            args.output.write_text(result)
        else:
            print(result)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
```

**.gitignore**:
```
# Python
__pycache__/
*.py[cod]
*$py.class
*.so
.Python
env/
venv/
build/
develop-eggs/
dist/
downloads/
eggs/
.eggs/
lib/
lib64/
parts/
sdist/
var/
wheels/
*.egg-info/
.installed.cfg
*.egg

# Testing
.pytest_cache/
.coverage
htmlcov/

# IDEs
.vscode/
.idea/
*.swp
*.swo
*~

# mypy
.mypy_cache/
```

## Template 3: Medium Project (5,000-50,000 lines)

**Use when**: Application, library with multiple submodules, team of 3-10 developers

```
project_name/
├── README.md
├── LICENSE
├── pyproject.toml
├── requirements.txt
├── requirements-dev.txt
├── .gitignore
├── .github/
│   └── workflows/
│       ├── test.yml
│       └── publish.yml
├── src/
│   └── project_name/
│       ├── __init__.py
│       ├── __main__.py
│       ├── cli.py
│       ├── config.py
│       ├── exceptions.py
│       ├── core/
│       │   ├── __init__.py
│       │   ├── processor.py
│       │   └── validator.py
│       ├── models/
│       │   ├── __init__.py
│       │   ├── data.py
│       │   └── results.py
│       ├── utils/
│       │   ├── __init__.py
│       │   ├── helpers.py
│       │   └── converters.py
│       └── api/
│           ├── __init__.py
│           ├── client.py
│           └── endpoints.py
├── tests/
│   ├── __init__.py
│   ├── conftest.py
│   ├── test_core/
│   │   ├── __init__.py
│   │   ├── test_processor.py
│   │   └── test_validator.py
│   ├── test_models/
│   │   └── test_data.py
│   ├── test_integration/
│   │   └── test_workflow.py
│   └── fixtures/
│       └── sample_data.json
├── docs/
│   ├── conf.py
│   ├── index.rst
│   ├── api.rst
│   ├── usage.rst
│   └── development.rst
└── scripts/
    ├── setup_dev.sh
    └── run_checks.sh
```

**Additional key files**:

**requirements-dev.txt**:
```
# Development dependencies
pytest>=7.0
pytest-cov>=4.0
pytest-mock>=3.10
black>=22.0
isort>=5.10
mypy>=1.0
pylint>=2.15
sphinx>=5.0
sphinx-rtd-theme>=1.0
```

**src/project_name/config.py**:
```python
"""Configuration management for project_name."""
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional
import os

@dataclass
class Config:
    """Application configuration."""

    # Paths
    data_dir: Path = field(default_factory=lambda: Path.home() / ".project_name")
    cache_dir: Optional[Path] = None

    # API settings
    api_base_url: str = "https://api.example.com"
    api_timeout: int = 30
    api_retries: int = 3

    # Processing settings
    batch_size: int = 100
    max_workers: int = 4

    # Feature flags
    enable_caching: bool = True
    debug_mode: bool = False

    def __post_init__(self):
        """Validate and setup configuration."""
        self.data_dir.mkdir(parents=True, exist_ok=True)

        if self.cache_dir is None:
            self.cache_dir = self.data_dir / "cache"

        # Load from environment
        if api_key := os.getenv("PROJECT_NAME_API_KEY"):
            self.api_key = api_key

    @classmethod
    def from_file(cls, path: Path) -> "Config":
        """Load configuration from TOML file."""
        import tomli
        with open(path, "rb") as f:
            data = tomli.load(f)
        return cls(**data)

# Global default config
_config: Optional[Config] = None

def get_config() -> Config:
    """Get global configuration instance."""
    global _config
    if _config is None:
        _config = Config()
    return _config

def set_config(config: Config):
    """Set global configuration instance."""
    global _config
    _config = config
```

**src/project_name/exceptions.py**:
```python
"""Custom exceptions for project_name."""

class ProjectNameError(Exception):
    """Base exception for all project_name errors."""
    pass

class ConfigurationError(ProjectNameError):
    """Raised when configuration is invalid."""
    pass

class ValidationError(ProjectNameError):
    """Raised when data validation fails."""
    pass

class ProcessingError(ProjectNameError):
    """Raised when data processing fails."""
    pass

class APIError(ProjectNameError):
    """Raised when API requests fail."""

    def __init__(self, message: str, status_code: Optional[int] = None):
        super().__init__(message)
        self.status_code = status_code
```

**tests/conftest.py**:
```python
"""Pytest configuration and shared fixtures."""
import pytest
from pathlib import Path
from project_name.config import Config

@pytest.fixture
def temp_config(tmp_path):
    """Provide a temporary configuration for testing."""
    config = Config(
        data_dir=tmp_path / "data",
        cache_dir=tmp_path / "cache",
        enable_caching=False,
        debug_mode=True
    )
    return config

@pytest.fixture
def sample_data():
    """Load sample data for tests."""
    fixtures_dir = Path(__file__).parent / "fixtures"
    with open(fixtures_dir / "sample_data.json") as f:
        import json
        return json.load(f)
```

**.github/workflows/test.yml**:
```yaml
name: Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        python-version: ["3.9", "3.10", "3.11"]

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python ${{ matrix.python-version }}
      uses: actions/setup-python@v4
      with:
        python-version: ${{ matrix.python-version }}

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -e ".[dev]"

    - name: Lint with pylint
      run: pylint src/

    - name: Type check with mypy
      run: mypy src/

    - name: Format check with black
      run: black --check src/ tests/

    - name: Import order check with isort
      run: isort --check-only src/ tests/

    - name: Test with pytest
      run: pytest --cov=project_name --cov-report=xml

    - name: Upload coverage
      uses: codecov/codecov-action@v3
      if: matrix.os == 'ubuntu-latest' && matrix.python-version == '3.11'
```

**scripts/run_checks.sh**:
```bash
#!/bin/bash
# Run all code quality checks

set -e

echo "Running black..."
black src/ tests/

echo "Running isort..."
isort src/ tests/

echo "Running pylint..."
pylint src/

echo "Running mypy..."
mypy src/

echo "Running pytest..."
pytest --cov=project_name --cov-report=html

echo "All checks passed!"
```

## Template 4: Large Project (>50,000 lines)

**Use when**: Enterprise application, platform, large team

```
project_name/
├── README.md
├── LICENSE
├── pyproject.toml
├── requirements.txt
├── requirements-dev.txt
├── docker-compose.yml
├── Dockerfile
├── .gitignore
├── .github/
│   ├── workflows/
│   │   ├── test.yml
│   │   ├── publish.yml
│   │   └── deploy.yml
│   └── CODEOWNERS
├── src/
│   └── project_name/
│       ├── __init__.py
│       ├── __main__.py
│       ├── cli/
│       │   ├── __init__.py
│       │   ├── main.py
│       │   ├── commands/
│       │   │   ├── __init__.py
│       │   │   ├── process.py
│       │   │   └── export.py
│       │   └── formatters/
│       ├── core/
│       │   ├── __init__.py
│       │   ├── engine.py
│       │   ├── pipeline.py
│       │   └── strategies/
│       ├── models/
│       │   ├── __init__.py
│       │   ├── base.py
│       │   ├── domain/
│       │   └── dto/
│       ├── services/
│       │   ├── __init__.py
│       │   ├── processor.py
│       │   ├── storage.py
│       │   └── notification.py
│       ├── adapters/
│       │   ├── __init__.py
│       │   ├── database/
│       │   ├── cache/
│       │   └── queue/
│       ├── api/
│       │   ├── __init__.py
│       │   ├── rest/
│       │   └── graphql/
│       ├── config/
│       │   ├── __init__.py
│       │   ├── settings.py
│       │   └── environments/
│       ├── utils/
│       │   ├── __init__.py
│       │   ├── logging.py
│       │   ├── metrics.py
│       │   └── decorators.py
│       └── exceptions.py
├── tests/
│   ├── unit/
│   ├── integration/
│   ├── e2e/
│   ├── performance/
│   ├── conftest.py
│   └── fixtures/
├── docs/
│   ├── source/
│   │   ├── conf.py
│   │   ├── index.rst
│   │   ├── architecture/
│   │   ├── api/
│   │   └── guides/
│   └── Makefile
├── scripts/
│   ├── setup_dev.sh
│   ├── run_checks.sh
│   ├── deploy.sh
│   └── migrations/
├── config/
│   ├── development.toml
│   ├── staging.toml
│   └── production.toml
└── deployments/
    ├── kubernetes/
    └── terraform/
```

**Key architectural patterns for large projects**:

1. **Layered architecture**:
   - `models/`: Domain models and data structures
   - `services/`: Business logic layer
   - `adapters/`: External system integrations
   - `api/`: Presentation layer

2. **Dependency injection**:
```python
# src/project_name/services/processor.py
from typing import Protocol

class StorageAdapter(Protocol):
    """Storage adapter interface."""
    def save(self, data): ...
    def load(self, key): ...

class ProcessorService:
    """Main processing service with injected dependencies."""

    def __init__(self, storage: StorageAdapter, notifier):
        self.storage = storage
        self.notifier = notifier

    def process(self, data):
        result = self._transform(data)
        self.storage.save(result)
        self.notifier.notify_completion()
        return result
```

3. **Configuration management**:
```python
# src/project_name/config/settings.py
from pydantic import BaseSettings, Field

class Settings(BaseSettings):
    """Application settings with validation."""

    # Database
    database_url: str = Field(..., env="DATABASE_URL")
    database_pool_size: int = Field(10, env="DATABASE_POOL_SIZE")

    # Cache
    redis_url: str = Field(..., env="REDIS_URL")

    # API
    api_key: str = Field(..., env="API_KEY")
    api_rate_limit: int = 1000

    # Feature flags
    enable_analytics: bool = True
    enable_experimental: bool = False

    class Config:
        env_file = ".env"
        case_sensitive = False

settings = Settings()
```

## Quick Start Commands

### Simple Project Setup
```bash
mkdir my_project && cd my_project
python -m venv venv
source venv/bin/activate
pip install pytest black isort
```

### Medium Project Setup
```bash
mkdir -p my_project/{src/my_project,tests,docs}
cd my_project
python -m venv venv
source venv/bin/activate
pip install -e ".[dev]"
```

### Initialize Git
```bash
git init
echo "__pycache__/\n*.pyc\n.pytest_cache/\nvenv/" > .gitignore
git add .
git commit -m "Initial commit"
```

## Summary

Choose the simplest template that meets your needs. Start small and grow the structure as the project grows. Don't over-engineer from the beginning - follow Guido's principle of "good enough" over perfect.
