"""pytest configuration + shared fixtures for adapter tests.

Provides:
- `repo_root` : Path to the ARS repo root
- `adapters_dir` : Path to scripts/adapters/
- `examples_dir` : Path to scripts/adapters/examples/
- `clean_timestamps(doc, extra_blank=None)` : helper that blanks
   `generated_at` and `obtained_at` by default. Pass `extra_blank` to
   widen the blanking set (e.g., folder_scan tests pass
   `extra_blank={"source_pointer", "input_source"}` because absolute
   filesystem paths drift across machines; T8/T9 keep their
   `zotero://N` / `obsidian://N` pointers asserted directly so
   broken pointers cannot slip through golden tests).
- `load_yaml(path)` : convenience YAML loader.
"""
from __future__ import annotations
from pathlib import Path
import copy
import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[3]


@pytest.fixture(scope="session")
def repo_root() -> Path:
    return REPO_ROOT


@pytest.fixture(scope="session")
def adapters_dir() -> Path:
    return REPO_ROOT / "scripts/adapters"


@pytest.fixture(scope="session")
def examples_dir() -> Path:
    return REPO_ROOT / "scripts/adapters/examples"


def _strip_keys(obj, keys_to_blank: set[str]):
    if isinstance(obj, dict):
        return {
            k: ("<TIMESTAMP>" if k in keys_to_blank else _strip_keys(v, keys_to_blank))
            for k, v in obj.items()
        }
    if isinstance(obj, list):
        return [_strip_keys(v, keys_to_blank) for v in obj]
    return obj


_DEFAULT_BLANK = {"generated_at", "obtained_at"}


@pytest.fixture
def clean_timestamps():
    """Return a function `_clean(doc, extra_blank=None)` that returns a copy
    of a dict/list with timestamp-like fields blanked to '<TIMESTAMP>'.

    By default only `generated_at` and `obtained_at` are blanked.
    Adapters whose `source_pointer` is a machine-dependent absolute path
    (folder_scan) should pass `extra_blank={"source_pointer", "input_source"}`
    explicitly. Adapters whose `source_pointer` is a deterministic logical
    URI (zotero://N, obsidian://path) should NOT widen, so broken pointers
    fail the golden test loudly."""
    def _clean(doc, extra_blank: set[str] | None = None):
        keys = _DEFAULT_BLANK | (extra_blank or set())
        return _strip_keys(copy.deepcopy(doc), keys)
    return _clean


@pytest.fixture
def load_yaml():
    """Return a function that loads a YAML file into a Python dict."""
    def _load(path: Path):
        with path.open("r", encoding="utf-8") as f:
            return yaml.safe_load(f)
    return _load
