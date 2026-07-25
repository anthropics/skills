#!/usr/bin/env python3
"""Shared ruamel.yaml round-trip configuration for passport migration tools.

For tools that **mutate and re-emit** passport YAML (preserving comments,
key order, quoting). Read-only validators should keep using `yaml.safe_load`.

Previously duplicated byte-equivalently in
`migrate_literature_corpus_to_v3_7_3.py` and
`migrate_literature_corpus_to_v3_9_0.py`. Extracted in #128 (v3.9.1
housekeeping) so future migration tools inherit the spec-aligned round-trip
shape without re-deriving it.

Behavior must remain byte-equivalent with the per-tool configuration that
was verified across multiple v3.7.3 / v3.9.0 review rounds. See
`test_passport_yaml.py` for the configuration + round-trip contract.

Configuration:
- preserve_quotes = True → keeps single vs double quoting choice.
- indent(mapping=2, sequence=4, offset=2) → sequence items align with `- `
  two spaces past the parent key, matching the passport convention used
  by `shared/contracts/passport/literature_corpus_entry.schema.json` examples.

Thread-safety: single-threaded use only. The module-level `_yaml` is a shared
mutable singleton; instantiate per-thread (or per-call) if future tools
parallelize passport migration.
"""
from __future__ import annotations

from pathlib import Path
from typing import Any

from ruamel.yaml import YAML


# Single shared YAML round-tripper. ruamel.yaml preserves comments,
# key order, and quoting style across read → mutate → write.
_yaml = YAML()
_yaml.preserve_quotes = True
_yaml.indent(mapping=2, sequence=4, offset=2)


def load_passport(path: Path) -> Any:
    """Round-trip load a passport YAML file. Returns the ruamel-yaml
    representation (a CommentedMap), not a plain dict."""
    with path.open("r", encoding="utf-8") as f:
        return _yaml.load(f)


def dump_passport(path: Path, doc: Any) -> None:
    """Round-trip dump a passport YAML document back to disk, preserving
    comments / key order / quoting style from the matching load."""
    with path.open("w", encoding="utf-8") as f:
        _yaml.dump(doc, f)
