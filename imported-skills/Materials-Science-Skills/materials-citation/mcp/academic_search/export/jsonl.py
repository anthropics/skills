"""JSON Lines export for citation records."""

from __future__ import annotations

import json
from typing import Any


def build_jsonl(records: list[dict[str, Any]]) -> str:
    return "".join(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n" for record in records)
