"""Shared helpers for registry-driven figure scripts."""

from __future__ import annotations

import csv
from pathlib import Path
from typing import Any


def _coerce_number(value: str) -> float | str:
    try:
        return float(value)
    except (TypeError, ValueError):
        return value


def load_mapped_data(csv_path: str | Path, column_map: dict[str, Any]) -> dict[str, Any]:
    """Load CSV data according to semantic COLUMN_MAP roles."""

    with Path(csv_path).open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))

    result: dict[str, Any] = {}
    for role, spec in column_map.items():
        if not isinstance(spec, dict):
            continue
        if "value" in spec:
            result[role] = spec["value"]
            continue
        column = spec.get("column")
        if not column:
            continue
        result[role] = [_coerce_number(row.get(column, "")) for row in rows]

    series = column_map.get("series")
    if isinstance(series, list):
        result["series"] = []
        for item in series:
            if not isinstance(item, dict):
                continue
            column = item.get("column")
            if not column:
                continue
            entry = {
                "key": item.get("key", column),
                "values": [_coerce_number(row.get(column, "")) for row in rows],
            }
            error_column = item.get("error")
            if error_column:
                entry["errors"] = [_coerce_number(row.get(error_column, "")) for row in rows]
            result["series"].append(entry)

    return result
