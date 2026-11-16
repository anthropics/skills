"""Validate the suite's capacity input contract using only the standard library.

This is the bounded numeric subset declared by domain-contract.json, not a
general JSON Schema implementation. Quantities must already use canonical units.
"""

import json
import math
from pathlib import Path


def validate_capacity_inputs(values):
    """Return a copy of nine validated quantities; reject unknown or unsafe inputs."""
    path = Path(__file__).resolve().parents[1] / "references/domain-contract.json"
    schema = json.loads(path.read_text(encoding="utf-8"))["capacity_inputs"]
    if not isinstance(values, dict):
        raise ValueError("capacity_inputs: expected an object")
    missing = set(schema["required"]) - values.keys()
    if missing:
        raise ValueError(f"capacity_inputs: missing {', '.join(sorted(missing))}")
    unknown = values.keys() - schema["properties"].keys()
    if unknown:
        raise ValueError(f"capacity_inputs: undeclared {', '.join(sorted(unknown))}")
    for field, rules in schema["properties"].items():
        value = values[field]
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ValueError(f"{field}: expected numeric {rules['unit']}")
        if rules["type"] == "integer" and not isinstance(value, int):
            raise ValueError(f"{field}: expected integer {rules['unit']}")
        try:
            finite = math.isfinite(value)
        except OverflowError:
            finite = False
        if not finite:
            raise ValueError(f"{field}: expected finite {rules['unit']}")
        if "minimum" in rules and value < rules["minimum"]:
            raise ValueError(f"{field}: below minimum {rules['minimum']}")
        if "exclusiveMinimum" in rules and value <= rules["exclusiveMinimum"]:
            raise ValueError(f"{field}: must exceed {rules['exclusiveMinimum']}")
        if "maximum" in rules and value > rules["maximum"]:
            raise ValueError(f"{field}: exceeds maximum {rules['maximum']}")
    if values["failure_domain_reserve"] >= values["scaling_limit"]:
        raise ValueError("failure_domain_reserve: must be below scaling_limit")
    return dict(values)
