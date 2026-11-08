#!/usr/bin/env python3
"""
Validate a learning-plan.json file.

Usage:
    python3 validate_plan.py <path-to-learning-plan.json> [--schema <path-to-schema.json>]

What this checks:
  1. The file is valid JSON.
  2. Structural validation against learning-plan.schema.json -- required fields,
     types, and enum values. This is a small hand-rolled validator covering the
     subset of JSON Schema used by that schema (type, enum, required, properties,
     items, $ref/$defs), so no third-party 'jsonschema' dependency is required.
  3. All module IDs are unique.
  4. Every parent_id and prerequisite reference points to an existing module ID.
  5. The prerequisites graph has no cycles.
  6. The parent_id hierarchy has no cycles.
  7. (Warnings only) Content fields that are present but empty, which usually
     indicates a module was scaffolded but not fully written.

Exit code 0 if there are no errors (warnings may still be printed).
Exit code 1 if any errors are found.
"""
import argparse
import json
import os
import sys


CONTENT_ARRAY_FIELDS = [
    "learning_objectives",
    "deep_understanding_concepts",
    "common_mistakes",
    "mastery_goals",
    "evaluation",
    "real_world_competence",
    "resources",
]


def load_json(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def resolve_ref(ref, root_schema):
    assert ref.startswith("#/"), f"Unsupported $ref: {ref}"
    node = root_schema
    for part in ref[2:].split("/"):
        node = node[part]
    return node


def check_type(value, expected):
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "null":
        return value is None
    if expected == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if expected == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    return True


def validate_node(value, schema, root_schema, path, errors):
    if "$ref" in schema:
        schema = resolve_ref(schema["$ref"], root_schema)

    expected_type = schema.get("type")
    if expected_type is not None:
        types = expected_type if isinstance(expected_type, list) else [expected_type]
        if not any(check_type(value, t) for t in types):
            errors.append(f"{path}: expected type {types}, got {type(value).__name__} ({value!r})")
            return

    if "enum" in schema and value not in schema["enum"]:
        errors.append(f"{path}: value {value!r} is not one of {schema['enum']}")

    types = expected_type if isinstance(expected_type, list) else [expected_type]

    if "object" in types and isinstance(value, dict):
        for required_field in schema.get("required", []):
            if required_field not in value:
                errors.append(f"{path}: missing required field '{required_field}'")
        for key, subschema in schema.get("properties", {}).items():
            if key in value:
                validate_node(value[key], subschema, root_schema, f"{path}.{key}", errors)

    if "array" in types and isinstance(value, list):
        item_schema = schema.get("items")
        if item_schema:
            for i, item in enumerate(value):
                validate_node(item, item_schema, root_schema, f"{path}[{i}]", errors)


def find_cycle(by_id, edges_fn):
    """Return a list of IDs forming a cycle (first found), or None."""
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {mid: WHITE for mid in by_id}
    stack = []

    def dfs(mid):
        color[mid] = GRAY
        stack.append(mid)
        for nxt in edges_fn(by_id[mid]):
            if nxt not in by_id:
                continue  # dangling references are reported separately
            if color[nxt] == GRAY:
                idx = stack.index(nxt)
                return stack[idx:] + [nxt]
            if color[nxt] == WHITE:
                result = dfs(nxt)
                if result:
                    return result
        stack.pop()
        color[mid] = BLACK
        return None

    for mid in by_id:
        if color[mid] == WHITE:
            result = dfs(mid)
            if result:
                return result
    return None


def check_graph(data, errors):
    if not isinstance(data, dict):
        return
    modules = data.get("modules", [])
    if not isinstance(modules, list):
        return
    modules = [m for m in modules if isinstance(m, dict)]

    seen = set()
    for m in modules:
        mid = m.get("id")
        if mid is None:
            continue
        if mid in seen:
            errors.append(f"Duplicate module id: '{mid}'")
        seen.add(mid)

    by_id = {m["id"]: m for m in modules if "id" in m}
    id_set = set(by_id)

    for m in modules:
        mid = m.get("id", "<missing id>")
        parent = m.get("parent_id")
        if parent is not None and parent not in id_set:
            errors.append(f"Module '{mid}': parent_id '{parent}' does not refer to an existing module")
        for prereq in m.get("prerequisites", []) or []:
            if prereq not in id_set:
                errors.append(f"Module '{mid}': prerequisite '{prereq}' does not refer to an existing module")

    cycle = find_cycle(by_id, lambda m: m.get("prerequisites", []) or [])
    if cycle:
        errors.append("Cycle detected in prerequisites graph: " + " -> ".join(cycle))

    cycle = find_cycle(by_id, lambda m: [m["parent_id"]] if m.get("parent_id") else [])
    if cycle:
        errors.append("Cycle detected in parent_id hierarchy: " + " -> ".join(cycle))


def check_completeness(data, warnings):
    if not isinstance(data, dict):
        return
    modules = data.get("modules", [])
    if not isinstance(modules, list):
        return
    for m in modules:
        if not isinstance(m, dict):
            continue
        mid = m.get("id", "<missing id>")
        for field in CONTENT_ARRAY_FIELDS:
            value = m.get(field)
            if isinstance(value, list) and len(value) == 0:
                warnings.append(f"Module '{mid}': '{field}' is empty -- confirm this is intentional")
        if isinstance(m.get("expected_competence"), str) and m["expected_competence"].strip() == "":
            warnings.append(f"Module '{mid}': 'expected_competence' is empty")


def main():
    parser = argparse.ArgumentParser(description="Validate a learning-plan.json file.")
    parser.add_argument("plan", help="Path to learning-plan.json")
    default_schema = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "references", "learning-plan.schema.json"
    )
    parser.add_argument("--schema", default=default_schema, help="Path to learning-plan.schema.json")
    args = parser.parse_args()

    try:
        data = load_json(args.plan)
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: could not read/parse '{args.plan}': {e}")
        sys.exit(1)

    try:
        schema = load_json(args.schema)
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: could not read/parse schema '{args.schema}': {e}")
        sys.exit(1)

    errors = []
    warnings = []

    validate_node(data, schema, schema, "$", errors)
    # Graph and completeness checks are defensive against malformed input,
    # so they run regardless of schema errors -- this surfaces as many
    # issues as possible in a single pass.
    check_graph(data, errors)
    check_completeness(data, warnings)

    print(f"Validating {args.plan}")
    print(f"Schema:    {args.schema}\n")

    if errors:
        print(f"ERRORS ({len(errors)}):")
        for e in errors:
            print(f"  - {e}")
        print()

    if warnings:
        print(f"WARNINGS ({len(warnings)}):")
        for w in warnings:
            print(f"  - {w}")
        print()

    if not errors and not warnings:
        print("No errors or warnings. Plan is structurally valid and complete.")

    if errors:
        print("RESULT: FAIL")
        sys.exit(1)
    else:
        print("RESULT: PASS")
        sys.exit(0)


if __name__ == "__main__":
    main()
