"""
Shared helpers for render_plan.py and render_dashboard.py.

Keeping these in one place ensures the two render scripts stay in lockstep
(e.g. status labels, hierarchical ordering, and template substitution behave
identically for both generated artifacts).
"""
import json
import re


STATUS_LABELS = {
    "locked": "Locked",
    "available": "Available",
    "in-progress": "In Progress",
    "completed": "Completed",
}

PLACEHOLDER_RE = re.compile(r"\{\{(\w+)\}\}")


def load_json(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def read_file(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def extract_section(text, name):
    start_marker = f"<!-- {name} -->"
    end_marker = f"<!-- END:{name} -->"
    start = text.index(start_marker) + len(start_marker)
    end = text.index(end_marker)
    return text[start:end].strip("\n")


def fill(template, values):
    def repl(m):
        key = m.group(1)
        if key not in values:
            raise KeyError(f"Missing template value for placeholder '{{{{{key}}}}}'")
        return str(values[key])

    return PLACEHOLDER_RE.sub(repl, template)


def ordered_modules(modules):
    """[(module, depth), ...] in hierarchical order: each top-level module
    (parent_id=null) followed by its submodules, recursively, preserving
    JSON order within each parent group."""
    children = {}
    for m in modules:
        children.setdefault(m.get("parent_id"), []).append(m)

    result = []

    def visit(parent_id, depth):
        for m in children.get(parent_id, []):
            result.append((m, depth))
            visit(m["id"], depth + 1)

    visit(None, 0)
    return result
