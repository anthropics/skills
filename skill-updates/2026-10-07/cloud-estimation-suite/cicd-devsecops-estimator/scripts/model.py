"""Typed, validated input shared by every estimation domain."""

from dataclasses import dataclass, fields
import json
import math
from pathlib import Path
from typing import Any, Mapping

CONTRACT = json.loads(Path(__file__).with_name("workbook-contract.json").read_text(encoding="utf-8"))
SCENARIOS = tuple(CONTRACT["scenario_names"])


@dataclass(frozen=True)
class Task:
    id: str
    lot: str
    domain: str
    task: str
    deliverable: str
    environment: str
    role: str
    prerequisites: str
    dependencies: tuple[str, ...]
    acceptance_criterion: str
    expected_evidence: str
    jh_low: float
    jh_likely: float
    jh_high: float
    scenario_override: str | None
    nature: str
    coverage: str
    source: str
    confidence: str
    notes: str


@dataclass(frozen=True)
class CloudCost:
    id: str
    provider: str
    service: str
    environment: str
    scenario: str
    unit: str
    quantity: float
    unit_price: float
    currency: str
    monthly_multiplier: float
    source: str
    confidence: str
    notes: str


@dataclass(frozen=True)
class Scenario:
    name: str
    description: str
    notes: str


@dataclass(frozen=True)
class EstimateModel:
    metadata: Mapping[str, Any]
    assumptions: tuple[Mapping[str, Any], ...]
    inventory: tuple[Mapping[str, Any], ...]
    architecture: tuple[Mapping[str, Any], ...]
    tasks: tuple[Task, ...]
    cloud_costs: tuple[CloudCost, ...]
    scenarios: tuple[Scenario, ...]
    phasing: tuple[Mapping[str, Any], ...]
    risks: tuple[Mapping[str, Any], ...]
    decisions: tuple[Mapping[str, Any], ...]
    sources: tuple[Mapping[str, Any], ...]


ROW_KEYS = {
    "assumptions": ("key", "value", "unit", "status", "source", "notes"),
    "inventory": ("id", "component", "environment", "quantity", "unit", "notes"),
    "architecture": ("id", "component", "type", "environment", "provider", "decision", "notes"),
    "phasing": ("phase", "sequence", "milestone", "notes"),
    "risks": ("id", "risk", "impact", "probability", "mitigation", "owner", "status"),
    "decisions": ("id", "question", "option", "rationale", "status", "source"),
    "sources": ("id", "title", "type", "date", "url", "notes"),
}


def _required(data: Mapping, keys: tuple[str, ...], location: str) -> None:
    if not isinstance(data, dict):
        raise ValueError(f"{location}: expected an object")
    missing = set(keys) - data.keys()
    if missing:
        raise ValueError(f"{location}: missing {', '.join(sorted(missing))}")


def _number(value: Any, location: str) -> None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value < 0:
        raise ValueError(f"{location}: expected a finite non-negative number")


def _records(data: dict, section: str, cls: type) -> tuple:
    result = []
    keys = tuple(field.name for field in fields(cls))
    for index, row in enumerate(data[section]):
        _required(row, keys, f"{section}[{index}]")
        values = {key: row[key] for key in keys}
        for field in fields(cls):
            if field.type is str and not isinstance(values[field.name], str):
                raise ValueError(f"{section}[{index}].{field.name}: expected text")
        if cls is Task:
            for key in ("jh_low", "jh_likely", "jh_high"):
                _number(values[key], f"{section}[{index}].{key}")
            if not values["jh_low"] <= values["jh_likely"] <= values["jh_high"]:
                raise ValueError(f"{section}[{index}]: require jh_low <= jh_likely <= jh_high")
            if values["scenario_override"] not in (*SCENARIOS, None, ""):
                raise ValueError(f"{section}[{index}].scenario_override: unknown scenario")
            if not isinstance(values["dependencies"], list) or not all(isinstance(item, str) for item in values["dependencies"]):
                raise ValueError(f"{section}[{index}].dependencies: expected a list of task IDs")
            values["dependencies"] = tuple(values["dependencies"])
            if values["nature"] not in ("Build", "Run"):
                raise ValueError(f"{section}[{index}].nature: expected Build or Run")
        if cls is CloudCost:
            for key in ("quantity", "unit_price", "monthly_multiplier"):
                _number(values[key], f"{section}[{index}].{key}")
            if values["scenario"] not in SCENARIOS:
                raise ValueError(f"{section}[{index}].scenario: unknown scenario")
        if cls is Scenario and values["name"] not in SCENARIOS:
            raise ValueError(f"{section}[{index}].name: unknown scenario")
        result.append(cls(**values))
    return tuple(result)


def load_model(path: Path) -> EstimateModel:
    """Load a synthetic or anonymised brief; reject incomplete numeric inputs."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    sections = tuple(field.name for field in fields(EstimateModel))
    _required(data, sections, "estimate")
    _required(data["metadata"], ("title", "date", "currency", "effort_unit", "notes"), "metadata")
    if data["metadata"]["effort_unit"] != "JH":
        raise ValueError("metadata.effort_unit: expected JH")
    for section in sections[1:]:
        if not isinstance(data[section], list):
            raise ValueError(f"{section}: expected a list")
    for section, keys in ROW_KEYS.items():
        for index, row in enumerate(data[section]):
            _required(row, keys, f"{section}[{index}]")
    tasks = _records(data, "tasks", Task)
    ids = [task.id for task in tasks]
    if len(set(ids)) != len(ids):
        raise ValueError("tasks: duplicate ID")
    for task in tasks:
        if any(dependency not in ids or dependency == task.id for dependency in task.dependencies):
            raise ValueError(f"tasks.{task.id}.dependencies: unknown or self-referencing task")
    pending = {task.id: set(task.dependencies) for task in tasks}
    while pending:
        ready = {key for key, dependencies in pending.items() if not dependencies}
        if not ready:
            raise ValueError("tasks.dependencies: cycle detected")
        pending = {key: dependencies - ready for key, dependencies in pending.items() if key not in ready}
    scenarios = _records(data, "scenarios", Scenario)
    if sorted(item.name for item in scenarios) != sorted(SCENARIOS):
        raise ValueError("scenarios.name: require each contract scenario exactly once")
    assumptions = {row["key"]: row["value"] for row in data["assumptions"]}
    _required(assumptions, ("scenario_global", "taux_journalier", "mois_par_an"), "assumptions")
    if len(assumptions) != len(data["assumptions"]):
        raise ValueError("assumptions.key: duplicate key")
    if assumptions["scenario_global"] not in SCENARIOS:
        raise ValueError("assumptions.scenario_global: unknown scenario")
    if "comparison_scenario" in assumptions and assumptions["comparison_scenario"] not in SCENARIOS:
        raise ValueError("assumptions.comparison_scenario: unknown scenario")
    for key in ("taux_journalier", "mois_par_an"):
        if key == "taux_journalier" and assumptions[key] in (None, "A chiffrer"):
            continue  # Unknown is not a zero price; only financial dependencies stop.
        _number(assumptions[key], f"assumptions.{key}")
    costs = _records(data, "cloud_costs", CloudCost)
    if any(cost.currency != data["metadata"]["currency"] for cost in costs):
        raise ValueError("cloud_costs.currency: mixed currencies require prior normalisation")
    return EstimateModel(metadata=dict(data["metadata"]), tasks=tasks, cloud_costs=costs, scenarios=scenarios,
                         **{section: tuple(dict(row) for row in data[section]) for section in ROW_KEYS})
