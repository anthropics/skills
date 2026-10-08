"""Mechanical packaging checks only; these do not prove agent behavior."""

from dataclasses import fields
import json
from pathlib import Path
import re
from types import SimpleNamespace

import pytest
import yaml

from tooling.model import CloudCost, EstimateModel, ROW_KEYS, Scenario, Task

ROOT = Path(__file__).parents[1]
RESOURCE = re.compile(r"(?:\]\(|`)((?:references|scripts|assets)/[^\s)`#]+)")
SCAFFOLD = re.compile(r"\b(?:TODO|TBD|FIXME)\b|\[INSERT[^\]]*\]", re.I)


def inspect_skill(directory):
    entrypoint = directory / "SKILL.md"
    assert entrypoint.is_file(), f"Missing skill entrypoint: {entrypoint}"
    raw = entrypoint.read_bytes()
    assert b"\r" not in raw, f"Skill frontmatter must use LF: {entrypoint}"
    text = raw.decode("utf-8")
    header = re.match(r"\A---\n(.*?)\n---(?:\n|\Z)", text, re.S)
    assert header, f"Invalid frontmatter delimiters: {entrypoint}"
    frontmatter = yaml.safe_load(header.group(1))
    assert isinstance(frontmatter, dict), f"Expected frontmatter mapping: {entrypoint}"
    assert isinstance(frontmatter.get("name"), str)
    assert isinstance(frontmatter.get("description"), str)
    assert re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", frontmatter["name"])
    assert len(frontmatter["name"]) < 64
    missing = {"references": [], "scripts": [], "assets": []}
    scaffold = []
    inspected = set()
    pending = [entrypoint]
    while pending:
        document = pending.pop()
        if document in inspected:
            continue
        inspected.add(document)
        content = document.read_text(encoding="utf-8")
        scaffold.extend(f"{document.name}:{match.group(0)}" for match in SCAFFOLD.finditer(content))
        for relative in RESOURCE.findall(content):
            target = (directory / relative).resolve()
            assert target.is_relative_to(directory.resolve()), f"Escaping resource path: {relative}"
            if not target.is_file():
                missing[relative.split("/", 1)[0]].append(relative)
            elif target.suffix == ".md":
                pending.append(target)
    return SimpleNamespace(
        frontmatter=frontmatter,
        unfinished_scaffold_markers=scaffold,
        missing_references=missing["references"],
        missing_scripts=missing["scripts"],
        missing_assets=missing["assets"],
    )


@pytest.fixture
def load_skill():
    return lambda name: inspect_skill(ROOT / name)


def test_orchestrator_has_required_enforcement(load_skill):
    # A missing entrypoint, invalid frontmatter or dangling resource fails here.
    # Decision quality and enforcement need an independent forward-test.
    skill = load_skill("cloud-estimation-orchestrator")
    assert skill.frontmatter["name"] == "cloud-estimation-orchestrator"
    assert skill.frontmatter["description"].strip()
    assert skill.unfinished_scaffold_markers == []
    assert skill.missing_references == []
    assert skill.missing_scripts == []
    assert skill.missing_assets == []


@pytest.mark.parametrize("name,required_outputs", [
    ("infra-work-estimator", {"task": "tasks", "inventory": "inventory", "risk": "risks", "source": "sources"}),
    ("cloud-architecture-advisor", {"option": "architecture", "decision": "decisions", "risk": "risks", "cost-driver": "assumptions"}),
])
def test_domain_contract_maps_records_to_common_model(name, required_outputs, load_skill):
    # Removing a required record or emitting a nonexistent field must fail.
    # This checks the interchange contract, never the agent's prose decisions.
    skill = load_skill(name)
    assert skill.frontmatter["name"] == name
    assert skill.frontmatter["description"].strip()
    assert skill.unfinished_scaffold_markers == []
    assert skill.missing_references == []
    assert skill.missing_scripts == []
    assert skill.missing_assets == []
    path = ROOT / name / "references/domain-contract.json"
    assert path.is_file(), f"Missing domain contract: {path}"
    contract = json.loads(path.read_text(encoding="utf-8"))
    assert contract["skill"] == name
    assert contract["model"] == "EstimateModel"
    assert contract["effort_unit"] == "JH"
    model_sections = {field.name for field in fields(EstimateModel)}
    assert contract["inputs"] and set(contract["inputs"]) <= model_sections
    assert len(contract["inputs"]) == len(set(contract["inputs"]))
    expected_keys = {**ROW_KEYS, **{
        section: tuple(field.name for field in fields(record))
        for section, record in (("tasks", Task), ("cloud_costs", CloudCost), ("scenarios", Scenario))
    }}
    expected_sheets = dict(zip(
        ("metadata", "assumptions", "inventory", "architecture", "tasks", "cloud_costs", "scenarios", "phasing", "risks", "decisions", "sources"),
        json.loads((ROOT / "tooling/workbook-contract.json").read_text(encoding="utf-8"))["sheets"],
    ))
    assert required_outputs.keys() <= contract["outputs"].keys()
    for record_type, section in required_outputs.items():
        assert contract["outputs"][record_type]["section"] == section
    for record in contract["outputs"].values():
        section = record["section"]
        assert section in expected_keys, f"Unknown output section: {section}"
        assert set(record["required_keys"]) == set(expected_keys[section])
        assert len(record["required_keys"]) == len(set(record["required_keys"]))
        assert record["workbook_sheet"] == expected_sheets[section]
