"""Mechanical packaging checks only; these do not prove agent behavior."""

from dataclasses import fields
import importlib.util
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
    ("kubernetes-architect", {"node-pool": "inventory", "platform-task": "tasks", "risk": "risks", "recurring-operation": "tasks"}),
    ("hosting-capacity-simulator", {"sizing-input": "assumptions", "capacity-result": "assumptions", "measurement-task": "tasks", "scenario": "scenarios", "risk": "risks"}),
    ("cicd-devsecops-estimator", {"pipeline-task": "tasks", "recurring-operation": "tasks", "risk": "risks", "source": "sources"}),
    ("server-hardening-estimator", {"control-task": "tasks", "recurring-operation": "tasks", "residual-risk": "risks", "source": "sources"}),
    ("cloud-provider-selector", {"comparison-input": "assumptions", "provider-decision": "decisions", "implementation-task": "tasks", "recurring-operation": "tasks", "cloud-cost": "cloud_costs", "risk": "risks", "source": "sources"}),
    ("finops-optimizer", {"opportunity": "decisions", "baseline": "assumptions", "implementation-task": "tasks", "recurring-operation": "tasks", "cloud-cost": "cloud_costs", "risk": "risks", "source": "sources"}),
    ("cloud-migration-estimator", {"inventory": "inventory", "source-write-policy": "assumptions", "documentation-drift": "decisions", "service-mapping": "architecture", "migration-task": "tasks", "recurring-operation": "tasks", "risk": "risks", "source": "sources"}),
    ("cloud-architecture-diagrammer", {"inventory": "inventory", "topology-node": "architecture", "flow-evidence": "sources", "topology-issue": "risks", "diagram-task": "tasks"}),
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


@pytest.mark.parametrize("name,expected_fields", [
    ("cicd-devsecops-estimator", {
        "pipeline_stage": {"record": "pipeline-task", "keys": ["notes"]},
        "evidence": {"record": "pipeline-task", "keys": ["expected_evidence"]},
        "one_off_jh": {"record": "pipeline-task", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "recurring_jh": {"record": "recurring-operation", "keys": ["jh_low", "jh_likely", "jh_high"]},
    }),
    ("server-hardening-estimator", {
        "control_boundary": {"record": "control-task", "keys": ["notes"]},
        "implementation_task": {"record": "control-task", "keys": ["task"]},
        "verification_evidence": {"record": "control-task", "keys": ["expected_evidence"]},
        "one_off_jh": {"record": "control-task", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "recurring_jh": {"record": "recurring-operation", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "residual_risk": {"record": "residual-risk", "keys": ["risk", "mitigation", "owner", "status"]},
    }),
])
def test_delivery_and_hardening_fields_preserve_evidence_and_effort_nature(name, expected_fields):
    # Dropping evidence, confusing Build/Run, or pointing to nonexistent fields
    # breaks the emitted domain interface, independent of instruction wording.
    path = ROOT / name / "references/domain-contract.json"
    assert path.is_file(), f"Missing domain contract: {path}"
    contract = json.loads(path.read_text(encoding="utf-8"))
    assert contract["domain_fields"] == expected_fields
    outputs = contract["outputs"]
    for binding in contract["domain_fields"].values():
        assert binding["record"] in outputs
        assert binding["keys"] and set(binding["keys"]) <= set(outputs[binding["record"]]["required_keys"])
    build_record = contract["domain_fields"]["one_off_jh"]["record"]
    assert outputs[build_record]["constraints"] == {"nature": "Build"}
    assert outputs["recurring-operation"]["constraints"] == {"nature": "Run", "period": "month"}
    assert "expected_evidence" in outputs["recurring-operation"]["required_keys"]


def validate_capacity(values):
    # Missing fields, weakened numeric types or dropped bounds break the interface.
    path = ROOT / "hosting-capacity-simulator/references/domain-contract.json"
    assert path.is_file(), f"Missing domain contract: {path}"
    schema = json.loads(path.read_text(encoding="utf-8"))["capacity_inputs"]
    expected_units = {
        "cpu": "vCPU", "memory": "GiB", "storage": "GiB", "iops": "operations/s",
        "bandwidth": "Mbit/s", "concurrency": "requests", "utilisation_target": "ratio",
        "scaling_limit": "instances", "failure_domain_reserve": "instances",
    }
    assert set(schema["required"]) == set(expected_units)
    assert set(schema["properties"]) == set(expected_units)
    assert {key: value["unit"] for key, value in schema["properties"].items()} == expected_units
    script = ROOT / "hosting-capacity-simulator/scripts/validate_capacity.py"
    assert script.is_file(), f"Missing capacity validator: {script}"
    spec = importlib.util.spec_from_file_location("capacity_validator", script)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.validate_capacity_inputs(values)


@pytest.fixture
def capacity_validator():
    return validate_capacity


@pytest.fixture
def measured_capacity():
    # Synthetic simultaneous peak; no client data or prices.
    return {
        "cpu": 12.5, "memory": 24.0, "storage": 512.0, "iops": 2500,
        "bandwidth": 200.0, "concurrency": 80, "utilisation_target": 0.7,
        "scaling_limit": 12, "failure_domain_reserve": 1,
    }


def test_capacity_contract_accepts_measured_peaks(capacity_validator, measured_capacity):
    assert capacity_validator(measured_capacity) == measured_capacity


@pytest.mark.parametrize("field", [
    "cpu", "memory", "storage", "iops", "bandwidth", "concurrency",
    "utilisation_target", "scaling_limit", "failure_domain_reserve",
])
def test_capacity_contract_rejects_missing_dimension(capacity_validator, measured_capacity, field):
    del measured_capacity[field]
    with pytest.raises(ValueError, match=field):
        capacity_validator(measured_capacity)


@pytest.mark.parametrize("field,value", [
    ("cpu", "12 vCPU"), ("cpu", True), ("memory", -1), ("storage", None),
    ("iops", -1), ("bandwidth", "200 Mbps"), ("concurrency", 1.5),
    ("utilisation_target", 0), ("utilisation_target", 1.01),
    ("scaling_limit", 0), ("scaling_limit", 2.5),
    ("failure_domain_reserve", -1), ("failure_domain_reserve", 0.5),
])
def test_capacity_contract_rejects_invalid_quantity(capacity_validator, measured_capacity, field, value):
    measured_capacity[field] = value
    with pytest.raises(ValueError, match=field):
        capacity_validator(measured_capacity)


def test_capacity_contract_accepts_explicit_zero_demand_and_no_reserve(capacity_validator, measured_capacity):
    for field in ("cpu", "memory", "storage", "iops", "bandwidth", "concurrency", "failure_domain_reserve"):
        measured_capacity[field] = 0
    measured_capacity["utilisation_target"] = 1
    measured_capacity["scaling_limit"] = 1
    assert capacity_validator(measured_capacity) == measured_capacity


@pytest.mark.parametrize("field,value", [("cpu", float("nan")), ("memory", float("inf")), ("failure_domain_reserve", 12)])
def test_capacity_contract_rejects_nonfinite_or_exhausted_reserve(capacity_validator, measured_capacity, field, value):
    measured_capacity[field] = value
    with pytest.raises(ValueError, match=field):
        capacity_validator(measured_capacity)


def test_capacity_contract_rejects_undeclared_unit_field(capacity_validator, measured_capacity):
    measured_capacity["cpu_millicores"] = 1000
    with pytest.raises(ValueError, match="cpu_millicores"):
        capacity_validator(measured_capacity)


@pytest.mark.parametrize("name,schema_key,expected_bindings", [
    ("cloud-provider-selector", "comparison_inputs", {
        "region_eligibility": {"record": "comparison-input", "keys": ["value", "source", "notes"]},
        "service_scope": {"record": "comparison-input", "keys": ["value", "notes"]},
        "commercial_policy": {"record": "comparison-input", "keys": ["value", "source", "notes"]},
        "weighted_criteria": {"record": "comparison-input", "keys": ["value", "source", "notes"]},
        "implementation_jh": {"record": "implementation-task", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "recurring_jh": {"record": "recurring-operation", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "tco_horizon_years": {"record": "comparison-input", "keys": ["value", "unit"]},
    }),
    ("finops-optimizer", "opportunity_fields", {
        "baseline": {"record": "baseline", "keys": ["value", "unit", "status", "source", "notes"]},
        "action": {"record": "opportunity", "keys": ["option"]},
        "savings_range": {"record": "opportunity", "keys": ["rationale"]},
        "one_off_jh": {"record": "implementation-task", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "recurring_jh": {"record": "recurring-operation", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "risk": {"record": "risk", "keys": ["risk", "mitigation", "owner", "status"]},
        "reversibility": {"record": "opportunity", "keys": ["rationale"]},
        "validation_method": {"record": "implementation-task", "keys": ["acceptance_criterion", "expected_evidence"]},
    }),
])
def test_provider_and_finops_contracts_require_decision_inputs(name, schema_key, expected_bindings):
    # Omitting a savings dimension, effort nature, or region/scope input breaks
    # the domain interchange interface; no prose or recommendation is tested.
    path = ROOT / name / "references/domain-contract.json"
    assert path.is_file(), f"Missing domain contract: {path}"
    contract = json.loads(path.read_text(encoding="utf-8"))
    schema = contract[schema_key]
    assert set(schema["required"]) == set(expected_bindings)
    assert len(schema["required"]) == len(set(schema["required"]))
    assert schema["bindings"] == expected_bindings
    for binding in schema["bindings"].values():
        output = contract["outputs"][binding["record"]]
        assert set(binding["keys"]) <= set(output["required_keys"])
    assert contract["outputs"]["implementation-task"]["constraints"] == {"nature": "Build"}
    assert contract["outputs"]["recurring-operation"]["constraints"] == {"nature": "Run", "period": "month"}
    if name == "cloud-provider-selector":
        assert schema["constraints"]["tco_horizon_years"] == 3
        assert schema["constraints"]["region_eligibility"] == {
            "count_eligible_regions": True, "multi_region_dr_minimum": 2,
        }
        assert schema["constraints"]["service_scope"] == "equal"
    else:
        assert schema["constraints"]["baseline_kind"] == ["measured-billing", "forecast"]
        assert schema["constraints"]["savings_status"] == ["forecast", "validated-measured"]


def test_migration_contract_preserves_source_constraints_and_complete_lifecycle():
    # Removing a lifecycle field or mapping evidence to a nonexistent common
    # column breaks the domain interface; this makes no claim about agent prose.
    path = ROOT / "cloud-migration-estimator/references/domain-contract.json"
    assert path.is_file(), f"Missing domain contract: {path}"
    contract = json.loads(path.read_text(encoding="utf-8"))
    expected = {
        "inventory_evidence": {"record": "inventory", "keys": ["id", "notes"]},
        "documentation_drift": {"record": "documentation-drift", "keys": ["question", "option", "rationale", "status", "source"]},
        "source_write_policy": {"record": "source-write-policy", "keys": ["value", "status", "source", "notes"]},
        "source_target_mapping": {"record": "service-mapping", "keys": ["id", "component", "decision", "notes"]},
        **{phase: {"record": "migration-task", "keys": ["task", "dependencies", "acceptance_criterion", "expected_evidence", "notes"]}
           for phase in ("preparation", "rehearsal", "data_transfer", "cutover", "integrity", "rollback", "decommissioning", "hypercare")},
        "one_off_jh": {"record": "migration-task", "keys": ["jh_low", "jh_likely", "jh_high"]},
        "recurring_jh": {"record": "recurring-operation", "keys": ["jh_low", "jh_likely", "jh_high"]},
    }
    schema = contract["migration_fields"]
    assert set(schema["required"]) == set(expected)
    assert len(schema["required"]) == len(set(schema["required"]))
    assert schema["bindings"] == expected
    for binding in schema["bindings"].values():
        assert set(binding["keys"]) <= set(contract["outputs"][binding["record"]]["required_keys"])
    assert schema["constraints"]["source_write_policy"] == ["forbidden", "owner-only", "scoped-authorised", "unknown"]
    assert schema["constraints"]["inventory_method"] == "read-only-live-first"
    assert contract["outputs"]["migration-task"]["constraints"] == {"nature": "Build"}
    assert contract["outputs"]["recurring-operation"]["constraints"] == {"nature": "Run", "period": "month"}


def test_diagram_contract_uses_shared_graph_and_icon_provenance_interfaces():
    # A detached graph, lost endpoint identity, missing provenance or a changed
    # render target breaks the interchange contract. Rendering refusal and
    # artifact embedding are exercised by the canonical renderer tests.
    path = ROOT / "cloud-architecture-diagrammer/references/domain-contract.json"
    assert path.is_file(), f"Missing domain contract: {path}"
    contract = json.loads(path.read_text(encoding="utf-8"))
    schema = contract["diagram_fields"]
    assert set(schema["required"]) == {"inventory_node_ids", "nodes", "edges", "icon_provenance", "artifacts", "topology_verification"}
    assert schema["nodes"] == {"required_keys": ["id", "component", "environment", "zone", "provider", "icon"], "id_reference": "inventory.id", "coverage": "exact"}
    assert schema["edges"] == {"required_keys": ["id", "source", "target", "label"], "endpoint_reference": "nodes.id", "evidence_reference": "sources.id", "infer_connections": False}
    assert schema["topology_verification"] == {"before": "estimate-finalisation", "reject": ["duplicate-node-id", "duplicate-edge-id", "node-absent-from-inventory", "missing-inventory-node", "dangling-flow"], "unresolved_flow": "risk-or-assumption"}
    policy = json.loads((ROOT / "tooling/icon-policy.json").read_text(encoding="utf-8"))
    assert schema["icon_provenance"]["default"] == policy["default"]
    assert schema["icon_provenance"]["asset_formats"] == policy["asset_formats"]
    assert set(schema["icon_provenance"]["required_keys"]) == {"path", "sha256", "provider", "official_source_url", "licence_or_trademark_notice"}
    assert schema["artifacts"] == {"exports": ["SVG", "PNG"], "primary": "XLSX", "embed": {"sheet": "03_Architecture", "format": "PNG"}, "manifest_keys": ["node_ids", "edge_ids", "icon_sources", "icon_provenance", "output_hashes", "warnings"]}
