import json
from pathlib import Path

ROOT = Path(__file__).parents[1]


def test_contract_has_stable_workbook_shape():
    data = json.loads((ROOT / "tooling/workbook-contract.json").read_text(encoding="utf-8"))
    assert data["sheets"] == [
        "00_Lisez-moi", "01_Hypotheses", "02_Inventaire", "03_Architecture",
        "04_Taches_JH", "05_Couts_cloud", "06_Scenarios", "07_Phasage",
        "08_Risques", "09_Arbitrages", "10_Sources", "11_Synthese",
    ]
    assert {
        "ID", "Lot", "Domaine", "Tache", "Livrable", "Environnement", "Role",
        "Prerequis", "Dependances", "Critere d'acceptation", "Preuve attendue",
        "JH bas", "JH probable", "JH haut", "JH retenu", "Scenario retenu",
        "Scenario override", "Nature", "Couverture", "Source", "Confiance", "Notes",
    } <= set(data["task_columns"])
    assert len(data["task_columns"]) == len(set(data["task_columns"]))
    assert data["scenario_names"] == ["Economique", "Standard", "Resilient"]
    assert isinstance(data["forbidden_patterns"], list)
    assert data["forbidden_patterns"]


def test_registry_contains_all_public_skills():
    data = json.loads((ROOT / "tooling/domain-registry.json").read_text(encoding="utf-8"))
    assert len(data["skills"]) == 11
    assert {item["name"] for item in data["skills"]} == {
        "cloud-estimation-orchestrator", "infra-work-estimator",
        "cloud-architecture-advisor", "kubernetes-architect",
        "cicd-devsecops-estimator", "server-hardening-estimator",
        "hosting-capacity-simulator", "cloud-provider-selector", "finops-optimizer",
        "cloud-migration-estimator", "cloud-architecture-diagrammer",
    }
    contract = json.loads((ROOT / "tooling/workbook-contract.json").read_text(encoding="utf-8"))
    for item in data["skills"]:
        assert item["domain"]
        assert item["triggers"]
        assert item["required_workbook_sections"] == contract["sheets"]
