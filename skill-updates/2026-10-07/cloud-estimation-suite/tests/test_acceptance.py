"""Exercise the shipped synthetic workbook, including cached domain calculations.

Missing caches, a merged provider budget, dropped flows, double-counted tasks,
or lost capacity/FinOps decisions must fail these consumer-facing checks.
"""

from collections import Counter
import json
import shutil
from pathlib import Path
import subprocess
import sys

from openpyxl import load_workbook
from openpyxl.utils.cell import range_boundaries
import pytest

from tooling.anonymisation import scan_tree
from tooling.model import load_model
from tooling.recalculate import FormulaFailure, _EXCEL_RECALCULATE, _run_excel_powershell, recalculate
from tooling.workbook_validator import validate_workbook
from tooling.workbook_builder import build_workbook

ROOT = Path(__file__).parents[1]
EXAMPLES = ROOT / "examples"


@pytest.fixture(scope="module")
def example_report():
    path = EXAMPLES / "synthetic-cloud-estimate.xlsx"
    for name in ("synthetic-cloud-estimate.xlsx", "synthetic-cloud-brief.json",
                 "synthetic-architecture.json", "synthetic-assertions.json"):
        assert (EXAMPLES / name).is_file(), f"Generate the complete public example: missing {name}"
    model = load_model(EXAMPLES / "synthetic-cloud-brief.json")
    formulas = load_workbook(path)
    values = load_workbook(path, data_only=True)
    architecture = json.loads((EXAMPLES / "synthetic-architecture.json").read_text(encoding="utf-8"))
    inventory = [row.id if hasattr(row, "id") else row["id"] for row in model.inventory]
    assertions = json.loads((EXAMPLES / "synthetic-assertions.json").read_text(encoding="utf-8"))
    report = validate_workbook(path, diagram_inventory_ids=inventory, asserted_totals=assertions)
    return model, formulas, values, architecture, report


def test_public_example_meets_suite_success_criteria(example_report):
    assert example_report is not None, "Generate the public synthetic XLSX acceptance example"
    model, formulas, values, architecture, report = example_report
    assert report.ok, report.errors
    assert report.counts["formula_errors"] == 0
    assert report.counts["missing_cached_values"] == 0
    assert report.counts["formula_semantic_errors"] == 0
    assert report.counts["reconciliation_errors"] == 0
    assert report.counts["formulas"] >= 100
    assert report.counts["reconciliations"] >= 100
    assert len(model.scenarios) == 3
    providers = {row.provider for row in model.cloud_costs}
    assert len(providers) == 3
    groups = Counter((row.provider, row.scenario) for row in model.cloud_costs)
    assert len(groups) == 9 and all(count == 3 for count in groups.values())
    assert len({row.id for row in model.tasks}) == len(model.tasks) == 10
    inventory_ids = {row["id"] for row in model.inventory}
    assert len(inventory_ids) == 4
    manifest = next(json.loads(row[1].value) for row in formulas["03_Architecture"]
                    if row[0].value == "JSON")
    assert set(manifest["node_ids"]) == inventory_ids
    assert set(manifest["edge_ids"]) == {row["id"] for row in architecture["edges"]}
    assert len(manifest["edge_ids"]) == 1
    assert manifest["icon_provenance"] == []
    assert len(formulas["03_Architecture"]._images) == 1
    scan = scan_tree(ROOT)
    assert scan.clean, scan.summary()
    assert scan.match_count == 0 and scan.scanned_files > 200


def test_domain_calculations_and_separate_build_run_reconcile(example_report):
    assert example_report is not None, "Generate the public synthetic XLSX acceptance example"
    model, formulas, values, architecture, report = example_report
    assumptions = {row[0].value: row[1] for row in values["01_Hypotheses"] if row[0].value}
    expected = {
        "schedule.foundation_overload": 3,
        "capacity.production.Standard.high.overload_ratio": 2,
        "contradiction.cloud_delta": 45,
        "contradiction.build_delta": 2,
        "contradiction.run_delta": 0.5,
        "finops.savings_low": 22.5,
        "finops.savings_high": 45,
        "finops.savings_selected": 45,
        "tco.ProviderA.Standard": 41906,
    }
    for key, value in expected.items():
        cell = assumptions[key]
        assert cell.value == pytest.approx(value), key
        assert formulas["01_Hypotheses"][cell.coordinate].data_type == "f", key
    assert values["11_Synthese"]["B6"].value == 19
    assert values["11_Synthese"]["B7"].value == 1
    assert values["11_Synthese"]["C6"].value == "JH"
    assert values["11_Synthese"]["C7"].value == "JH/mois"
    assert values["11_Synthese"]["B8"].value == 12350
    assert values["11_Synthese"]["B9"].value == 650
    assert values["11_Synthese"]["B11"].value == 171
    assert values["06_Scenarios"]["D5"].value == 9.5
    assert values["06_Scenarios"]["D6"].value == 17
    assert values["06_Scenarios"]["D7"].value == 30
    assert {row["id"] for row in model.decisions} >= {"DEC-CONFLICT", "DEC-FINOPS", "DEC-ARCH", "DEC-SCHEDULE"}
    assert any(row.domain == "finops" and row.nature == "Build" for row in model.tasks)
    assert any(row.domain == "finops" and row.nature == "Run" for row in model.tasks)


def test_regeneration_runs_real_shared_toolchain(tmp_path):
    script = EXAMPLES / "generate_example.py"
    assert script.is_file(), "Missing executable public example generator"
    result = subprocess.run([sys.executable, str(script), "--output-dir", str(tmp_path)],
                            capture_output=True, text=True, timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr
    evidence = json.loads(result.stdout)
    assert evidence["validation"]["ok"]
    assert evidence["recalculation"]["formula_count"] >= 100
    assert evidence["recalculation"]["cached_values_count"] == evidence["recalculation"]["formula_count"]
    assert evidence["anonymisation_matches"] == 0
    assert not list(tmp_path.glob("estimate-recalc-*")), "Native recalculation left temporary files"
    path = tmp_path / "synthetic-cloud-estimate.xlsx"
    with path.open("rb") as stream:
        assert load_workbook(stream, data_only=True)["11_Synthese"]["B6"].value == 19
    # On Windows these operations fail if any verification reader retains a handle.
    replacement = tmp_path / "replacement.xlsx"
    path.replace(replacement)
    replacement.unlink()
    assert not path.exists() and not replacement.exists()


@pytest.mark.skipif(sys.platform != "win32", reason="Windows PowerShell COM bridge")
def test_windows_com_bridge_rejects_exit_zero_before_completion():
    _run_excel_powershell("Write-Output 'control'")
    with pytest.raises(FormulaFailure, match="PowerShell Excel COM failed"):
        _run_excel_powershell("exit 0")


def test_standard_provider_comparison_separates_effort_cloud_and_three_year_tco(example_report, tmp_path, monkeypatch):
    model, formulas, values, architecture, report = example_report
    ws = formulas["06_Scenarios"]
    assert "ComparaisonFournisseurs" in ws.tables, "Missing three-provider Standard TCO comparison"
    left, header, right, bottom = range_boundaries(ws.tables["ComparaisonFournisseurs"].ref)
    assert [ws.cell(header, column).value for column in range(left, right + 1)] == [
        "Fournisseur", "Build (JH)", "Run humain (JH/mois)", "Cloud (EUR/mois)",
        "Horizon (annees)", "TCO (EUR)",
    ]
    expected = {"Provider A": (19, 1, 171, 3, 41906),
                "Provider B": (19, 1, 186, 3, 42446),
                "Provider C": (19, 1, 201, 3, 42986)}
    found = {}
    for row in range(header + 1, bottom + 1):
        provider = values[ws.title].cell(row, left).value
        found[provider] = tuple(values[ws.title].cell(row, column).value for column in range(left + 1, right + 1))
        assert all(ws.cell(row, column).data_type == "f" for column in range(left + 1, right + 1))
    assert found == expected
    assertions = json.loads((EXAMPLES / "synthetic-assertions.json").read_text(encoding="utf-8"))
    for row in range(header + 1, bottom + 1):
        for column in range(left + 1, right + 1):
            assert assertions[f"{ws.title}!{ws.cell(row, column).coordinate}"] == values[ws.title].cell(row, column).value
    # Reference Standard remains comparable when global selection changes.
    # Independent sensitivity: 19*700 + 24*(700 + cloud) for a two-year horizon.
    with (EXAMPLES / "synthetic-cloud-estimate.xlsx").open("rb") as stream:
        trial = load_workbook(stream)
    assumptions = {row[0].value: row[1].coordinate for row in trial["01_Hypotheses"] if row[0].value}
    for key, value in (("scenario_global", "Economique"), ("taux_journalier", 700), ("tco_horizon_years", 2)):
        trial["01_Hypotheses"][assumptions[key]] = value
    path = tmp_path / "sensitivity.xlsx"
    trial.save(path)
    import tooling.recalculate as adapter
    monkeypatch.setattr(adapter, "_select_excel_backend", lambda: None)
    monkeypatch.setattr(adapter, "_find_libreoffice", lambda: None)
    assert recalculate(path).ok
    with path.open("rb") as stream:
        recalculated = load_workbook(stream, data_only=True)
    expected_tcos = {"Provider A": 34204, "Provider B": 34564, "Provider C": 34924}
    for row in range(header + 1, bottom + 1):
        assert recalculated[ws.title].cell(row, left + 1).value == 19
        assert recalculated[ws.title].cell(row, left + 2).value == 1
        provider = recalculated[ws.title].cell(row, left).value
        assert recalculated[ws.title].cell(row, right).value == expected_tcos[provider]


def test_foundation_overload_compares_collective_capacity_with_all_foundation_roles(example_report):
    model, formulas, values, architecture, report = example_report
    inputs = {row[0].value: row for row in values["01_Hypotheses"] if row[0].value}
    available = inputs["schedule.foundation_available"]
    assert available[1].value == 6
    assert "collective capacity" in available[5].value.lower()
    assert "not per-role capacity" in available[5].value.lower()
    overload = inputs["schedule.foundation_overload"][1]
    assert overload.value == 3
    assert "Taches[Lot]" in formulas["01_Hypotheses"][overload.coordinate].value
    assert "Taches[Role]" not in formulas["01_Hypotheses"][overload.coordinate].value
    foundation = [task for task in model.tasks if task.lot == "Foundation" and task.nature == "Build"]
    assert len({task.role for task in foundation}) == 2
    effort_fields = {"Economique": "jh_low", "Standard": "jh_likely", "Resilient": "jh_high"}
    demand = sum(getattr(task, effort_fields[task.scenario_override or "Standard"]) for task in foundation)
    assert demand == 9 and demand - available[1].value == overload.value


def test_comparison_scenario_has_a_visible_stopping_dropdown(tmp_path):
    model = load_model(EXAMPLES / "synthetic-cloud-brief.json")
    path = build_workbook(model, tmp_path / "dropdown.xlsx")
    with path.open("rb") as stream:
        workbook = load_workbook(stream)
    sheet = workbook["01_Hypotheses"]
    cell = next(row[1] for row in sheet if row[0].value == "comparison_scenario")
    validations = [rule for rule in sheet.data_validations.dataValidation if cell.coordinate in rule]
    assert len(validations) == 1
    rule = validations[0]
    assert rule.type == "list" and rule.formula1 == '"Economique,Standard,Resilient"'
    assert rule.showDropDown is not True
    assert rule.showErrorMessage and rule.errorStyle == "stop" and not rule.allow_blank


def test_model_refuses_misspelled_comparison_scenario(tmp_path):
    data = json.loads((EXAMPLES / "synthetic-cloud-brief.json").read_bytes())
    next(row for row in data["assumptions"] if row["key"] == "comparison_scenario")["value"] = "Standrad"
    path = tmp_path / "misspelled.json"
    path.write_text(json.dumps(data), encoding="utf-8")
    with pytest.raises(ValueError, match="comparison_scenario.*unknown scenario"):
        load_model(path)


@pytest.mark.skipif(sys.platform != "win32", reason="Final public artifact native Excel opening")
def test_final_public_metadata_normalization_remains_native_readable(tmp_path):
    # Reopen the delivered bytes after privacy normalization, not its precursor.
    trial = tmp_path / "final-public-artifact.xlsx"
    shutil.copyfile(EXAMPLES / "synthetic-cloud-estimate.xlsx", trial)
    _run_excel_powershell(_EXCEL_RECALCULATE, trial)


def test_validator_refuses_edited_misspelled_comparison_scenario(tmp_path, monkeypatch):
    with (EXAMPLES / "synthetic-cloud-estimate.xlsx").open("rb") as stream:
        workbook = load_workbook(stream)
    sheet = workbook["01_Hypotheses"]
    cell = next(row[1] for row in sheet if row[0].value == "comparison_scenario")
    cell.value = "Standrad"
    path = tmp_path / "misspelled.xlsx"
    workbook.save(path)
    import tooling.recalculate as adapter
    monkeypatch.setattr(adapter, "_select_excel_backend", lambda: None)
    monkeypatch.setattr(adapter, "_find_libreoffice", lambda: None)
    assert recalculate(path).ok
    report = validate_workbook(path)
    assert not report.ok
    assert any("comparison_scenario" in error and "invalid" in error for error in report.errors)


@pytest.mark.skipif(sys.platform != "win32", reason="Windows PowerShell cleanup contract")
def test_excel_cleanup_attempts_quit_all_releases_and_gc_after_close_and_release_failures():
    # Fake only the external COM boundary; execute the real production PowerShell.
    prefix = r"""
$script:events = [Collections.Generic.List[string]]::new()
$script:fake_book = [pscustomobject]@{Kind='Workbook'}
$script:fake_book | Add-Member ScriptMethod Save { $script:events.Add('SAVE') }
$script:fake_book | Add-Member ScriptMethod Close { param($save) $script:events.Add('CLOSE'); throw 'forced Close failure' }
$script:fake_books = [pscustomobject]@{Kind='Workbooks'}
$script:fake_books | Add-Member ScriptMethod Open { param($path,$links,$readonly) return $script:fake_book }
$script:fake_excel = [pscustomobject]@{Kind='Excel'; Workbooks=$script:fake_books; Visible=$false; DisplayAlerts=$false; AutomationSecurity=3}
$script:fake_excel | Add-Member ScriptMethod CalculateFullRebuild { $script:events.Add('CALCULATE') }
$script:fake_excel | Add-Member ScriptMethod Quit { $script:events.Add('QUIT'); throw 'forced Quit failure' }
function New-Object { param($ComObject) return $script:fake_excel }
function Release-ExcelComObject { param($object) $script:events.Add('RELEASE-'+$object.Kind); throw ('forced release '+$object.Kind) }
function Invoke-ExcelCollection { $script:events.Add('COLLECT'); throw 'forced collection failure' }
function Wait-ExcelFinalizers { $script:events.Add('FINALIZERS') }
$reported = ''
try {
"""
    suffix = r"""
} catch { $reported = $_.Exception.Message }
$expected = 'CALCULATE,SAVE,CLOSE,RELEASE-Workbook,RELEASE-Workbooks,QUIT,RELEASE-Excel,COLLECT,FINALIZERS'
if (($script:events -join ',') -ne $expected) { throw ('Missing downstream cleanup: '+($script:events -join ',')) }
foreach ($message in @('forced Close failure','forced release Workbook','forced release Workbooks','forced Quit failure','forced release Excel','forced collection failure')) {
    if (!$reported.Contains($message)) { throw ('Missing collected error: '+$message+'; report='+$reported) }
}
"""
    _run_excel_powershell(prefix + _EXCEL_RECALCULATE + suffix)
