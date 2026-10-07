# Cloud Estimation Skill Suite Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build and package eleven public Codex skills that always produce a homogeneous, anonymised XLSX estimate whose work items are expressed in JH.

**Architecture:** Each staged skill is self-contained, while canonical workbook contracts and reusable Python modules live under suite tooling and are copied into every bundle by a deterministic synchronisation step. Domain skills emit structured model data; the shared builder renders it into the fixed workbook schema, and shared validators enforce formulas, cached values, reconciliation, diagram consistency, and anonymisation.

**Tech Stack:** Python 3.11+, openpyxl, Pillow, pytest, JSON Schema-style validation implemented with the Python standard library, PowerShell-compatible commands, Excel COM or LibreOffice when available.

## Global Constraints

- Stage all work under `skill-updates/2026-10-07/cloud-estimation-suite/`; do not modify installed live skills.
- Every skill produces one `.xlsx` workbook with the twelve sheet names defined by the approved specification.
- Every task effort is stored in `JH`; one JH defaults to eight hours and remains editable.
- All public examples are synthetic and contain no client, project, account, domain, IP, repository, or traceable topology.
- Cloud prices require provider, SKU/service, region, unit, currency, capture date, source, and confidence; unverifiable prices remain `A chiffrer`.
- Every skill is licensed CC BY 4.0 and attributed to the repository maintainers without inventing a repository URL.
- Every bundle is self-contained and may not read files from a sibling skill at runtime.
- XLSX totals and scenario selections use formulas; no generated formula contains a hardcoded row coordinate derived by hand.
- Use provider-neutral diagram symbols by default; official icon packs are accepted only as runtime inputs with recorded rights metadata.

---

### Task 1: Establish the staged suite and executable contract

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/workbook-contract.json`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/domain-registry.json`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/LICENSE`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_contract.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/pytest.ini`

**Interfaces:**
- Produces: `workbook-contract.json` with `sheets`, `task_columns`, `scenario_names`, and `forbidden_patterns`.
- Produces: `domain-registry.json` mapping every skill name to its domain, triggers, and required workbook sections.

- [ ] **Step 1: Write the failing contract tests**

```python
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
    assert {"ID", "Tache", "Livrable", "JH bas", "JH probable", "JH haut", "JH retenu"} <= set(data["task_columns"])
    assert data["scenario_names"] == ["Economique", "Standard", "Resilient"]

def test_registry_contains_all_public_skills():
    data = json.loads((ROOT / "tooling/domain-registry.json").read_text(encoding="utf-8"))
    assert len(data["skills"]) == 11
    assert len({item["name"] for item in data["skills"]}) == 11
```

- [ ] **Step 2: Run the tests and verify the missing-contract failure**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_contract.py -v`

Expected: FAIL because the two JSON contracts do not exist.

- [ ] **Step 3: Create the contracts and licence**

Define the exact twelve sheets from the specification. Define task columns for ID, lot, domain, task, deliverable, environment, role, prerequisites, acceptance evidence, low/probable/high/retained JH, scenario override, one-off/recurring nature, coverage, source, confidence, and notes. Register exactly the eleven approved skill names. Add the unmodified CC BY 4.0 licence text.

- [ ] **Step 4: Run the contract tests**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_contract.py -v`

Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: define cloud estimation suite contract"
```

### Task 2: Implement the shared data model and XLSX builder

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/model.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/workbook_builder.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/fixtures/synthetic-brief.json`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_builder.py`

**Interfaces:**
- Produces: `load_model(path: Path) -> EstimateModel`.
- Produces: `build_workbook(model: EstimateModel, output: Path) -> Path`.
- `EstimateModel` contains `metadata`, `assumptions`, `inventory`, `architecture`, `tasks`, `cloud_costs`, `scenarios`, `phasing`, `risks`, `decisions`, and `sources`.

- [ ] **Step 1: Write failing builder tests**

```python
import json
from pathlib import Path
from openpyxl import load_workbook
from tooling.model import load_model
from tooling.workbook_builder import build_workbook

ROOT = Path(__file__).parents[1]

def test_builder_emits_contract_and_formulas(tmp_path):
    model = load_model(ROOT / "tests/fixtures/synthetic-brief.json")
    target = build_workbook(model, tmp_path / "estimate.xlsx")
    wb = load_workbook(target, data_only=False)
    contract = json.loads((ROOT / "tooling/workbook-contract.json").read_text(encoding="utf-8"))
    assert wb.sheetnames == contract["sheets"]
    ws = wb["04_Taches_JH"]
    headers = [cell.value for cell in ws[4]]
    assert headers == contract["task_columns"]
    retained = headers.index("JH retenu") + 1
    assert ws.cell(5, retained).value.startswith("=")

def test_builder_uses_required_financial_colours(tmp_path):
    model = load_model(ROOT / "tests/fixtures/synthetic-brief.json")
    wb = load_workbook(build_workbook(model, tmp_path / "estimate.xlsx"), data_only=False)
    assert wb["01_Hypotheses"]["B5"].font.color.rgb.endswith("0000FF")
```

- [ ] **Step 2: Run the builder tests and verify import failure**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_builder.py -v`

Expected: FAIL because `tooling.model` and `tooling.workbook_builder` do not exist.

- [ ] **Step 3: Implement the typed model and fixture parser**

Use frozen dataclasses for `Task`, `CloudCost`, `Scenario`, and `EstimateModel`. Validate required keys and reject negative JH. The fixture describes a synthetic web service with generic component names, three environments, three providers, and six tasks.

- [ ] **Step 4: Implement workbook generation**

Create sheets in contract order, titles at row 1, explanations at row 2, headers at row 4, and data from row 5. Use `openpyxl.worksheet.table.Table` for data ranges, blue font for inputs, black for formulas, green for cross-sheet links, and yellow fill for assumptions with status `A confirmer`. Generate `JH retenu` formulas from the global scenario named range unless a task override is present.

- [ ] **Step 5: Run builder tests**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_builder.py -v`

Expected: all tests pass.

- [ ] **Step 6: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: generate homogeneous estimation workbooks"
```

### Task 3: Add recalculation, reconciliation, and XLSX validation

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/recalculate.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/workbook_validator.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_validator.py`

**Interfaces:**
- Produces: `recalculate(path: Path) -> RecalculationResult` selecting Excel COM, LibreOffice, then calibrated Python fallback.
- Produces: `validate_workbook(path: Path, contract: Path) -> ValidationReport`.

- [ ] **Step 1: Write failure-focused validation tests**

```python
from openpyxl import Workbook
from tooling.workbook_validator import validate_workbook

def test_validator_rejects_formula_errors(tmp_path):
    path = tmp_path / "broken.xlsx"
    wb = Workbook()
    wb.active["A1"] = "=#REF!"
    wb.save(path)
    report = validate_workbook(path)
    assert not report.ok
    assert "#REF!" in report.errors[0]

def test_validator_rejects_hardcoded_prose_total(tmp_path, valid_workbook):
    report = validate_workbook(valid_workbook, asserted_totals={"11_Synthese!B12": 999})
    assert not report.ok
    assert any("reconciliation" in item.lower() for item in report.errors)
```

- [ ] **Step 2: Run tests and verify missing-validator failure**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_validator.py -v`

Expected: FAIL on missing imports.

- [ ] **Step 3: Implement platform-aware recalculation**

On Windows, detect Excel COM with `win32com.client.DispatchEx` and native LibreOffice under standard program directories. On other systems, discover `soffice` on `PATH`. Never use `socket.AF_UNIX` without `hasattr`. The Python fallback must first pass control workbooks whose correct and deliberately broken results differ.

- [ ] **Step 4: Implement structural and financial validation**

Validate required sheets and columns, formulas, cached values, table/filter overlap, unsupported future functions, detail-to-summary JH, provider/environment/scenario cost totals, diagram inventory IDs, prose assertions, and formula error tokens. Emit a JSON-serialisable report with explicit counts even when zero.

- [ ] **Step 5: Run validator tests and a synthetic workbook round trip**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_validator.py -v`

Expected: all tests pass and the valid fixture reports zero errors.

- [ ] **Step 6: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: validate and reconcile estimation workbooks"
```

### Task 4: Implement architecture diagram rendering

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/diagram_renderer.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/icon-policy.json`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_diagram_renderer.py`

**Interfaces:**
- Produces: `render_diagram(architecture: dict, svg: Path, png: Path, icon_pack: Path | None = None) -> DiagramManifest`.
- `DiagramManifest` exposes node IDs, edge IDs, icon sources, and output hashes.

- [ ] **Step 1: Write diagram consistency tests**

```python
from tooling.diagram_renderer import render_diagram

def test_diagram_contains_every_inventory_node(tmp_path, architecture):
    manifest = render_diagram(architecture, tmp_path / "a.svg", tmp_path / "a.png")
    assert set(manifest.node_ids) == {item["id"] for item in architecture["nodes"]}
    assert (tmp_path / "a.svg").read_text(encoding="utf-8").startswith("<svg")
    assert (tmp_path / "a.png").read_bytes().startswith(b"\x89PNG")

def test_unlicensed_icon_pack_is_rejected(tmp_path, architecture):
    bad_pack = tmp_path / "icons"
    bad_pack.mkdir()
    result = render_diagram(architecture, tmp_path / "a.svg", tmp_path / "a.png", bad_pack)
    assert result.icon_sources == ["provider-neutral"]
```

- [ ] **Step 2: Run tests and verify missing-renderer failure**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_diagram_renderer.py -v`

Expected: FAIL on missing import.

- [ ] **Step 3: Implement deterministic SVG and PNG rendering**

Lay out zones, environments, nodes, and directed flows deterministically. Use XML generation for SVG and Pillow for PNG. Render generic labelled symbols unless an icon pack includes a manifest with provider, official source URL, licence/trademark notice, and SHA-256 for every asset.

- [ ] **Step 4: Embed the PNG and manifest in `03_Architecture`**

Extend `build_workbook` so the sheet contains the PNG, node/flow tables, and icon provenance. Ensure the workbook inventory IDs and diagram manifest IDs are identical.

- [ ] **Step 5: Run diagram and workbook tests**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_diagram_renderer.py skill-updates/2026-10-07/cloud-estimation-suite/tests/test_workbook_builder.py -v`

Expected: all tests pass.

- [ ] **Step 6: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: render validated cloud architecture diagrams"
```

### Task 5: Author the orchestration skill

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/references/intake.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/references/reconciliation.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py`

**Interfaces:**
- Consumes: structured domain outputs matching `EstimateModel`.
- Produces: one merged, de-duplicated model and one validated XLSX.

- [ ] **Step 1: Write the structural skill test**

```python
def test_orchestrator_has_required_enforcement(load_skill):
    skill = load_skill("cloud-estimation-orchestrator")
    assert skill.frontmatter["name"] == "cloud-estimation-orchestrator"
    assert skill.frontmatter["description"]
    assert skill.unfinished_scaffold_markers == []
    assert skill.missing_references == []
    assert skill.missing_scripts == []
```

- [ ] **Step 2: Run the test and verify the missing-skill failure**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: FAIL because the skill does not exist.

- [ ] **Step 3: Write the skill and references**

The workflow must classify scope, route domains, distinguish measured from estimated components, reconcile existing estimates, price contradictory branches, merge stable task IDs, draw before finalising, generate the workbook, run validators, and stop delivery on any gate failure.

- [ ] **Step 4: Run structural tests**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: orchestrator test passes.

- [ ] **Step 5: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator skill-updates/2026-10-07/cloud-estimation-suite/tests
git commit -m "feat: add cloud estimation orchestrator skill"
```

### Task 6: Author infrastructure and architecture decision skills

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/infra-work-estimator/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/infra-work-estimator/references/task-catalogue.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-advisor/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-advisor/references/decision-matrix.md`
- Modify: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py`

**Interfaces:**
- Produces: infrastructure tasks, inventory items, architecture options, ADR decisions, risks, and source records.

- [ ] **Step 1: Add failing domain-contract tests**

Add a machine-readable `references/domain-contract.json` to each skill and validate its allowed input/output record types against `tooling/model.py`. The infrastructure contract must emit task, inventory, risk, and source records. The architecture contract must emit option, decision, risk, and cost-driver records. These tests validate interfaces and references, not prose wording.

- [ ] **Step 2: Run tests and verify both skills are missing**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: two domain failures.

- [ ] **Step 3: Write both skills with explicit output mappings**

Each workflow writes to the common model, identifies exclusions, prevents application work from leaking into infrastructure JH, and includes its own pre-delivery gate.

- [ ] **Step 4: Run tests and commit**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: all current structure tests pass.

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: add infrastructure and architecture skills"
```

### Task 7: Author Kubernetes and hosting simulation skills

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/kubernetes-architect/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/kubernetes-architect/references/cluster-checklist.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/hosting-capacity-simulator/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/hosting-capacity-simulator/references/capacity-model.md`
- Modify: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py`

**Interfaces:**
- Produces: sizing assumptions, capacity calculations, node pools, scaling bounds, failure domains, and sensitivity scenarios.

- [ ] **Step 1: Add failing domain-contract tests for sizing outputs**

Validate that the Kubernetes contract can emit node-pool, platform-task, risk, and recurring-operation records, and that the capacity contract accepts CPU, memory, storage, IOPS, bandwidth, concurrency, utilisation target, scaling limit, and failure-domain reserve as typed inputs. Do not test for prose phrases.

- [ ] **Step 2: Run tests and confirm failures**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

- [ ] **Step 3: Write both skills and references**

Use measured peaks when available. When absent, publish low/base/high workload assumptions and a measurement task. Require headroom and N+1 calculations to be visible workbook inputs.

- [ ] **Step 4: Run tests and commit**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: all current structure tests pass.

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: add kubernetes and capacity simulation skills"
```

### Task 8: Author CI/CD and server hardening skills

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cicd-devsecops-estimator/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cicd-devsecops-estimator/references/pipeline-catalogue.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/server-hardening-estimator/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/server-hardening-estimator/references/control-catalogue.md`
- Modify: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py`

**Interfaces:**
- Produces: delivery pipeline tasks, security control tasks, acceptance evidence, one-off JH, and recurring JH.

- [ ] **Step 1: Add failing domain-contract tests for delivery and control evidence**

Validate that CI/CD records support pipeline stage, evidence, one-off JH, and recurring JH fields. Validate that hardening records support control boundary, implementation task, verification evidence, one-off JH, recurring JH, and residual risk. Do not test for prose phrases.

- [ ] **Step 2: Run tests and confirm failures**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

- [ ] **Step 3: Write both skills and references**

Every control must name the evidence that proves completion. Every recurring activity must remain separate from construction JH.

- [ ] **Step 4: Run tests and commit**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: all current structure tests pass.

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: add cicd and server hardening skills"
```

### Task 9: Author provider selection and FinOps skills

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-provider-selector/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-provider-selector/references/scoring.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/finops-optimizer/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/finops-optimizer/references/optimisation-catalogue.md`
- Modify: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py`

**Interfaces:**
- Produces: transparent weighted scores, equal-scope three-year TCO, and savings opportunities with implementation/operation JH.

- [ ] **Step 1: Add failing domain-contract tests for decisions and savings**

Validate that provider comparison accepts region eligibility, service scope, commercial policy, implementation JH, recurring JH, and TCO horizon as inputs. Validate that every FinOps opportunity record requires baseline, action, savings range, one-off JH, recurring JH, risk, reversibility, and validation method. Do not test for prose phrases.

- [ ] **Step 2: Run tests and confirm failures**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

- [ ] **Step 3: Write both skills and references**

Require official pricing sources or billing exports, two independent total reconciliations, explicit forecast-versus-measurement labels, and no hardcoded current prices in skill files.

- [ ] **Step 4: Run tests and commit**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: all current structure tests pass.

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: add provider selection and finops skills"
```

### Task 10: Author migration and diagramming skills

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-migration-estimator/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-migration-estimator/references/migration-workflow.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-diagrammer/SKILL.md`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-diagrammer/references/icon-policy.md`
- Modify: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py`

**Interfaces:**
- Produces: source/target mapping, source-write constraint, cutover and rollback tasks, diagram node/flow model, SVG, PNG, and workbook embedding.

- [ ] **Step 1: Add failing domain-contract tests for migration and diagrams**

Validate that migration records require inventory evidence, documentation drift, source-write policy, rehearsal, integrity, rollback, decommissioning, and hypercare fields. Validate that diagram records reference inventory node IDs and icon provenance. Do not test for prose phrases.

- [ ] **Step 2: Run tests and confirm failures**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

- [ ] **Step 3: Write both skills and references**

Make topology drawing a verification step before estimate finalisation, not only a presentation step. Reject dangling flows and nodes absent from the inventory.

- [ ] **Step 4: Run tests and commit**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_skill_structure.py -v`

Expected: all eleven skill structure tests pass.

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "feat: add migration and architecture diagram skills"
```

### Task 11: Synchronise shared runtime files into self-contained skills

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/sync_shared.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_self_contained.py`

**Interfaces:**
- Produces: `sync_skill(skill_dir: Path) -> list[Path]`.
- Copies the contract, model, builder, validator, recalculator, renderer, licence, and common methodology into each skill.

- [ ] **Step 1: Write the failing self-containment test**

```python
def test_every_skill_contains_all_referenced_files(skill_dirs, parse_references):
    for skill_dir in skill_dirs:
        for relative in parse_references(skill_dir / "SKILL.md"):
            assert (skill_dir / relative).is_file(), f"{skill_dir.name}: missing {relative}"

def test_shared_runtime_copies_are_identical(skill_dirs):
    payloads = {(d / "scripts/workbook_builder.py").read_bytes() for d in skill_dirs}
    assert len(payloads) == 1
```

- [ ] **Step 2: Run tests and verify missing runtime files**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_self_contained.py -v`

Expected: FAIL with missing referenced files.

- [ ] **Step 3: Implement deterministic synchronisation**

Copy canonical shared files with LF line endings, create required directories, and emit `manifest.json` with SHA-256 hashes. Refuse to overwrite a divergent generated copy unless it matches the previous manifest.

- [ ] **Step 4: Synchronise and rerun tests**

Run: `python skill-updates/2026-10-07/cloud-estimation-suite/tooling/sync_shared.py`

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_self_contained.py -v`

Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "build: make every cloud estimation skill self contained"
```

### Task 12: Enforce public anonymisation

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/anonymisation.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_anonymisation.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/fixtures/forbidden-sample.txt`

**Interfaces:**
- Produces: `scan_tree(root: Path, policy: Path) -> AnonymisationReport` with matched path, rule, line, and redacted excerpt.

- [ ] **Step 1: Write a failing positive-control test**

```python
from tooling.anonymisation import scan_tree

def test_scanner_detects_identifiers_and_accepts_public_tree(tmp_path, policy):
    leaked = tmp_path / "leak.txt"
    leaked.write_text("project_id=client-prod-123 account=123456789012", encoding="utf-8")
    report = scan_tree(tmp_path, policy)
    assert {item.rule for item in report.matches} >= {"cloud-project-id", "cloud-account-id"}
```

- [ ] **Step 2: Run the test and verify missing-scanner failure**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_anonymisation.py -v`

- [ ] **Step 3: Implement bounded text and archive scanning**

Scan Markdown, JSON, Python, CSV, XML, SVG, and every textual entry inside XLSX/ZIP archives. Detect provider account formats, public IPs, non-example domains, email addresses, source workbook names, and a denylist derived from the private corpus. Report counts explicitly when zero.

- [ ] **Step 4: Scan the staged suite**

Run: `python skill-updates/2026-10-07/cloud-estimation-suite/tooling/anonymisation.py skill-updates/2026-10-07/cloud-estimation-suite`

Expected: `matches=0`, excluding the isolated positive-control fixture by explicit test-fixture rule.

- [ ] **Step 5: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "test: enforce public skill anonymisation"
```

### Task 13: Build and inspect `.skill` bundles

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tooling/build_bundles.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_bundles.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/bundles/.gitkeep`

**Interfaces:**
- Produces: `build_bundle(skill_dir: Path, output_dir: Path) -> Path`.
- Produces eleven ZIP-compatible `.skill` files and `bundles/manifest.json`.

- [ ] **Step 1: Write bundle completeness tests**

```python
from zipfile import ZipFile

def test_bundle_has_one_root_and_no_build_artifacts(bundle):
    with ZipFile(bundle) as zf:
        names = zf.namelist()
    roots = {name.split("/", 1)[0] for name in names}
    assert len(roots) == 1
    assert any(name.endswith("/SKILL.md") for name in names)
    assert not any("__pycache__" in name or name.endswith(".pyc") or ".DS_Store" in name for name in names)
```

- [ ] **Step 2: Run tests and verify missing bundles**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_bundles.py -v`

- [ ] **Step 3: Implement reproducible bundle creation**

Sort archive entries, normalise timestamps, include the full skill directory, exclude test/build artefacts, and record SHA-256, member count, and uncompressed size in the manifest.

- [ ] **Step 4: Build and inspect all archives**

Run: `python skill-updates/2026-10-07/cloud-estimation-suite/tooling/build_bundles.py`

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_bundles.py -v`

Expected: eleven bundles pass archive inspection.

- [ ] **Step 5: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "build: package cloud estimation skills"
```

### Task 14: Run the full synthetic acceptance scenario

**Files:**
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/tests/test_acceptance.py`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/examples/synthetic-cloud-estimate.xlsx`
- Create: `skill-updates/2026-10-07/cloud-estimation-suite/README.md`

**Interfaces:**
- Consumes: the synthetic brief, all skill contracts, and shared tooling.
- Produces: one public example workbook and an acceptance report.

- [ ] **Step 1: Write the end-to-end acceptance test**

```python
def test_public_example_meets_suite_success_criteria(example_report):
    assert example_report.formula_errors == 0
    assert example_report.anonymisation_matches == 0
    assert example_report.duplicate_task_ids == 0
    assert example_report.scenarios == 3
    assert example_report.providers >= 3
    assert example_report.capacity_overloads >= 1
    assert example_report.diagram_inventory_delta == 0
    assert example_report.cached_value_gaps == 0
```

- [ ] **Step 2: Run the acceptance test and capture failures**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests/test_acceptance.py -v`

Expected: FAIL until the example workbook and report are generated.

- [ ] **Step 3: Generate the example and README**

Generate a fully synthetic three-provider scenario with economic, standard, and resilient options, at least one capacity overload, one priced contradiction, one FinOps action, and one architecture decision. Document installation, skill routing, XLSX output, icon policy, validation commands, and public-data policy.

- [ ] **Step 4: Run the entire verification chain**

Run: `python -m pytest skill-updates/2026-10-07/cloud-estimation-suite/tests -v`

Run: `python skill-updates/2026-10-07/cloud-estimation-suite/tooling/anonymisation.py skill-updates/2026-10-07/cloud-estimation-suite`

Run: `python skill-updates/2026-10-07/cloud-estimation-suite/tooling/build_bundles.py`

Expected: all tests pass, anonymisation reports zero matches, and eleven bundles are rebuilt reproducibly.

- [ ] **Step 5: Open and recalculate the public example in a native spreadsheet application**

Open `examples/synthetic-cloud-estimate.xlsx` using Excel COM on Windows or LibreOffice elsewhere, save it, reopen it with `data_only=True`, and confirm zero cached-value gaps and zero formula errors.

- [ ] **Step 6: Commit**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "test: verify cloud estimation suite end to end"
```

### Task 15: Final skill-authoring and delivery gate

**Files:**
- Modify: any staged file that fails the final checks
- Verify: `skill-updates/2026-10-07/cloud-estimation-suite/bundles/manifest.json`

**Interfaces:**
- Produces: eleven reviewed `.skill` bundles ready for user installation.

- [ ] **Step 1: Validate every skill with the installed skill-authoring tooling**

Run the validator over the exact registry:

```powershell
rtk powershell -NoProfile -Command '$root="skill-updates/2026-10-07/cloud-estimation-suite"; $names=(Get-Content -Raw "$root/tooling/domain-registry.json" | ConvertFrom-Json).skills.name; foreach($name in $names){ & python -X utf8 "C:\Users\hp\.codex\skills\.system\skill-creator\scripts\quick_validate.py" "$root/$name"; if($LASTEXITCODE -ne 0){ exit $LASTEXITCODE } }'
```

Record each name, exit status, and diagnostic count. Expected: eleven exit statuses equal to zero and zero unfinished scaffold placeholders.

- [ ] **Step 2: Run independent forward-tests on realistic synthetic requests**

Dispatch a fresh evaluator for each skill with only the staged skill path, one synthetic request, and the minimum synthetic inputs. The evaluator must generate the requested XLSX in an isolated temporary directory. Review observable results: stable workbook sheets, non-duplicated JH tasks, correct domain boundaries, explicit unknowns, scenario differences, formula reconciliation, and the domain-specific decisions required by the specification. Record the request, artifact hash, validator report, and behavioural verdict. Failed behaviour requires a focused skill correction and a new forward-test; matching preferred wording is not a pass criterion.

- [ ] **Step 3: Run confidentiality and cross-example re-identification review**

List every public example's vertical, geography, counts, dates, amounts, and provider mix. Confirm that their combination cannot be mapped back to any source workbook; widen or replace any identifying combination.

- [ ] **Step 4: Verify bundle references and archive listings**

For each `SKILL.md`, resolve every `references/`, `scripts/`, and `assets/` path inside its corresponding `.skill` archive. Assert eleven manifest entries, eleven unique hashes, and no unlisted file.

- [ ] **Step 5: Run final repository checks**

Run: `git diff --check`

Run: `git status --short`

Expected: no whitespace errors; only intended staged suite files and generated bundles are changed.

- [ ] **Step 6: Commit the delivery gate results**

```bash
git add skill-updates/2026-10-07/cloud-estimation-suite
git commit -m "chore: complete cloud estimation skill delivery gate"
```

