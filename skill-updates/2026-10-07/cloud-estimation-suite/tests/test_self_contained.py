"""Mechanical self-containment and real isolated-runtime checks, not agent decisions."""

from hashlib import sha256
import importlib
import json
from pathlib import Path
import re
import site
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).parents[1]
SKILLS = [item["name"] for item in json.loads((ROOT / "tooling/domain-registry.json").read_text())["skills"]]
SHARED = {
    "scripts/model.py": "model.py",
    "scripts/workbook_builder.py": "workbook_builder.py",
    "scripts/workbook_validator.py": "workbook_validator.py",
    "scripts/recalculate.py": "recalculate.py",
    "scripts/publication.py": "publication.py",
    "scripts/diagram_renderer.py": "diagram_renderer.py",
    "scripts/fonts/lato/Lato-Regular.ttf": "fonts/lato/Lato-Regular.ttf",
    "scripts/fonts/lato/OFL.txt": "fonts/lato/OFL.txt",
    "scripts/fonts/lato/provenance.json": "fonts/lato/provenance.json",
    "scripts/workbook-contract.json": "workbook-contract.json",
    "scripts/icon-policy.json": "icon-policy.json",
    "references/common-methodology.md": "common-methodology.md",
    "LICENSE": "LICENSE",
}


def local_references(document):
    """Resolve every local Markdown target from its containing document."""
    for match in re.finditer(r"\]\(([^)]+)\)", document.read_text(encoding="utf-8")):
        relative = match.group(1).split("#", 1)[0]
        if relative and not re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", relative):
            yield document.parent / relative


@pytest.fixture
def sync_module():
    path = ROOT / "tooling/sync_shared.py"
    assert path.is_file(), "Missing deterministic shared-runtime synchronizer"
    return importlib.import_module("tooling.sync_shared")


def test_registry_and_local_links_cover_all_eleven_skills():
    assert len(SKILLS) == len(set(SKILLS)) == 11
    for name in SKILLS:
        directory = ROOT / name
        documents = sorted(directory.rglob("*.md"))
        assert directory / "SKILL.md" in documents
        for document in documents:
            for target in local_references(document):
                assert target.resolve().is_relative_to(directory.resolve()), f"{document}: escapes bundle: {target}"
                assert target.is_file(), f"{document}: missing {target}"


def test_local_reference_control_uses_document_directory(tmp_path):
    reference = tmp_path / "references"
    reference.mkdir()
    (reference / "contract.json").write_bytes(b"{}\n")
    document = reference / "guide.md"
    document.write_bytes(b"[good](contract.json) [broken](references/contract.json)\n")
    good, broken = list(local_references(document))
    assert good.is_file()
    assert not broken.is_file()


@pytest.mark.parametrize("name", SKILLS)
def test_shared_copies_and_complete_manifest_are_lf_and_identical(name):
    directory = ROOT / name
    for relative, canonical in SHARED.items():
        target = directory / relative
        assert target.is_file(), f"{name}: missing {relative}"
        payload = target.read_bytes()
        expected = (ROOT / "tooling" / canonical).read_bytes()
        if not canonical.endswith(".ttf"):
            assert b"\r" not in payload, f"{name}: non-LF generated file {relative}"
            expected = expected.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
        assert payload == expected
    manifest = json.loads((directory / "manifest.json").read_bytes())
    expected = {
        path.relative_to(directory).as_posix(): sha256(path.read_bytes()).hexdigest()
        for path in directory.rglob("*")
        if path.is_file() and path != directory / "manifest.json"
        and "__pycache__" not in path.parts and path.suffix != ".pyc"
    }
    assert manifest["files"] == expected
    assert set(manifest["generated_files"]) == set(SHARED)
    assert "manifest.json" not in manifest["files"]


def test_sync_is_deterministic_without_rewriting_unchanged_files(sync_module, tmp_path):
    directory = tmp_path / "skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"Authored entrypoint\n")
    first = sync_module.sync_skill(directory)
    before = {p.relative_to(directory).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns) for p in first}
    second = sync_module.sync_skill(directory)
    assert first == second
    assert before == {p.relative_to(directory).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns) for p in second}


@pytest.mark.parametrize("prior_manifest", [False, True])
def test_sync_refuses_divergent_copy_before_any_write(sync_module, tmp_path, prior_manifest):
    directory = tmp_path / "skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"Authored entrypoint\n")
    if prior_manifest:
        sync_module.sync_skill(directory)
    target = directory / "scripts/workbook_builder.py"
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(b"Locally authored builder; preserve me\n")
    before = {p.relative_to(directory): p.read_bytes() for p in directory.rglob("*") if p.is_file()}
    with pytest.raises(ValueError, match="scripts/workbook_builder.py"):
        sync_module.sync_skill(directory)
    assert before == {p.relative_to(directory): p.read_bytes() for p in directory.rglob("*") if p.is_file()}


def test_sync_updates_copy_matching_previous_manifest(sync_module, tmp_path):
    directory = tmp_path / "skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"Authored entrypoint\n")
    sync_module.sync_skill(directory)
    target = directory / "scripts/model.py"
    target.write_bytes(b"Previous canonical generation\n")
    path = directory / "manifest.json"
    manifest = json.loads(path.read_bytes())
    manifest["files"]["scripts/model.py"] = sha256(target.read_bytes()).hexdigest()
    path.write_bytes(json.dumps(manifest).encode())
    sync_module.sync_skill(directory)
    assert target.read_bytes() == (ROOT / "tooling/model.py").read_bytes().replace(b"\r\n", b"\n")


def test_sync_refuses_malformed_manifest(sync_module, tmp_path):
    directory = tmp_path / "skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"Authored entrypoint\n")
    (directory / "manifest.json").write_bytes(b"not JSON\n")
    with pytest.raises(ValueError, match="manifest.json"):
        sync_module.sync_skill(directory)
    assert not (directory / "scripts").exists()


def test_sync_refuses_blocked_parent_before_any_write(sync_module, tmp_path):
    directory = tmp_path / "skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"Authored entrypoint\n")
    (directory / "scripts").write_bytes(b"Authored file blocking runtime directory\n")
    before = {p.name: p.read_bytes() for p in directory.iterdir()}
    with pytest.raises(ValueError, match="scripts"):
        sync_module.sync_skill(directory)
    assert before == {p.name: p.read_bytes() for p in directory.iterdir()}


@pytest.mark.parametrize("name", SKILLS)
def test_skill_runtime_executes_with_no_suite_or_sibling_on_path(name, tmp_path):
    # Missing transitive imports, colocated policies or external path dependencies
    # fail here even if all of the source paths exist in the authoring repository.
    directory = tmp_path / name
    shutil.copytree(ROOT / name, directory, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    shutil.copyfile(ROOT / "tests/fixtures/synthetic-brief.json", tmp_path / "input.json")
    program = """
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path.cwd()))
# -I deliberately excludes user-site discovery. Admit only explicit installed
# dependency directories; do not execute .pth files or inherit PYTHONPATH.
sys.path.extend(json.loads(sys.argv[1]))
from scripts.model import load_model
from scripts.workbook_builder import build_workbook
from scripts.diagram_renderer import render_diagram
from scripts.recalculate import _calibrate_python
from scripts.workbook_validator import validate_workbook
for module in ('scripts.model', 'scripts.workbook_builder', 'scripts.diagram_renderer',
               'scripts.recalculate', 'scripts.workbook_validator'):
    assert Path(sys.modules[module].__file__).resolve().is_relative_to(Path.cwd())
model = load_model(Path('../input.json'))
graph = {'nodes': [dict(row) for row in model.inventory], 'edges': []}
diagram = render_diagram(graph, Path('isolated.svg'), Path('isolated.png'))
workbook = build_workbook(model, Path('isolated.xlsx'), architecture=graph)
report = validate_workbook(workbook, diagram_inventory_ids=diagram.node_ids)
assert report.counts['sheets'] == 12
assert report.counts['diagram_inventory_ids'] == 3
assert report.counts['formula_errors'] == 0
assert report.counts['missing_cached_values'] > 0
assert not report.ok  # Unrecalculated workbook must still fail closed.
assert _calibrate_python() == (10, [])
print(json.dumps({'sheets': 12, 'nodes': 3, 'calibration_controls': 10}))
"""
    dependency_paths = [*site.getsitepackages(), site.getusersitepackages()]
    assert all(not Path(path).resolve().is_relative_to(ROOT) for path in dependency_paths)
    result = subprocess.run([sys.executable, "-I", "-c", program, json.dumps(dependency_paths)],
                            cwd=directory, text=True, capture_output=True, timeout=45)
    assert result.returncode == 0, f"{name}: {result.stdout}\n{result.stderr}"
    assert json.loads(result.stdout) == {"sheets": 12, "nodes": 3, "calibration_controls": 10}
