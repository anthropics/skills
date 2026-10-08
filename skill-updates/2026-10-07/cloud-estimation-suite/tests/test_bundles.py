"""Inspect actual ZIP artifacts; these checks do not prove agent decisions."""

from hashlib import sha256
import importlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
import stat
import subprocess
import sys
from types import SimpleNamespace
from zipfile import ZipFile

import pytest

ROOT = Path(__file__).parents[1]
SKILLS = (
    "cicd-devsecops-estimator", "cloud-architecture-advisor",
    "cloud-architecture-diagrammer", "cloud-estimation-orchestrator",
    "cloud-migration-estimator", "cloud-provider-selector", "finops-optimizer",
    "hosting-capacity-simulator", "infra-work-estimator", "kubernetes-architect",
    "server-hardening-estimator",
)


def test_bundle_builder_entrypoint_is_available():
    assert (ROOT / "tooling/build_bundles.py").is_file(), "Missing bundle builder"


@pytest.fixture
def builder():
    assert (ROOT / "tooling/build_bundles.py").is_file(), "Missing bundle builder"
    return importlib.import_module("tooling.build_bundles")


@pytest.fixture(scope="module")
def builds(tmp_path_factory):
    script = ROOT / "tooling/build_bundles.py"
    assert script.is_file(), "Missing bundle builder"
    workspace = tmp_path_factory.mktemp("bundle-builds")
    outputs = [workspace / "first", workspace / "second"]
    for output in outputs:
        result = subprocess.run(
            [sys.executable, str(script), "--output-dir", str(output)],
            cwd=workspace, capture_output=True, text=True, timeout=45,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert "Built and inspected 11 bundles" in result.stdout
    return outputs


def test_cli_builds_exact_registry_and_reproducible_manifest(builds):
    first, second = builds
    assert set(SKILLS) == {
        item["name"] for item in json.loads((ROOT / "tooling/domain-registry.json").read_bytes())["skills"]
    }
    expected = {f"{name}.skill" for name in SKILLS} | {"manifest.json"}
    assert {path.name for path in first.iterdir()} == expected
    assert {path.name for path in second.iterdir()} == expected
    for filename in expected:
        assert (first / filename).read_bytes() == (second / filename).read_bytes(), filename
    manifest = json.loads((first / "manifest.json").read_bytes())
    assert manifest["version"] == 1
    assert set(manifest["bundles"]) == {f"{name}.skill" for name in SKILLS}
    assert "manifest.json" not in manifest["bundles"]
    for filename, record in manifest["bundles"].items():
        archive = first / filename
        with ZipFile(archive) as zf:
            assert record == {
                "sha256": sha256(archive.read_bytes()).hexdigest(),
                "member_count": len(zf.infolist()),
                "uncompressed_size": sum(info.file_size for info in zf.infolist()),
            }


@pytest.mark.parametrize("name", SKILLS)
def test_every_bundle_contains_all_delivered_bytes_with_safe_deterministic_metadata(name, builds):
    directory = ROOT / name
    file_manifest = json.loads((directory / "manifest.json").read_bytes())
    expected = {f"{name}/{relative}" for relative in file_manifest["files"]} | {f"{name}/manifest.json"}
    with ZipFile(builds[0] / f"{name}.skill") as zf:
        assert zf.testzip() is None
        names = zf.namelist()
        assert names == sorted(expected)
        assert len(names) == len(set(names))
        assert {PurePosixPath(path).parts[0] for path in names} == {name}
        for info in zf.infolist():
            path = PurePosixPath(info.filename)
            assert not path.is_absolute() and ".." not in path.parts and "\\" not in info.filename
            assert info.date_time == (1980, 1, 1, 0, 0, 0)
            assert info.create_system == 3
            assert info.external_attr >> 16 == stat.S_IFREG | 0o644
            assert info.extra == b"" and info.comment == b""
            assert not info.is_dir()
            assert zf.read(info) == directory.joinpath(*path.parts[1:]).read_bytes()
        for relative, digest in file_manifest["files"].items():
            assert sha256(zf.read(f"{name}/{relative}")).hexdigest() == digest
        # Follow local links from each archived document's own directory.
        for filename in names:
            if filename.endswith(".md"):
                for target in re.findall(r"\]\(([^)]+)\)", zf.read(filename).decode("utf-8")):
                    relative = target.split("#", 1)[0]
                    if relative and not re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", relative):
                        resolved = posixpath.normpath(str(PurePosixPath(filename).parent / relative))
                        assert resolved in expected


def test_build_excludes_nested_cache_tests_and_build_artifacts_but_keeps_assets(builder, tmp_path):
    directory = tmp_path / "example-skill"
    wanted = {"SKILL.md": b"entrypoint\n", "scripts/main.py": b"print('ok')\n",
              "assets/template.zip": b"binary-template", "references/guide.md": b"guide\n"}
    debris = ["__pycache__/module.pyc", "scripts/cache.pyc", "scripts/cache.pyo",
              ".pytest_cache/cache", ".mypy_cache/cache", ".ruff_cache/cache",
              ".git/config", "tests/test_module.py", "scripts/test_main.py",
              "build/output", "dist/output", "bundles/prior.skill", "venv/config",
              ".venv/config", "node_modules/config", "htmlcov/index.html",
              "package.egg-info/PKG-INFO", "references/.DS_Store", ".gitkeep",
              ".coverage", "assets/.~lock.workbook.xlsx#"]
    for relative, payload in {**wanted, **dict.fromkeys(debris, b"exclude me")}.items():
        path = directory / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)
    archive = builder.build_bundle(directory, tmp_path / "output")
    assert archive == tmp_path / "output/example-skill.skill"
    with ZipFile(archive) as zf:
        assert zf.namelist() == sorted(f"example-skill/{relative}" for relative in wanted)
        for relative, payload in wanted.items():
            assert zf.read(f"example-skill/{relative}") == payload


def test_archive_bytes_ignore_source_order_timestamps_and_permissions(builder, tmp_path):
    first = tmp_path / "first/example-skill"
    second = tmp_path / "second/example-skill"
    payloads = {"SKILL.md": b"entrypoint\n", "scripts/z.py": b"z\n", "assets/a.bin": b"\x00\xff"}
    for directory, order, timestamp, mode in (
        (first, list(payloads), 1700000000, 0o644),
        (second, list(reversed(payloads)), 1800000000, 0o666),
    ):
        for relative in order:
            path = directory / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payloads[relative])
            os.utime(path, (timestamp, timestamp))
            path.chmod(mode)
    a = builder.build_bundle(first, tmp_path / "out-first")
    b = builder.build_bundle(second, tmp_path / "out-second")
    assert a.read_bytes() == b.read_bytes()


@pytest.mark.parametrize("relative_name", [
    r"..\..\outside.txt", r"C:\outside.txt", "/outside.txt",
    "//host/share/outside.txt", "C:/outside.txt", "C:outside.txt",
    "nested/C:/outside.test", "nested//outside.test", "./outside.txt",
    "nested/../outside.txt", "nested/./outside.txt", "", ".", "..",
    "nested/.../outside.txt", "nested/.. /outside.txt", "nested/ /outside.txt",
    "nested/trailing./outside.txt", "nested/name:stream.txt", "nested/name\x00truncated.txt",
    "nested/CON", "nested/prn.txt", "AUX/device.txt", "nested/NUL.json",
    "nested/COM1.txt", "nested/com9.log", "LPT1/guide.md", "nested/lpt9.bin",
    "nested/COM¹.txt", "nested/LPT².bin", "nested/CONIN$", "nested/CONOUT$.txt",
    "nested/CON .txt", 'nested/name".txt', "nested/name<.txt", "nested/name>.txt",
    "nested/name|.txt", "nested/name?.txt", "nested/name*.txt",
])
def test_cross_platform_unsafe_member_names_are_refused_before_output(
        builder, tmp_path, monkeypatch, relative_name):
    directory = tmp_path / "example-skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"entrypoint\n")
    candidate = directory / "candidate.txt"
    candidate.write_bytes(b"harmless local payload\n")
    output = tmp_path / "output"
    # Windows cannot create a POSIX filename containing literal backslashes.
    # Substitute only the relative name of an ordinary local file; all reads,
    # ZIP construction and output behavior still exercise the real builder.
    # Nothing named outside.txt is ever created or extracted by this test.
    real_relative_to = Path.relative_to
    portable_relative = SimpleNamespace(
        parts=tuple(relative_name.split("/")),
        name=PurePosixPath(relative_name).name,
        suffix=PurePosixPath(relative_name).suffix,
        as_posix=lambda: relative_name,
    )

    def relative_to(path, *args, **kwargs):
        if path == candidate:
            return portable_relative
        return real_relative_to(path, *args, **kwargs)

    monkeypatch.setattr(Path, "relative_to", relative_to)
    with pytest.raises(ValueError, match="archive path"):
        builder.build_bundle(directory, output)
    assert not output.exists()
    assert sorted(path.name for path in tmp_path.iterdir()) == ["example-skill"]


@pytest.mark.parametrize("relative", [Path("."), Path("foo") / ".."])
def test_resolved_skill_basename_matches_bundle_filename_and_archive_root(
        builder, tmp_path, monkeypatch, relative):
    directory = tmp_path / "example-skill"
    (directory / "foo").mkdir(parents=True)
    (directory / "SKILL.md").write_bytes(b"entrypoint\n")
    output = tmp_path / "output"
    monkeypatch.chdir(directory)
    archive = builder.build_bundle(relative, output)
    assert archive == output / "example-skill.skill"
    with ZipFile(archive) as zf:
        assert zf.namelist() == ["example-skill/SKILL.md"]


def test_missing_entrypoint_is_refused_without_output(builder, tmp_path):
    directory = tmp_path / "incomplete"
    directory.mkdir()
    output = tmp_path / "output"
    with pytest.raises(ValueError, match="SKILL.md"):
        builder.build_bundle(directory, output)
    assert not output.exists()


@pytest.mark.parametrize("change", ["modified", "missing", "unlisted"])
def test_stale_member_manifest_is_refused_before_output(builder, tmp_path, change):
    directory = tmp_path / "infra-work-estimator"
    shutil.copytree(ROOT / directory.name, directory,
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    target = directory / "scripts/model.py"
    if change == "modified":
        target.write_bytes(b"modified runtime\n")
    elif change == "missing":
        target.unlink()
    else:
        (directory / "unlisted-resource.md").write_bytes(b"new resource\n")
    with pytest.raises(ValueError, match="manifest"):
        builder.build_bundle(directory, tmp_path / "output")
    assert not (tmp_path / "output").exists()


def test_output_inside_skill_is_refused_without_mutating_source(builder, tmp_path):
    directory = tmp_path / "example-skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"entrypoint\n")
    with pytest.raises(ValueError, match="inside"):
        builder.build_bundle(directory, directory / "bundles")
    assert not (directory / "bundles").exists()


def test_symlink_to_external_payload_is_refused_without_output(builder, tmp_path):
    directory = tmp_path / "example-skill"
    directory.mkdir()
    (directory / "SKILL.md").write_bytes(b"entrypoint\n")
    outside = tmp_path / "outside.txt"
    outside.write_bytes(b"must stay outside\n")
    try:
        (directory / "linked.txt").symlink_to(outside)
    except OSError as error:
        pytest.skip(f"Symlink creation unavailable: {error}")
    with pytest.raises(ValueError, match="symlink|link"):
        builder.build_bundle(directory, tmp_path / "output")
    assert not (tmp_path / "output").exists()


def test_extracted_bundle_runtime_has_no_authoring_tree_dependency(builds, tmp_path):
    import site

    name = "hosting-capacity-simulator"
    with ZipFile(builds[0] / f"{name}.skill") as zf:
        zf.extractall(tmp_path)
    shutil.copyfile(ROOT / "tests/fixtures/synthetic-brief.json", tmp_path / "input.json")
    program = """
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path.cwd()))
sys.path.extend(json.loads(sys.argv[1]))
from scripts.model import load_model
from scripts.workbook_builder import build_workbook
from scripts.workbook_validator import validate_workbook
from scripts.validate_capacity import validate_capacity_inputs
model = load_model(Path('../input.json'))
path = build_workbook(model, Path('isolated.xlsx'))
report = validate_workbook(path)
assert report.counts['sheets'] == 12
assert report.counts['formula_errors'] == 0
assert report.counts['missing_cached_values'] > 0
assert not report.ok
for name, module in list(sys.modules.items()):
    if name.startswith('scripts.'):
        assert Path(module.__file__).resolve().is_relative_to(Path.cwd())
print('isolated bundle runtime verified')
"""
    result = subprocess.run(
        [sys.executable, "-I", "-c", program,
         json.dumps([*site.getsitepackages(), site.getusersitepackages()])],
        cwd=tmp_path / name, capture_output=True, text=True, timeout=45,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == "isolated bundle runtime verified"
