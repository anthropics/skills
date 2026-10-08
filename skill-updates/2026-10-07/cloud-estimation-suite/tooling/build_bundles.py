"""Build self-contained, reproducible ZIP-compatible .skill packages.

Run from any directory: python /path/to/tooling/build_bundles.py
Optional --output-dir chooses the destination (default: suite/bundles).
ZIP_STORED deliberately avoids compressor-version differences. Source bytes
are preserved; filenames, timestamps and regular-file modes are normalized.
Requires Python 3.11+ and only the standard library.
"""

import argparse
from hashlib import sha256
from io import BytesIO
import json
import ntpath
from pathlib import Path
import posixpath
import re
import stat
from zipfile import ZIP_STORED, ZipFile, ZipInfo

SUITE = Path(__file__).resolve().parents[1]
EXCLUDED_DIRECTORIES = {
    "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache", ".git",
    ".tox", ".venv", "venv", "node_modules", "tests", "build", "dist",
    "bundles", "htmlcov",
}
EXCLUDED_FILES = {".DS_Store", ".gitkeep", ".coverage"}


def _excluded(relative: Path) -> bool:
    return (
        any(part in EXCLUDED_DIRECTORIES or part.endswith(".egg-info") for part in relative.parts)
        or relative.name in EXCLUDED_FILES
        or relative.suffix in {".pyc", ".pyo", ".skill"}
        or relative.name.startswith(".~lock.")
        or (relative.suffix == ".py" and
            (relative.name.startswith("test_") or relative.name.endswith("_test.py")))
    )


def _resolved_skill_dir(skill_dir: Path) -> Path:
    if skill_dir.is_symlink() or getattr(skill_dir, "is_junction", lambda: False)():
        raise ValueError(f"Refusing linked skill directory: {skill_dir}")
    root = skill_dir.resolve()
    if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", root.name):
        raise ValueError(f"Invalid skill directory name: {root.name}")
    return root


def _validate_archive_path(filename: str) -> None:
    """Require a canonical relative path with unambiguous POSIX/Windows parts."""
    parts = filename.split("/")
    windows_name = filename.replace("/", "\\")
    if (not filename or any(character in filename for character in '\\:<>"|?*')
            or any(ord(character) < 32 for character in filename)
            or posixpath.isabs(filename) or ntpath.isabs(filename)
            or ntpath.splitdrive(filename)[0]
            or any(part in {"", ".", ".."} or part.rstrip(" .") != part for part in parts)
            or any(re.fullmatch(r"CON|PRN|AUX|NUL|CONIN\$|CONOUT\$|COM[1-9¹²³]|LPT[1-9¹²³]",
                                part.split(".", 1)[0].rstrip(" "), re.I) for part in parts)
            or posixpath.normpath(filename) != filename
            or ntpath.normpath(windows_name) != windows_name):
        raise ValueError(f"Unsafe archive path: {filename!r}")


def _archive_bytes(root: Path, output_dir: Path) -> bytes:
    if output_dir.resolve().is_relative_to(root):
        raise ValueError("Refusing output directory inside the skill")
    if not (root / "SKILL.md").is_file():
        raise ValueError(f"Missing skill entrypoint: {root / 'SKILL.md'}")
    payloads = {}
    for path in root.rglob("*"):
        relative = path.relative_to(root)
        if _excluded(relative):
            continue
        # Validate the complete name that will be given to ZipInfo. In particular,
        # literal backslashes in a POSIX filename must never become Windows '..'.
        filename = f"{root.name}/{relative.as_posix()}"
        _validate_archive_path(filename)
        if path.is_symlink() or getattr(path, "is_junction", lambda: False)():
            raise ValueError(f"Refusing symlink or junction in skill: {relative.as_posix()}")
        if not path.resolve().is_relative_to(root):
            raise ValueError(f"Skill member escapes its root: {relative.as_posix()}")
        if path.is_file():
            payloads[filename] = path.read_bytes()
        elif not path.is_dir():
            raise ValueError(f"Unsupported skill member: {relative.as_posix()}")
    manifest_member = f"{root.name}/manifest.json"
    if manifest_member in payloads:
        try:
            manifest = json.loads(payloads[manifest_member])
            actual = {filename.removeprefix(f"{root.name}/"): sha256(payload).hexdigest()
                      for filename, payload in payloads.items() if filename != manifest_member}
            if manifest["version"] != 1 or manifest["files"] != actual:
                raise ValueError("file inventory or hashes do not match delivered bytes")
        except (ValueError, KeyError, TypeError) as error:
            raise ValueError(f"Invalid member manifest for {root.name}: {error}") from error
    buffer = BytesIO()
    with ZipFile(buffer, "w", compression=ZIP_STORED) as archive:
        for filename, payload in sorted(payloads.items()):
            info = ZipInfo(filename, date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = ZIP_STORED
            archive.writestr(info, payload)
    return buffer.getvalue()


def _write_bundle(skill_dir: Path, output_dir: Path, payload: bytes) -> Path:
    filename = f"{skill_dir.name}.skill"
    _validate_archive_path(filename)
    target = output_dir / filename
    if target.is_symlink() or (target.exists() and not target.is_file()):
        raise ValueError(f"Refusing non-regular output: {target}")
    output_dir.mkdir(parents=True, exist_ok=True)
    if not target.exists() or target.read_bytes() != payload:
        target.write_bytes(payload)
    return target


def build_bundle(skill_dir: Path, output_dir: Path) -> Path:
    """Package delivered files below one root, refusing links and recursive output.

    All inputs are read before the output is touched. No temporary directory or
    authoring-tree path is encoded in the archive. Identical outputs stay intact.
    """
    root, output_dir = _resolved_skill_dir(Path(skill_dir)), Path(output_dir)
    payload = _archive_bytes(root, output_dir)
    return _write_bundle(root, output_dir, payload)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=SUITE / "bundles")
    output = parser.parse_args().output_dir
    registry = json.loads((SUITE / "tooling/domain-registry.json").read_bytes())
    names = [item["name"] for item in registry["skills"]]
    if (len(names) != 11 or len(set(names)) != 11
            or any(not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name) for name in names)):
        raise ValueError("Expected eleven unique skill names in the registry")
    # Preflight the whole suite before producing any output.
    roots = [_resolved_skill_dir(SUITE / name) for name in sorted(names)]
    payloads = {root: _archive_bytes(root, output) for root in roots}
    manifest = {"version": 1, "bundles": {}}
    manifest_path = output / "manifest.json"
    if manifest_path.is_symlink() or (manifest_path.exists() and not manifest_path.is_file()):
        raise ValueError(f"Refusing non-regular output: {manifest_path}")
    for root, payload in payloads.items():
        path = _write_bundle(root, output, payload)
        with ZipFile(path) as archive:
            if archive.testzip() is not None:
                raise ValueError(f"Corrupt archive: {path.name}")
            members = archive.infolist()
            record = {"sha256": sha256(path.read_bytes()).hexdigest(),
                      "member_count": len(members),
                      "uncompressed_size": sum(info.file_size for info in members)}
        manifest["bundles"][path.name] = record
        print(f"{path.name}: {record['member_count']} members, {record['uncompressed_size']} bytes, SHA-256 {record['sha256']}")
    manifest_bytes = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if not manifest_path.exists() or manifest_path.read_bytes() != manifest_bytes:
        manifest_path.write_bytes(manifest_bytes)
    print(f"Built and inspected {len(names)} bundles: {output}")


if __name__ == "__main__":
    main()
