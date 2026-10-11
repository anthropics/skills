"""Materialise canonical runtime files without overwriting divergent local edits.

Run from any directory with Python 3.11+: python /path/to/tooling/sync_shared.py.
The per-skill manifest hashes delivered files, excludes itself and build debris,
and records which paths the synchronizer owns. It is not a signed attestation.
"""

from hashlib import sha256
import json
from pathlib import Path
import re

CANONICAL = Path(__file__).resolve().parent
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
BUILD_DIRECTORIES = {"__pycache__", ".pytest_cache"}


def _delivered(path: Path, root: Path) -> bool:
    parts = path.relative_to(root).parts
    return not (BUILD_DIRECTORIES.intersection(parts) or path.suffix in {".pyc", ".pyo"}
                or path.name == ".DS_Store" or path.name.startswith(".~lock."))


def _safe_target(root: Path, relative: str) -> Path:
    target = root / relative
    for part in (target, *target.parents):
        if part == root:
            break
        if part.is_symlink():
            raise ValueError(f"Refusing symlink in delivered path: {relative}")
        if part != target and part.exists() and not part.is_dir():
            raise ValueError(f"Expected a directory above delivered path: {relative}")
    if not target.resolve().is_relative_to(root):
        raise ValueError(f"Delivered path escapes skill: {relative}")
    if target.exists() and not target.is_file():
        raise ValueError(f"Expected a file at delivered path: {relative}")
    return target


def _previous_manifest(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        manifest = json.loads(path.read_bytes())
        files = manifest["files"]
        generated = manifest["generated_files"]
        if manifest["version"] != 1 or not isinstance(files, dict) or not isinstance(generated, list):
            raise ValueError("unsupported manifest structure")
        if len(generated) != len(set(generated)) or not set(generated) <= files.keys():
            raise ValueError("invalid generated-file inventory")
        for relative, digest in files.items():
            parts = relative.split("/")
            if (not relative or relative == "manifest.json" or "\\" in relative or ":" in relative
                    or any(part in {"", ".", ".."} for part in parts)
                    or not isinstance(digest, str) or not re.fullmatch(r"[a-f0-9]{64}", digest)):
                raise ValueError("invalid file path or SHA-256")
        return {relative: files[relative] for relative in generated}
    except (ValueError, KeyError, TypeError, AttributeError) as error:
        raise ValueError(f"Invalid manifest.json: {error}") from error


def sync_skill(skill_dir: Path) -> list[Path]:
    """Return sorted materialised paths (including manifest); leave identical files untouched.

    A differing existing shared file may be replaced only when its current bytes
    match its generated-file hash in the prior manifest. Preflight every file
    before any mutation, so a refused local edit cannot cause a partial update.
    Authored resources are hashed but never overwritten by this function.
    """
    root = Path(skill_dir).resolve()
    if not (root / "SKILL.md").is_file():
        raise ValueError(f"Missing skill entrypoint: {root / 'SKILL.md'}")
    manifest_path = _safe_target(root, "manifest.json")
    previous = _previous_manifest(manifest_path)
    payloads = {}
    for relative, source in sorted(SHARED.items()):
        target = _safe_target(root, relative)
        wanted = (CANONICAL / source).read_bytes()
        if Path(source).suffix not in {".ttf"}:
            wanted = wanted.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
        if target.exists():
            current = target.read_bytes()
            if current != wanted and sha256(current).hexdigest() != previous.get(relative):
                raise ValueError(f"Refusing divergent generated copy: {relative}; restore it or review its local changes")
        payloads[relative] = wanted

    hashes = {}
    for path in sorted(root.rglob("*")):
        if not _delivered(path, root):
            continue
        if path.is_symlink():
            raise ValueError(f"Refusing symlink in skill: {path.relative_to(root).as_posix()}")
        if path.is_file() and path != manifest_path:
            relative = path.relative_to(root).as_posix()
            hashes[relative] = sha256(payloads.get(relative, path.read_bytes())).hexdigest()
    hashes.update({relative: sha256(payload).hexdigest() for relative, payload in payloads.items()})
    manifest = {"version": 1, "generated_files": sorted(SHARED), "files": dict(sorted(hashes.items()))}
    payloads["manifest.json"] = (json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")
    for relative, payload in sorted(payloads.items()):
        target = root / relative
        if not target.exists() or target.read_bytes() != payload:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
    return [root / relative for relative in sorted(payloads)]


def main() -> None:
    registry = json.loads((CANONICAL / "domain-registry.json").read_bytes())
    names = [item["name"] for item in registry["skills"]]
    if len(names) != 11 or len(set(names)) != 11 or any(not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name) for name in names):
        raise ValueError("Expected eleven unique skill names in the registry")
    for name in sorted(names):
        paths = sync_skill(CANONICAL.parent / name)
        print(f"{name}: {len(paths) - 1} shared files, manifest verified")
    print(f"Synchronized {len(names)} self-contained skills")


if __name__ == "__main__":
    main()
