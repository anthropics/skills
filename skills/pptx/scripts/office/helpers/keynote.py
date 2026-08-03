"""Keynote compatibility repairs for packed PPTX files."""

from __future__ import annotations

import html
import os
import posixpath
import re
import tempfile
import zipfile
from collections.abc import Mapping
from pathlib import Path

import defusedxml.minidom

from . import opc_target, part_text

PRESENTATION = "ppt/presentation.xml"
PRESENTATION_RELS = "ppt/_rels/presentation.xml.rels"
CONTENT_TYPES = "[Content_Types].xml"

PRESENTATION_NS = "http://schemas.openxmlformats.org/presentationml/2006/main"
OFFICE_REL_NS = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
PRINTER_SETTINGS_CONTENT_TYPE = (
    "application/vnd.openxmlformats-officedocument.presentationml.printerSettings"
)
OLE_OBJECT_CONTENT_TYPE = "application/vnd.openxmlformats-officedocument.oleObject"

_SLIDE_SIZE_RE = re.compile(r"<(?P<prefix>[A-Za-z_][\w.-]*):sldSz\b(?P<attrs>[^>]*)/>")
_SUCCESSORS_OF_NOTES_MASTER = (
    "handoutMasterIdLst",
    "sldIdLst",
    "sldSz",
    "notesSz",
    "smartTags",
    "embeddedFontLst",
    "custShowLst",
    "photoAlbum",
    "custDataLst",
    "kinsoku",
    "defaultTextStyle",
    "modifyVerifier",
    "extLst",
)


class SanitizeError(ValueError):
    """The package cannot be repaired without guessing its semantics."""


def _attribute(attrs: str, name: str) -> str | None:
    match = re.search(rf"\b{re.escape(name)}\s*=\s*(['\"])(.*?)\1", attrs)
    return match.group(2) if match else None


def _remove_attribute(attrs: str, name: str) -> str:
    return re.sub(rf"\s+{re.escape(name)}\s*=\s*(['\"]).*?\1", "", attrs, count=1)


def _set_attribute(attrs: str, name: str, value: str) -> str:
    pattern = re.compile(rf"\b{re.escape(name)}\s*=\s*(['\"])(.*?)\1")
    if pattern.search(attrs):
        return pattern.sub(f'{name}="{value}"', attrs, count=1)
    return attrs.rstrip() + f' {name}="{value}"'


def _patch_slide_size(presentation_xml: str) -> tuple[str, bool]:
    """Normalize slide dimensions without discarding unrelated attributes."""
    match = _SLIDE_SIZE_RE.search(presentation_xml)
    if match is None:
        return presentation_xml, False

    attrs = match.group("attrs")
    cx_text = _attribute(attrs, "cx")
    cy_text = _attribute(attrs, "cy")
    if cx_text is None or cy_text is None:
        return presentation_xml, False
    try:
        cx, cy = int(cx_text), int(cy_text)
    except ValueError:
        return presentation_xml, False

    updated = attrs
    if abs(cx - 12192000) <= 60000 and abs(cy - 6858000) <= 60000:
        updated = _set_attribute(updated, "cx", "12192000")
        updated = _set_attribute(updated, "cy", "6858000")
        updated = _remove_attribute(updated, "type")
    elif abs(cx - 9144000) <= 60000 and abs(cy - 6858000) <= 60000:
        updated = _set_attribute(updated, "cx", "9144000")
        updated = _set_attribute(updated, "cy", "6858000")
        updated = _set_attribute(updated, "type", "screen4x3")
    else:
        updated = _remove_attribute(updated, "type")

    replacement = f"<{match.group('prefix')}:sldSz{updated}/>"
    if replacement == match.group(0):
        return presentation_xml, False
    return presentation_xml[: match.start()] + replacement + presentation_xml[
        match.end() :
    ], True


def _dom(data: bytes | str, part: str):
    try:
        return defusedxml.minidom.parseString(data)
    except Exception as exc:
        raise SanitizeError(f"cannot parse {part}: {exc}") from exc


def _relationship_elements(data: bytes | str, part: str):
    dom = _dom(data, part)
    return dom, list(dom.getElementsByTagName("Relationship"))


def _notes_master_rid(rels_xml: bytes | str) -> str | None:
    _, relationships = _relationship_elements(rels_xml, PRESENTATION_RELS)
    ids = [
        rel.getAttribute("Id")
        for rel in relationships
        if rel.getAttribute("Type").rstrip("/").endswith("/notesMaster")
    ]
    if len(ids) > 1:
        raise SanitizeError("presentation has more than one notesMaster relationship")
    return ids[0] if ids else None


def _namespace_prefix(xml: str, namespace: str) -> str | None:
    match = re.search(
        rf"\bxmlns:(?P<prefix>[A-Za-z_][\w.-]*)\s*=\s*(['\"]){re.escape(namespace)}\2",
        xml,
    )
    return match.group("prefix") if match else None


def _add_notes_master_id(
    presentation_xml: str, rels_xml: bytes | str
) -> tuple[str, bool]:
    """Register a missing notes master in CT_Presentation sequence order."""
    p_prefix = _namespace_prefix(presentation_xml, PRESENTATION_NS)
    r_prefix = _namespace_prefix(presentation_xml, OFFICE_REL_NS)
    if p_prefix is None or r_prefix is None:
        return presentation_xml, False
    if re.search(rf"<{re.escape(p_prefix)}:notesMasterIdLst\b", presentation_xml):
        return presentation_xml, False

    rid = _notes_master_rid(rels_xml)
    if rid is None:
        return presentation_xml, False
    block = (
        f"<{p_prefix}:notesMasterIdLst>"
        f'<{p_prefix}:notesMasterId {r_prefix}:id="{html.escape(rid, quote=True)}"/>'
        f"</{p_prefix}:notesMasterIdLst>"
    )

    for name in _SUCCESSORS_OF_NOTES_MASTER:
        anchor = re.search(rf"<{re.escape(p_prefix)}:{name}\b", presentation_xml)
        if anchor:
            return (
                presentation_xml[: anchor.start()]
                + block
                + presentation_xml[anchor.start() :],
                True,
            )

    master = re.search(
        rf"<{re.escape(p_prefix)}:sldMasterIdLst\b(?:[^>]*/>|.*?</{re.escape(p_prefix)}:sldMasterIdLst\s*>)",
        presentation_xml,
        re.DOTALL,
    )
    if master:
        return (
            presentation_xml[: master.end()] + block + presentation_xml[master.end() :],
            True,
        )
    raise SanitizeError("presentation.xml has no legal notesMasterIdLst anchor")


def _source_part_for_rels(rels_path: str) -> str:
    directory, filename = posixpath.split(rels_path)
    if posixpath.basename(directory) != "_rels" or not filename.endswith(".rels"):
        raise SanitizeError(f"invalid relationships part name: {rels_path}")
    return posixpath.join(posixpath.dirname(directory), filename[: -len(".rels")])


def _targets_for_relationship(
    files: Mapping[str, bytes], relationship_suffix: str
) -> set[str]:
    targets: set[str] = set()
    for name, data in files.items():
        if not name.endswith(".rels"):
            continue
        _, relationships = _relationship_elements(data, name)
        source = _source_part_for_rels(name)
        for rel in relationships:
            if not rel.getAttribute("Type").rstrip("/").endswith(relationship_suffix):
                continue
            try:
                target = opc_target(
                    rel.getAttribute("Target"),
                    source,
                    rel.getAttribute("TargetMode"),
                )
            except ValueError as exc:
                raise SanitizeError(f"invalid target in {name}: {exc}") from exc
            if target is not None:
                targets.add(target)
    return targets


def _remove_printer_relationships(files: dict[str, bytes]) -> bool:
    changed = False
    for name in list(files):
        if not name.endswith(".rels"):
            continue
        dom, relationships = _relationship_elements(files[name], name)
        removed = False
        for rel in relationships:
            if (
                rel.getAttribute("Type").rstrip("/").endswith("/printerSettings")
                and rel.parentNode is not None
            ):
                rel.parentNode.removeChild(rel)
                removed = True
        if removed:
            files[name] = dom.toxml(encoding="UTF-8")
            changed = True
    return changed


def _repair_content_types(files: dict[str, bytes], removed_parts: set[str]) -> bool:
    if CONTENT_TYPES not in files:
        raise SanitizeError(f"{CONTENT_TYPES} is missing")

    dom = _dom(files[CONTENT_TYPES], CONTENT_TYPES)
    root = dom.documentElement
    changed = False

    overrides: dict[str, object] = {}
    for override in list(dom.getElementsByTagName("Override")):
        part = override.getAttribute("PartName").lstrip("/")
        if part in removed_parts:
            if override.parentNode is not None:
                override.parentNode.removeChild(override)
                changed = True
            continue
        overrides[part.lower()] = override

    ole_targets = {
        target.lower(): target
        for target in _targets_for_relationship(files, "/oleObject")
        if target.lower().endswith(".bin")
    }
    remaining_bin = {name.lower() for name in files if name.lower().endswith(".bin")}
    for normalized in sorted(set(ole_targets) - set(overrides)):
        target = ole_targets[normalized]
        override = dom.createElement("Override")
        override.setAttribute("PartName", "/" + target)
        override.setAttribute("ContentType", OLE_OBJECT_CONTENT_TYPE)
        root.appendChild(override)
        overrides[normalized] = override
        changed = True

    printer_defaults = [
        node
        for node in dom.getElementsByTagName("Default")
        if node.getAttribute("Extension").lower() == "bin"
        and node.getAttribute("ContentType") == PRINTER_SETTINGS_CONTENT_TYPE
    ]
    if printer_defaults:
        undeclared = sorted(remaining_bin - set(overrides))
        if undeclared:
            raise SanitizeError(
                "cannot remove the printer-settings .bin default because these "
                "remaining parts have no specific content type: "
                + ", ".join(undeclared)
            )
        for default in printer_defaults:
            if default.parentNode is not None:
                default.parentNode.removeChild(default)
                changed = True

    if changed:
        files[CONTENT_TYPES] = dom.toxml(encoding="UTF-8")
    return changed


def sanitize_entries(files: Mapping[str, bytes]) -> tuple[dict[str, bytes], list[str]]:
    """Return a repaired package map and a list of applied changes."""
    repaired = dict(files)
    missing = [
        name
        for name in (PRESENTATION, PRESENTATION_RELS, CONTENT_TYPES)
        if name not in repaired
    ]
    if missing:
        raise SanitizeError(
            "not a complete PPTX package; missing " + ", ".join(missing)
        )

    changes: list[str] = []
    presentation_xml = part_text(repaired[PRESENTATION])
    presentation_xml, slide_size_changed = _patch_slide_size(presentation_xml)
    if slide_size_changed:
        changes.append("normalized slide size metadata")
    presentation_xml, notes_changed = _add_notes_master_id(
        presentation_xml, repaired[PRESENTATION_RELS]
    )
    if notes_changed:
        changes.append("registered the notes master")
    repaired[PRESENTATION] = presentation_xml.encode("utf-8", "surrogateescape")

    removed_parts = {
        name for name in repaired if name.startswith("ppt/printerSettings/")
    }
    for name in removed_parts:
        del repaired[name]
    rels_changed = _remove_printer_relationships(repaired)
    content_types_changed = _repair_content_types(repaired, removed_parts)
    if removed_parts or rels_changed or content_types_changed:
        changes.append("removed Windows printer settings safely")

    return repaired, changes


def _write_atomic(
    path: Path,
    original_infos: list[zipfile.ZipInfo],
    repaired: Mapping[str, bytes],
) -> None:
    fd, temp_name = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=path.parent
    )
    temp_path = Path(temp_name)
    try:
        with os.fdopen(fd, "wb") as handle:
            with zipfile.ZipFile(handle, "w") as output:
                for info in original_infos:
                    if info.filename in repaired:
                        output.writestr(info, repaired[info.filename])
            handle.flush()
            os.fsync(handle.fileno())
        with zipfile.ZipFile(temp_path, "r") as check:
            bad_part = check.testzip()
            if bad_part is not None:
                raise SanitizeError(f"rewritten package failed CRC check at {bad_part}")
        os.chmod(temp_path, path.stat().st_mode & 0o777)
        os.replace(temp_path, path)
    finally:
        if temp_path.exists():
            temp_path.unlink()


def sanitize_file(path: str | Path) -> list[str]:
    """Repair a PPTX in place, atomically, and return the applied changes."""
    target = Path(path).expanduser().resolve()
    if not target.is_file():
        raise SanitizeError(f"{target} is not a file")
    if target.suffix.lower() != ".pptx":
        raise SanitizeError(f"{target} is not a .pptx file")

    try:
        with zipfile.ZipFile(target, "r") as archive:
            infos = archive.infolist()
            names = [info.filename for info in infos]
            if len(names) != len(set(names)):
                raise SanitizeError("package contains duplicate part names")
            files = {info.filename: archive.read(info) for info in infos}
    except zipfile.BadZipFile as exc:
        raise SanitizeError(f"cannot open {target} as a PPTX: {exc}") from exc

    repaired, changes = sanitize_entries(files)
    if changes:
        _write_atomic(target, infos, repaired)
    return changes
