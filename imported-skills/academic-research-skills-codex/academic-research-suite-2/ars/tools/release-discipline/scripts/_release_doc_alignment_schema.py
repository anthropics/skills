"""Manifest schema loading and validation.

Cross-repo agnostic per INVARIANT 12. No domain assumptions, no language
literals (INVARIANT 3, 20). Pure schema + path safety logic; no network,
no file writes (INVARIANT 4, 17).
"""

from __future__ import annotations

import json
import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class ManifestError(Exception):
    kind: str
    message: str
    field: str | None = None
    reason: str | None = None

    def __str__(self) -> str:
        base = f"{self.kind}: {self.message}"
        if self.field:
            base += f" (field={self.field})"
        if self.reason:
            base += f" (reason={self.reason})"
        return base


def _load_manifest_toml(manifest_path: Path) -> dict[str, Any]:
    """Existence + TOML-decode prongs of manifest loading (shared by both
    validators' loaders)."""
    if not manifest_path.exists():
        raise ManifestError(
            kind="manifest_not_found",
            message=f"manifest file not found: {manifest_path}",
        )
    try:
        with open(manifest_path, "rb") as fh:
            return tomllib.load(fh)
    except tomllib.TOMLDecodeError as exc:
        raise ManifestError(
            kind="manifest_invalid_toml",
            message=f"manifest is not valid TOML: {exc}",
        ) from exc


def load_manifest(manifest_path: Path) -> dict[str, Any]:
    """Load and minimally validate the manifest TOML.

    Raises ManifestError with .kind set per §10 failure catalog.
    """
    manifest_path = Path(manifest_path)
    data = _load_manifest_toml(manifest_path)

    _check_unknown_keys(data)
    _check_value_types(data)
    _check_package_schema(data)
    _check_file_entries(data)
    _check_package_uniqueness(data)

    if "changelog_path" not in data:
        raise ManifestError(
            kind="manifest_required_field_missing",
            message="manifest missing required field: changelog_path",
            field="changelog_path",
        )

    _check_all_paths(data, manifest_path)
    _check_all_templates(data)
    _check_scanner_markers(data)
    _check_changelog_pattern(data)
    _check_pattern_against_comment_marker(data)

    return data


# Allow-list of top-level keys + per-section keys. Per INVARIANT 14, any key
# outside these is a hard error. Ordered tuples (not sets) so that key-driven
# validation loops raise deterministically (INVARIANT 4) and so the same
# catalog drives both _check_unknown_keys and _check_value_types — a key added
# here is automatically type-checked.
_TOP_LEVEL_KEYS: tuple[str, ...] = (
    "changelog_path",
    "changelog_entry_pattern",
    "suite",
    "changelog",
    "file",
    "package",
)
_SUITE_KEYS: tuple[str, ...] = ("latest", "latest_date")
_SCANNER_MARKER_KEYS: tuple[str, ...] = (
    "fence_marker",
    "comment_open",
    "comment_close",
)
_CHANGELOG_KEYS: tuple[str, ...] = _SCANNER_MARKER_KEYS + ("near_miss_whitelist",)
_FILE_KEYS: tuple[str, ...] = (
    "path",
    "release_block_form",
    "badge_template",
    "tag_url_template",
    "last_updated_template",
)
_PACKAGE_KEYS: tuple[str, ...] = ("path", "type", "key", "pattern")


_VALID_PACKAGE_TYPES: set[str] = {"toml", "json", "regex"}

_TEMPLATE_FIELDS: tuple[str, ...] = (
    "release_block_form",
    "badge_template",
    "tag_url_template",
    "last_updated_template",
)

_TEMPLATE_VAR_RE = re.compile(r"\{([^{}]*)\}")
_ALLOWED_VARS: frozenset[str] = frozenset({"version", "date"})


def _check_template_format(template: str, *, field: str) -> None:
    """Raise ManifestError(template_format_error) if template has unknown vars
    or unclosed braces. Allowed: {version}, {date}; any other {...} fails.
    Caller must guarantee template is not None (see _check_all_templates).
    """
    # Quick unbalanced-brace check: count { vs } and matched pairs via the regex.
    opens = template.count("{")
    closes = template.count("}")
    if opens != closes:
        raise ManifestError(
            kind="template_format_error",
            message=f"template has unbalanced braces: {template!r}",
            field=field,
        )
    for match in _TEMPLATE_VAR_RE.finditer(template):
        name = match.group(1)
        if name not in _ALLOWED_VARS:
            raise ManifestError(
                kind="template_format_error",
                message=f"template uses unknown variable {{{name}}}: {template!r}",
                field=field,
            )


def _require_str(value: Any, *, field: str) -> None:
    if value is not None and not isinstance(value, str):
        raise ManifestError(
            kind="manifest_invalid_type",
            message=f"{field} must be a string, got {type(value).__name__}",
            field=field,
        )


def _check_value_types(data: dict[str, Any]) -> None:
    """Validate scalar value types for known keys (manifest_invalid_type).

    Must run after _check_unknown_keys (which guarantees section/entry
    container shapes) and before every other check: downstream code assumes
    correct Python types, so a wrong-typed TOML value (e.g. a float where a
    version string is expected) would otherwise surface as an uncaught
    TypeError/AttributeError deep inside a check instead of a structured error.

    Driven by the same key catalogs as _check_unknown_keys; every known key is
    a string except changelog.near_miss_whitelist (array of strings).
    """
    _require_str(data.get("changelog_path"), field="changelog_path")
    _require_str(data.get("changelog_entry_pattern"), field="changelog_entry_pattern")

    suite = data.get("suite") or {}
    for key in _SUITE_KEYS:
        _require_str(suite.get(key), field=f"suite.{key}")

    cs = data.get("changelog") or {}
    for key in _SCANNER_MARKER_KEYS:
        _require_str(cs.get(key), field=f"changelog.{key}")
    whitelist = cs.get("near_miss_whitelist")
    if whitelist is not None:
        if not isinstance(whitelist, list) or any(
            not isinstance(item, str) for item in whitelist
        ):
            raise ManifestError(
                kind="manifest_invalid_type",
                message="changelog.near_miss_whitelist must be an array of strings",
                field="changelog.near_miss_whitelist",
            )

    for idx, entry in enumerate(data.get("file", [])):
        for key in _FILE_KEYS:
            _require_str(entry.get(key), field=f"file[{idx}].{key}")

    for idx, entry in enumerate(data.get("package", [])):
        for key in _PACKAGE_KEYS:
            _require_str(entry.get(key), field=f"package[{idx}].{key}")


def _check_all_templates(data: dict[str, Any]) -> None:
    """Validate all template fields in [[file]] entries (INVARIANT 21)."""
    for idx, entry in enumerate(data.get("file", [])):
        for tf in _TEMPLATE_FIELDS:
            value = entry.get(tf)
            if value is not None:
                _check_template_format(value, field=f"file[{idx}].{tf}")


_DEFAULT_CHANGELOG: dict[str, Any] = {
    "fence_marker": "```",
    "comment_open": "<!--",
    "comment_close": "-->",
    "near_miss_whitelist": ["Unreleased", "unreleased", "TBD", "Pending"],
}
_DEFAULT_CHANGELOG_PATTERN: str = (
    r"^## \[(?P<version>\S+)\] - (?P<date>\d{4}-\d{2}-\d{2})\s*$"
)


def changelog_settings(data: dict[str, Any]) -> dict[str, Any]:
    """Return effective changelog settings (defaults merged with manifest overrides).

    Caller should pass the dict returned by load_manifest (validated). Returned
    dict is a deep-enough copy that mutating the result (incl. the
    near_miss_whitelist list) does NOT poison the module-level _DEFAULT_CHANGELOG.
    """
    settings = dict(_DEFAULT_CHANGELOG)
    settings["near_miss_whitelist"] = list(settings["near_miss_whitelist"])
    settings.update(data.get("changelog") or {})
    return settings


def _check_regex(
    pattern_text: str,
    *,
    required_groups: tuple[str, ...],
    kind_invalid: str,
    kind_missing: str,
    field: str,
) -> None:
    """Validate that a manifest-declared regex compiles (re.MULTILINE) and
    contains all required named groups. Shared by the changelog-pattern and
    package-pattern checks so both fail at manifest-parse with their
    respective §10 kinds."""
    try:
        compiled = re.compile(pattern_text, re.MULTILINE)
    except re.error as exc:
        raise ManifestError(
            kind=kind_invalid,
            message=f"{field} does not compile: {exc}",
            field=field,
        ) from exc
    missing = [g for g in required_groups if g not in compiled.groupindex]
    if missing:
        raise ManifestError(
            kind=kind_missing,
            message=f"{field} must contain named group(s): {', '.join(missing)}",
            field=field,
        )


def _check_changelog_pattern(data: dict[str, Any]) -> None:
    """Validate an explicit changelog_entry_pattern at manifest-parse time.

    The default pattern (used when the key is absent) is known-good, so only
    a manifest-declared override is checked."""
    pattern_text = data.get("changelog_entry_pattern")
    if pattern_text is None:
        return
    _check_regex(
        pattern_text,
        required_groups=("version", "date"),
        kind_invalid="changelog_regex_invalid",
        kind_missing="changelog_regex_missing_groups",
        field="changelog_entry_pattern",
    )


def _check_scanner_markers(data: dict[str, Any]) -> None:
    cs = data.get("changelog") or {}
    for name in _SCANNER_MARKER_KEYS:
        if name in cs and cs[name] == "":
            raise ManifestError(
                kind=f"{name}_empty",
                message=f"[changelog].{name} must not be empty",
                field=f"changelog.{name}",
            )


def _check_pattern_against_comment_marker(data: dict[str, Any]) -> None:
    pattern = data.get("changelog_entry_pattern") or _DEFAULT_CHANGELOG_PATTERN
    cs = changelog_settings(data)
    for marker_field in ("comment_open", "comment_close"):
        if cs[marker_field] in pattern:
            raise ManifestError(
                kind="changelog_pattern_uses_comment_marker",
                message=(
                    f"changelog_entry_pattern contains {marker_field} literal "
                    f"({cs[marker_field]!r}); scanner strips comments before matching, "
                    f"so this pattern would never match"
                ),
                field="changelog_entry_pattern",
            )


def render_template(template: str, *, version: str, date: str | None) -> str | None:
    """Render a template with {version}/{date} substitutions.

    Returns None if the template references {date} but date is None — callers
    should emit a WARN (template_uses_date_but_date_unavailable) and skip the
    check per INVARIANT 21 + §10.
    """
    if "{date}" in template and date is None:
        return None
    return template.replace("{version}", version).replace("{date}", date or "")


def _check_path_shape(declared: str, *, field: str) -> Path:
    """Filesystem-free path-shape prongs of INVARIANT 13: non-empty, relative,
    no '..' segments. Returns Path(declared). Shared by single-file path
    validation (_check_path, which adds resolve/exists checks) and glob-pattern
    validation (shape only — a glob is not a single existing file)."""
    if declared is None or declared == "":
        raise ManifestError(
            kind="path_unsafe",
            message=f"path is empty for field {field}",
            field=field,
            reason="empty",
        )

    raw = Path(declared)
    if raw.is_absolute():
        raise ManifestError(
            kind="path_unsafe",
            message=f"path is absolute: {declared}",
            field=field,
            reason="absolute",
        )

    if ".." in raw.parts:
        raise ManifestError(
            kind="path_unsafe",
            message=f"path contains '..': {declared}",
            field=field,
            reason="traversal",
        )
    return raw


def _check_path(declared: str, *, field: str, manifest_parent: Path) -> Path:
    """Validate a single manifest-declared path.

    Returns the resolved Path on success. Raises ManifestError(kind="path_unsafe")
    with reason sub-field on failure, per INVARIANT 13.
    """
    raw = _check_path_shape(declared, field=field)

    parent_resolved = manifest_parent.resolve()
    candidate = (manifest_parent / raw).resolve()
    try:
        candidate.relative_to(parent_resolved)
    except ValueError:
        raise ManifestError(
            kind="path_unsafe",
            message=f"path resolves outside manifest parent: {declared} -> {candidate}",
            field=field,
            reason="symlink_escape",
        ) from None

    if not candidate.exists():
        raise ManifestError(
            kind="path_unsafe",
            message=f"path does not exist: {declared} (resolved to {candidate})",
            field=field,
            reason="not_found",
        )
    if candidate.is_dir():
        raise ManifestError(
            kind="path_unsafe",
            message=f"path is a directory, expected file: {declared}",
            field=field,
            reason="directory",
        )

    return candidate


def _check_all_paths(data: dict[str, Any], manifest_path: Path) -> None:
    """Validate all declared paths in the manifest (INVARIANT 13)."""
    parent = manifest_path.parent
    _check_path(data["changelog_path"], field="changelog_path", manifest_parent=parent)
    for idx, entry in enumerate(data.get("file", [])):
        _check_path(entry.get("path"), field=f"file[{idx}].path", manifest_parent=parent)
    for idx, entry in enumerate(data.get("package", [])):
        _check_path(entry.get("path"), field=f"package[{idx}].path", manifest_parent=parent)


def _check_file_entries(data: dict[str, Any]) -> None:
    """Raise ManifestError for missing path, empty, or duplicate [[file]] entries (INVARIANT 15)."""
    seen: set[str] = set()
    for idx, entry in enumerate(data.get("file", [])):
        path = entry.get("path")
        if path is None:
            raise ManifestError(
                kind="file_field_missing",
                message=f"[[file]] entry {idx} missing required field: path",
                field=f"file[{idx}].path",
            )
        if not any(entry.get(f) for f in _TEMPLATE_FIELDS):
            raise ManifestError(
                kind="empty_file_entry",
                message=(
                    f"[[file]] entry {idx} (path={path!r}) has no template fields. "
                    f"At least one of {list(_TEMPLATE_FIELDS)} must be set."
                ),
                field=f"file[{idx}]",
            )
        if path in seen:
            raise ManifestError(
                kind="duplicate_file_path",
                message=f"[[file]] path appears more than once: {path}",
                field=f"file[{idx}].path",
            )
        seen.add(path)


def _check_package_uniqueness(data: dict[str, Any]) -> None:
    """Raise ManifestError for duplicate [[package]] paths (INVARIANT 15)."""
    seen: set[str | None] = set()
    for idx, entry in enumerate(data.get("package", [])):
        path = entry.get("path")
        if path in seen:
            raise ManifestError(
                kind="duplicate_package_path",
                message=f"[[package]] path appears more than once: {path}",
                field=f"package[{idx}].path",
            )
        seen.add(path)


def _check_package_schema(data: dict[str, Any]) -> None:
    """Validate type discriminator and field exclusivity for [[package]] entries."""
    for idx, entry in enumerate(data.get("package", [])):
        if entry.get("path") is None:
            raise ManifestError(
                kind="package_field_missing",
                message=f"[[package]] entry {idx} missing required field: path",
                field=f"package[{idx}].path",
            )
        ptype = entry.get("type")
        if ptype is None:
            raise ManifestError(
                kind="package_field_missing",
                message=f"[[package]] entry {idx} missing required field: type",
                field=f"package[{idx}].type",
            )
        if ptype not in _VALID_PACKAGE_TYPES:
            raise ManifestError(
                kind="package_type_invalid",
                message=f"[[package]] entry {idx} type must be one of {sorted(_VALID_PACKAGE_TYPES)}, got: {ptype}",
                field=f"package[{idx}].type",
            )
        has_key = "key" in entry
        has_pattern = "pattern" in entry
        if ptype in ("toml", "json"):
            if not has_key:
                raise ManifestError(
                    kind="package_field_missing",
                    message=f'[[package]] entry {idx} with type="{ptype}" requires "key"',
                    field=f"package[{idx}].key",
                )
            if has_pattern:
                raise ManifestError(
                    kind="package_field_conflict",
                    message=f'[[package]] entry {idx} with type="{ptype}" must not set "pattern"',
                    field=f"package[{idx}].pattern",
                )
        elif ptype == "regex":
            if not has_pattern:
                raise ManifestError(
                    kind="package_field_missing",
                    message=f'[[package]] entry {idx} with type="regex" requires "pattern"',
                    field=f"package[{idx}].pattern",
                )
            if has_key:
                raise ManifestError(
                    kind="package_field_conflict",
                    message=f'[[package]] entry {idx} with type="regex" must not set "key"',
                    field=f"package[{idx}].key",
                )
            _check_regex(
                entry["pattern"],
                required_groups=("version",),
                kind_invalid="package_pattern_invalid",
                kind_missing="package_pattern_missing_group",
                field=f"package[{idx}].pattern",
            )


_BARE_VERSION_RE = re.compile(r"^\d+(?:\.\d+)+(?:[-.\s]|$)")


@dataclass
class ScannerError(Exception):
    kind: str
    message: str
    line_num: int | None = None
    line: str | None = None
    lines: list[int] = field(default_factory=list)

    def __str__(self) -> str:
        return f"{self.kind}: {self.message}"


def _strip_inline_comments(line: str, opener: str, closer: str) -> str:
    while True:
        start = line.find(opener)
        if start < 0:
            return line
        end = line.find(closer, start + len(opener))
        if end < 0:
            return line
        line = line[:start] + line[end + len(closer):]


def _comment_still_open(line: str, opener: str, closer: str) -> bool:
    last_open = line.rfind(opener)
    last_close = line.rfind(closer)
    return last_open >= 0 and last_open > last_close


def _is_release_like_heading(line: str, whitelist: list[str]) -> bool:
    s = line.lstrip()
    if not s.startswith("## "):
        return False
    rest = s[3:].strip()
    for label in whitelist:
        if rest.startswith(label) or rest.startswith(f"[{label}]"):
            return False
    has_bracket = "[" in rest and "]" in rest
    has_bare_version = bool(_BARE_VERSION_RE.match(rest))
    return has_bracket or has_bare_version


def scan_changelog(text: str, *, pattern: re.Pattern[str], fence_marker: str, comment_open: str,
                   comment_close: str, near_miss_whitelist: list[str]) -> list[dict[str, Any]]:
    """Per §8: state-aware fence + comment scanner. Returns parsed entries.

    Raises ScannerError on duplicate_version or near_miss_heading.
    """
    # INVARIANT 19: BOM strip + CRLF normalize.
    text = text.lstrip("﻿").replace("\r\n", "\n").replace("\r", "\n")

    NORMAL = "NORMAL"
    IN_FENCE = "IN_FENCE"
    IN_COMMENT_BLOCK = "IN_COMMENT_BLOCK"
    state = NORMAL

    entries: list[dict[str, Any]] = []
    seen: dict[str, int] = {}

    for line_num, line in enumerate(text.split("\n"), start=1):
        if state == IN_FENCE:
            if line.lstrip().startswith(fence_marker):
                state = NORMAL
            continue
        if state == IN_COMMENT_BLOCK:
            if comment_close in line:
                state = NORMAL
            continue

        if line.lstrip().startswith(fence_marker):
            state = IN_FENCE
            continue

        stripped = _strip_inline_comments(line, comment_open, comment_close)
        if _comment_still_open(stripped, comment_open, comment_close):
            stripped = stripped[:stripped.rindex(comment_open)].rstrip()
            state = IN_COMMENT_BLOCK

        m = pattern.match(stripped)
        if m:
            version = m.group("version")
            date = m.group("date")
            if version in seen:
                raise ScannerError(
                    kind="changelog_duplicate_version",
                    message=f"version {version!r} appears at lines {seen[version]} and {line_num}",
                    lines=[seen[version], line_num],
                )
            seen[version] = line_num
            entries.append({"version": version, "date": date, "line_num": line_num})
        elif _is_release_like_heading(stripped, near_miss_whitelist):
            raise ScannerError(
                kind="changelog_near_miss_heading",
                message=f"line looks like a release heading but did not match pattern: {stripped!r}",
                line_num=line_num,
                line=stripped,
            )

    return entries


def scan_changelog_file(
    path: Path,
    *,
    pattern: re.Pattern[str],
    fence_marker: str,
    comment_open: str,
    comment_close: str,
    near_miss_whitelist: list[str],
) -> list[dict[str, Any]]:
    """Read a CHANGELOG file and scan it — the shared read/decode/empty
    failure semantics for both validators.

    Raises ScannerError with kind ``changelog_decode_error`` (file is not
    valid UTF-8) or ``changelog_empty_after_scan`` (pattern matched zero
    entries), in addition to the scanner's own kinds.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise ScannerError(
            kind="changelog_decode_error",
            message=f"CHANGELOG is not valid UTF-8: {exc}",
        ) from exc
    entries = scan_changelog(
        text,
        pattern=pattern,
        fence_marker=fence_marker,
        comment_open=comment_open,
        comment_close=comment_close,
        near_miss_whitelist=near_miss_whitelist,
    )
    if not entries:
        raise ScannerError(
            kind="changelog_empty_after_scan",
            message=f"changelog_entry_pattern matched zero entries in {path}",
        )
    return entries


def _check_unknown_keys(data: dict[str, Any]) -> None:
    """Raise ManifestError for any key not in the allow-list (INVARIANT 14)."""
    for key in data:
        if key not in _TOP_LEVEL_KEYS:
            raise ManifestError(
                kind="unknown_manifest_key",
                message=f"unknown top-level key: {key}",
                field=key,
            )

    for section_name, allowed in (("suite", _SUITE_KEYS), ("changelog", _CHANGELOG_KEYS)):
        section = data.get(section_name)
        if section is None:
            continue
        if not isinstance(section, dict):
            raise ManifestError(
                kind="manifest_invalid_type",
                message=f"[{section_name}] must be a table",
                field=section_name,
            )
        for key in section:
            if key not in allowed:
                raise ManifestError(
                    kind="unknown_manifest_key",
                    message=f"unknown key in [{section_name}]: {key}",
                    field=f"{section_name}.{key}",
                )

    for kind, allowed in (("file", _FILE_KEYS), ("package", _PACKAGE_KEYS)):
        entries = data.get(kind, [])
        if not isinstance(entries, list):
            raise ManifestError(
                kind="manifest_invalid_type",
                message=f"[[{kind}]] must be an array of tables",
                field=kind,
            )
        for idx, entry in enumerate(entries):
            if not isinstance(entry, dict):
                raise ManifestError(
                    kind="manifest_invalid_type",
                    message=f"[[{kind}]] entry {idx} must be a table",
                    field=f"{kind}[{idx}]",
                )
            for key in entry:
                if key not in allowed:
                    raise ManifestError(
                        kind="unknown_manifest_key",
                        message=f"unknown key in [[{kind}]] entry {idx}: {key}",
                        field=f"{kind}[{idx}].{key}",
                    )


# ---------------------------------------------------------------------------
# Package version extractors
# ---------------------------------------------------------------------------


@dataclass
class PackageError(Exception):
    """Raised when a package version cannot be extracted from a declared file.

    Attributes:
        kind: machine-readable failure code per §10 failure catalog.
        message: human-readable explanation.
        path: resolved file path as a string, or None if not applicable.
    """

    kind: str
    message: str
    path: str | None = None

    def __str__(self) -> str:
        return f"{self.kind}: {self.message}"


def _walk_dotted(obj: Any, key: str) -> Any:
    """Walk a dotted key path into a nested dict.

    Returns the value at the terminal node, or None if any segment is
    missing or the current node is not a dict.
    """
    cur = obj
    for part in key.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return None
        cur = cur[part]
    return cur


def extract_package_version(
    path: Path,
    *,
    ptype: str,
    key: str | None,
    pattern: str | None,
) -> str:
    """Extract a version string from a declared package metadata file.

    Supported types:
    - ``"toml"``: reads via tomllib, walks ``key`` (dotted notation).
    - ``"json"``: reads via json.loads, walks ``key`` (dotted notation).
    - ``"regex"``: compiles ``pattern`` with re.MULTILINE, requires named group
      ``version``; exactly one match required.

    Returns the extracted version string on success.

    Raises:
        PackageError(kind="package_decode_error"): file is not valid UTF-8.
        PackageError(kind="package_version_unparseable"): key not found, not
            a string, or zero regex matches.
        PackageError(kind="package_version_ambiguous"): regex matched more
            than one line (hard error per spec §10).
        PackageError(kind="package_type_invalid"): ``ptype`` is not one of the
            three supported values.

    Precondition: when ptype in {"toml", "json"}, key must be a non-empty string;
    when ptype == "regex", pattern must be a valid regex with named group
    ``version``. Schema validation in load_manifest() enforces this for
    manifest-derived calls.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise PackageError(
            kind="package_decode_error",
            message=f"package file is not valid UTF-8: {path}: {exc}",
            path=str(path),
        ) from exc

    if ptype == "toml":
        try:
            data = tomllib.loads(text)
        except tomllib.TOMLDecodeError as exc:
            raise PackageError(
                kind="package_version_unparseable",
                message=f"TOML decode error in {path}: {exc}",
                path=str(path),
            ) from exc
        value = _walk_dotted(data, key)
        if not isinstance(value, str):
            raise PackageError(
                kind="package_version_unparseable",
                message=f"TOML key {key!r} not found or not a string in {path}",
                path=str(path),
            )
        return value

    if ptype == "json":
        try:
            data = json.loads(text)
        except json.JSONDecodeError as exc:
            raise PackageError(
                kind="package_version_unparseable",
                message=f"JSON decode error in {path}: {exc}",
                path=str(path),
            ) from exc
        value = _walk_dotted(data, key)
        if not isinstance(value, str):
            raise PackageError(
                kind="package_version_unparseable",
                message=f"JSON key {key!r} not found or not a string in {path}",
                path=str(path),
            )
        return value

    if ptype == "regex":
        compiled = re.compile(pattern, re.MULTILINE)
        matches = list(compiled.finditer(text))
        if len(matches) == 0:
            raise PackageError(
                kind="package_version_unparseable",
                message=f"regex pattern matched zero lines in {path}",
                path=str(path),
            )
        if len(matches) > 1:
            raise PackageError(
                kind="package_version_ambiguous",
                message=(
                    f"regex pattern matched {len(matches)} lines in {path}"
                    " (expected exactly 1)"
                ),
                path=str(path),
            )
        # Named group presence is a precondition (validated at manifest-parse
        # by _check_regex for manifest-derived calls).
        return matches[0].group("version")

    raise PackageError(
        kind="package_type_invalid",
        message=f"unknown package type: {ptype!r}",
        path=str(path),
    )


# ---------------------------------------------------------------------------
# Version resolution (§3 + INVARIANT 22)
# ---------------------------------------------------------------------------


@dataclass
class ResolutionResult:
    version: str
    date: str | None
    source: str  # "cli_flag" | "package" | "suite_fallback"
    warnings: list[str] = field(default_factory=list)


@dataclass
class ResolutionError(Exception):
    kind: str
    message: str
    detail: dict[str, Any] = field(default_factory=dict)

    def __str__(self) -> str:
        return f"{self.kind}: {self.message}"


def resolve_authoritative_version(
    *,
    manifest: dict[str, Any],
    manifest_parent: Path,
    expected_version: str | None,
    ci: bool,
) -> ResolutionResult:
    """Per §3 + INVARIANT 22.

    Order:
      1. --expected-version wins (source=cli_flag)
      2. [[package]] non-empty: all packages must agree (INVARIANT 22)
      3. [suite].latest (only if --ci NOT set)
      4. fail

    Returns:
        ResolutionResult with source in {"cli_flag", "package", "suite_fallback"}.

    Raises:
        ResolutionError with kind in {"packages_disagree",
            "version_resolution_failed_in_ci", "version_resolution_failed"}.
        PackageError (propagated from extract_package_version) when a declared
            package file cannot be parsed. Can only escape when
            expected_version is None (the CLI flag returns before any package
            file is read), so for the caller it is always the cascade path.
    """
    if expected_version is not None:
        return ResolutionResult(version=expected_version, date=None, source="cli_flag")

    packages = manifest.get("package") or []
    if packages:
        versions: list[tuple[str, str]] = []  # (path, version)
        for entry in packages:
            v = extract_package_version(
                manifest_parent / entry["path"],
                ptype=entry["type"],
                key=entry.get("key"),
                pattern=entry.get("pattern"),
            )
            versions.append((entry["path"], v))

        distinct = set(v for _, v in versions)
        if len(distinct) > 1:
            detail = ", ".join(f"{p}={v}" for p, v in versions)
            raise ResolutionError(
                kind="packages_disagree",
                message=f"declared packages report different versions: {detail}",
                detail={"versions": versions},
            )

        return ResolutionResult(version=versions[0][1], date=None, source="package")

    suite = manifest.get("suite") or {}
    if not ci and "latest" in suite:
        return ResolutionResult(
            version=suite["latest"],
            date=suite.get("latest_date"),
            source="suite_fallback",
            warnings=["suite_fallback_used"],
        )

    if ci:
        raise ResolutionError(
            kind="version_resolution_failed_in_ci",
            message="--ci mode requires --expected-version OR at least one [[package]] entry",
        )
    raise ResolutionError(
        kind="version_resolution_failed",
        message="no version source found: provide --expected-version, declare [[package]], or set [suite].latest",
    )


# ---------------------------------------------------------------------------
# Per-file check primitives (§7 + INVARIANT 21)
# ---------------------------------------------------------------------------


def _normalize(text: str) -> str:
    """Strip leading BOM and normalise line endings to LF."""
    return text.lstrip("﻿").replace("\r\n", "\n").replace("\r", "\n")


def check_release_block_presence(
    *,
    file_text: str,
    entries: list[dict[str, Any]],
    release_block_form: str,
) -> list[dict[str, Any]]:
    """Per INVARIANT 21: uses per-historical-entry version+date (not authoritative).

    Iterates each historical CHANGELOG entry and asserts that
    ``release_block_form`` (filled with that entry's version+date) appears in
    ``file_text``.

    Returns:
        List of check results, one per entry, each shaped::

            {"kind": "release_block_presence", "version": "<v>",
             "expected_needle": "<rendered>", "status": "pass" | "fail"}
    """
    text = _normalize(file_text)
    results: list[dict[str, Any]] = []
    for entry in entries:
        needle = release_block_form.replace("{version}", entry["version"]).replace(
            "{date}", entry["date"] or ""
        )
        results.append({
            "kind": "release_block_presence",
            "version": entry["version"],
            "expected_needle": needle,
            "status": "pass" if needle in text else "fail",
        })
    return results


def check_simple_template(
    *,
    file_text: str,
    template: str,
    authoritative_version: str,
    authoritative_date: str | None,
    kind: str,
) -> dict[str, Any]:
    """Needle check for badge_match / tag_url_match / last_updated_match.

    Composes the needle from ``template`` + authoritative version/date.
    Skips with ``reason="template_uses_date_but_date_unavailable"`` when
    the template references ``{date}`` but ``authoritative_date`` is None.

    Returns:
        Dict shaped::

            {"kind": <kind>, "status": "pass" | "fail" | "skip",
             "expected_needle": "<rendered>"}   # absent when status=="skip"

        When skipped, an additional key is present::

            {"reason": "template_uses_date_but_date_unavailable"}
    """
    rendered = render_template(template, version=authoritative_version, date=authoritative_date)
    if rendered is None:
        return {
            "kind": kind,
            "status": "skip",
            "reason": "template_uses_date_but_date_unavailable",
        }
    text = _normalize(file_text)
    return {
        "kind": kind,
        "expected_needle": rendered,
        "status": "pass" if rendered in text else "fail",
    }
