"""Materials knowledge validation engine.

Validates a figure-package against the materials knowledge graph
(`static/core/materials_kb.yaml`). Scans source_data CSV, figure_contract
markdown, and caption markdown for material claims that contradict the KB.

Exit codes:
    0 — passed (no errors; warnings allowed)
    1 — at least one error
    2 — package files missing or malformed
"""
import csv
import enum
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import yaml

KB_PATH = Path(__file__).resolve().parents[1] / "static" / "core" / "materials_kb.yaml"


# ---------------------------------------------------------------------------
# Aliases, tolerances, and unit hints (carried over from the original 790-line
# implementation so text-extracted claims and CSV-side phase names can be
# matched against the canonical KB names).
# ---------------------------------------------------------------------------

XRD_TOLERANCE_DEG = 0.5
FTIR_TOLERANCE_CM1 = 20
PERFORMANCE_TOLERANCE = 0.25  # fractional tolerance for single-value ranges

# Phase aliases -> canonical KB phase name. Longer aliases first so
# "t-ZrO2" matches before "ZrO2".
PHASE_ALIASES: list[tuple[str, str]] = [
    ("alpha-al2o3", "Al2O3 (alpha-corundum)"),
    ("α-al2o3", "Al2O3 (alpha-corundum)"),
    ("al2o3", "Al2O3 (alpha-corundum)"),
    ("corundum", "Al2O3 (alpha-corundum)"),
    ("alumina", "Al2O3 (alpha-corundum)"),
    ("t-zro2", "ZrO2 (tetragonal)"),
    ("tetragonal zro2", "ZrO2 (tetragonal)"),
    ("3y-tzp", "ZrO2 (tetragonal)"),
    ("m-zro2", "ZrO2 (monoclinic)"),
    ("monoclinic zro2", "ZrO2 (monoclinic)"),
    ("zro2", "ZrO2 (tetragonal)"),
    ("zirconia", "ZrO2 (tetragonal)"),
    ("8ysz", "8YSZ (cubic fluorite)"),
    ("ysz", "8YSZ (cubic fluorite)"),
    ("beta-sic", "SiC (3C, beta)"),
    ("3c-sic", "SiC (3C, beta)"),
    ("sic", "SiC (3C, beta)"),
    ("silicon carbide", "SiC (3C, beta)"),
    ("beta-si3n4", "Si3N4 (beta)"),
    ("si3n4", "Si3N4 (beta)"),
    ("silicon nitride", "Si3N4 (beta)"),
    ("ca(oh)2", "Ca(OH)2 (portlandite)"),
    ("portlandite", "Ca(OH)2 (portlandite)"),
    ("quartz", "Quartz (SiO2)"),
    ("sio2", "Quartz (SiO2)"),
    ("tio2 anatase", "TiO2 (anatase)"),
    ("anatase", "TiO2 (anatase)"),
    ("tio2 rutile", "TiO2 (rutile)"),
    ("rutile", "TiO2 (rutile)"),
    ("tio2", "TiO2 (anatase)"),
    ("fe2o3", "Fe2O3 (hematite)"),
    ("hematite", "Fe2O3 (hematite)"),
    ("caco3", "CaCO3 (calcite)"),
    ("calcite", "CaCO3 (calcite)"),
    ("mullite", "Mullite (3Al2O3·2SiO2)"),
]

# FTIR functional group keyword -> category for cross-checking claims.
FTIR_CATEGORIES: list[tuple[str, str]] = [
    ("oxirane", "epoxy"),
    ("epoxy", "epoxy"),
    ("c=o", "carbonyl"),
    ("carbonyl", "carbonyl"),
    ("ester", "carbonyl"),
    ("o-h", "hydroxyl"),
    ("hydroxyl", "hydroxyl"),
    ("oh stretch", "hydroxyl"),
    ("c-h", "methylene_ch"),
    ("ch2", "methylene_ch"),
    ("ch3", "methylene_ch"),
    ("methylene", "methylene_ch"),
    ("c-o-c", "ether"),
    ("ether", "ether"),
    ("c=c", "aromatic"),
    ("aromatic", "aromatic"),
    ("si-o-si", "silicate"),
    ("si-o", "silicate"),
    ("silicate", "silicate"),
    ("c-s-h", "csh"),
    ("csh", "csh"),
    ("so4", "sulfate"),
    ("sulfate", "sulfate"),
    ("ettringite", "sulfate"),
    ("co3", "carbonate"),
    ("carbonate", "carbonate"),
    ("calcite", "carbonate"),
    ("h-o-h", "water"),
    ("water", "water"),
    ("hydration", "water"),
]

# Performance property keywords -> KB property name.
PROPERTY_KEYWORDS: list[tuple[str, str]] = [
    ("flexural strength", "flexural_strength"),
    ("bending strength", "flexural_strength"),
    ("compressive strength", "compressive_strength"),
    ("elastic modulus", "elastic_modulus"),
    ("young's modulus", "elastic_modulus"),
    ("young modulus", "elastic_modulus"),
    ("thermal conductivity", "thermal_conductivity"),
    ("coefficient of thermal expansion", "CTE"),
    ("thermal expansion", "CTE"),
    ("cte", "CTE"),
    ("bond strength", "bond_strength"),
    ("bonding strength", "bond_strength"),
    ("weibull modulus", "weibull_modulus"),
    ("fracture strain", "fracture_strain"),
    ("strain at fracture", "fracture_strain"),
]

# Material aliases for performance claims -> KB material name.
MATERIAL_ALIASES: list[tuple[str, str]] = [
    ("3y-tzp zro2", "3Y-TZP ZrO2"),
    ("3y-tzp", "3Y-TZP ZrO2"),
    ("wer-ea modified", "WER-EA modified"),
    ("wer modified", "WER-EA modified"),
    ("wer-ea", "WER-EA modified"),
    ("asphalt-aggregate", "asphalt-aggregate"),
    ("asphalt aggregate", "asphalt-aggregate"),
    ("base asphalt", "asphalt-aggregate"),
    ("unmodified asphalt", "asphalt-aggregate"),
    ("portland cement", "Portland cement"),
    ("cement", "Portland cement"),
    ("al2o3", "Al2O3"),
    ("alumina", "Al2O3"),
    ("zro2", "ZrO2"),
    ("zirconia", "ZrO2"),
    ("sic", "SiC"),
    ("silicon carbide", "SiC"),
    ("si3n4", "Si3N4"),
    ("silicon nitride", "Si3N4"),
    ("ceramics", "ceramics"),
]

# Expected units for each property. A claim with a unit outside the allowed
# set triggers a ``unit_hint_mismatch`` warning.
PROPERTY_UNIT_HINTS: dict[str, set[str]] = {
    "flexural_strength": {"MPa", "GPa"},
    "compressive_strength": {"MPa"},
    "elastic_modulus": {"GPa"},
    "thermal_conductivity": {"W/mK", "W/m.K"},
    "CTE": {"/K", "1/K"},
    "bond_strength": {"MPa"},
    "weibull_modulus": {""},
    "fracture_strain": {"%"},
}

UNIT_ALIASES: dict[str, str] = {
    "W/m.K": "W/mK",
    "1/K": "/K",
}


# ---------------------------------------------------------------------------
# Alias resolution helpers
# ---------------------------------------------------------------------------

def resolve_phase_alias(phase_name: str) -> str | None:
    """Map a free-form phase name to its canonical KB name via PHASE_ALIASES.

    Returns the canonical name if a match is found, else ``None``. The
    longest matching alias wins so ``"t-ZrO2"`` is preferred over
    ``"ZrO2"``.
    """
    if not phase_name:
        return None
    lower = phase_name.lower().strip()
    # Direct canonical hit.
    for _, canonical in PHASE_ALIASES:
        if canonical.lower() == lower:
            return canonical
    # Alias hit.
    best: str | None = None
    best_len = -1
    for alias, canonical in PHASE_ALIASES:
        if alias in lower and len(alias) > best_len:
            best = canonical
            best_len = len(alias)
    return best


def normalise_unit(unit: str) -> str:
    """Return the canonical form of a unit (apply UNIT_ALIASES)."""
    u = (unit or "").strip()
    return UNIT_ALIASES.get(u, u)


def unit_is_allowed_for_property(prop_name: str, unit: str) -> bool:
    """Return whether a unit is acceptable for a parsed property claim."""

    allowed = PROPERTY_UNIT_HINTS.get(prop_name, set())
    normalised = normalise_unit(unit)
    if not allowed or normalised in allowed:
        return True
    if normalised in {"MPa", "GPa"} and allowed.intersection({"MPa", "GPa"}):
        return True
    return False


# ---------------------------------------------------------------------------
# Text parsing: split text into claim units and extract XRD/FTIR/performance
# claims from a figure_contract.md (carried over from the original 790-line
# implementation).
# ---------------------------------------------------------------------------

def split_units(text: str) -> list[str]:
    """Split text into claim units (sentences / list items / table rows)."""
    units: list[str] = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if "\t" in line or line.startswith("|") or line.startswith("- {"):
            units.append(line)
        else:
            for sent in re.split(r"[.;]\s+", line):
                sent = sent.strip()
                if sent:
                    units.append(sent)
    return units


def find_phases_in_text(text: str) -> list[tuple[str, int]]:
    """Find phase names in text. Returns [(canonical_phase, position), ...]."""
    results: list[tuple[str, int]] = []
    lower = text.lower()
    for alias, canonical in PHASE_ALIASES:
        for m in re.finditer(re.escape(alias), lower):
            results.append((canonical, m.start()))
    return results


def extract_xrd_claims(text: str) -> list[dict[str, Any]]:
    """Extract XRD peak claims: (2θ value, phase) pairs from text."""
    claims: list[dict[str, Any]] = []
    seen: set[tuple[float, str]] = set()

    for unit in split_units(text):
        theta_patterns = [
            r"(\d{1,2}\.\d{1,2})\s*°",
            r"2\s*[θθ]\s*[=:]\s*(\d{1,2}\.\d{1,2})",
        ]
        theta_matches: list[tuple[float, int]] = []
        for pat in theta_patterns:
            for m in re.finditer(pat, unit):
                theta_matches.append((float(m.group(1)), m.start()))

        if not theta_matches:
            continue

        phases = find_phases_in_text(unit)
        if not phases:
            continue

        for theta_val, theta_pos in theta_matches:
            nearest_phase = None
            min_dist = float("inf")
            for phase_name, phase_pos in phases:
                dist = abs(theta_pos - phase_pos)
                if dist < min_dist:
                    min_dist = dist
                    nearest_phase = phase_name

            key = (theta_val, nearest_phase or "")
            if key in seen:
                continue
            seen.add(key)

            claims.append({
                "two_theta": theta_val,
                "phase": nearest_phase,
                "context": unit[:200],
            })

    return claims


def find_ftir_groups_in_text(text: str) -> list[tuple[str, int]]:
    """Find functional group mentions in text."""
    results: list[tuple[str, int]] = []
    lower = text.lower()
    for alias, _ in FTIR_CATEGORIES:
        for m in re.finditer(re.escape(alias), lower):
            results.append((alias, m.start()))
    return results


def categorise_ftir(group_text: str) -> str | None:
    """Map a functional group text to a category via FTIR_CATEGORIES."""
    lower = group_text.lower()
    for alias, category in FTIR_CATEGORIES:
        if alias in lower:
            return category
    return None


def extract_ftir_claims(text: str) -> list[dict[str, Any]]:
    """Extract FTIR claims: (wavenumber, functional_group) pairs from text."""
    claims: list[dict[str, Any]] = []
    seen: set[tuple[int, str | None]] = set()

    for unit in split_units(text):
        wn_pattern = r"(\d{3,4})\s*cm\s*[-−‐⁻]?\s*[1¹]"
        wn_matches: list[tuple[int, int]] = []
        for m in re.finditer(wn_pattern, unit):
            wn_matches.append((int(m.group(1)), m.start()))

        if not wn_matches:
            continue

        groups = find_ftir_groups_in_text(unit)

        for wn_val, wn_pos in wn_matches:
            nearest_group: str | None = None
            min_dist = float("inf")
            for group_text, group_pos in groups:
                dist = abs(wn_pos - group_pos)
                if dist < min_dist:
                    min_dist = dist
                    nearest_group = group_text

            key = (wn_val, nearest_group)
            if key in seen:
                continue
            seen.add(key)

            claims.append({
                "wavenumber": wn_val,
                "functional_group": nearest_group,
                "context": unit[:200],
            })

    return claims


def find_materials_in_text(text: str) -> list[tuple[str, int]]:
    """Find material names in text. Returns [(canonical_material, position), ...]."""
    results: list[tuple[str, int]] = []
    lower = text.lower()
    for alias, canonical in MATERIAL_ALIASES:
        for m in re.finditer(re.escape(alias), lower):
            results.append((canonical, m.start()))
    return results


def find_properties_in_text(text: str) -> list[tuple[str, int]]:
    """Find property keywords in text. Uses word boundaries so 'cte' does not
    match inside 'characteristic'."""
    results: list[tuple[str, int]] = []
    lower = text.lower()
    for keyword, kb_prop in PROPERTY_KEYWORDS:
        for m in re.finditer(r"(?<!\w)" + re.escape(keyword) + r"(?!\w)", lower):
            results.append((kb_prop, m.start()))
    return results


def find_values_in_text(text: str) -> list[tuple[float, str, int]]:
    """Find numeric values with units. Returns [(value, unit, position), ...].

    The negative lookbehind ``(?<!\\w)`` excludes digits that are part of a
    chemical formula (e.g. the ``2`` and ``3`` in ``Al2O3``), which would
    otherwise be extracted as standalone numbers with an empty unit.
    """
    results: list[tuple[float, str, int]] = []
    pattern = r"(?<![\w])(\d+\.?\d*(?:e[-+]?\d+)?)\s*(MPa|GPa|W/mK|W/m\.K|/K|1/K|%|)"
    for m in re.finditer(pattern, text):
        val = float(m.group(1))
        unit = m.group(2).strip()
        results.append((val, unit, m.start()))
    return results


def extract_performance_claims(text: str) -> list[dict[str, Any]]:
    """Extract performance claims: (material, property, value, unit) from text.

    Uses proximity matching: for each property keyword found in a sentence,
    the nearest material and the nearest value (preferring values that follow
    the property) are paired with it.
    """
    claims: list[dict[str, Any]] = []
    seen: set[tuple[str, str, float]] = set()

    for unit in split_units(text):
        materials = find_materials_in_text(unit)
        if not materials:
            continue

        properties = find_properties_in_text(unit)
        if not properties:
            continue

        values = find_values_in_text(unit)
        if not values:
            continue

        for prop_name, prop_pos in properties:
            nearest_mat = min(
                materials, key=lambda mp: abs(prop_pos - mp[1])
            )[0]

            allowed_units = PROPERTY_UNIT_HINTS.get(prop_name, set())
            unit_matched_values = [
                (v, u, p)
                for v, u, p in values
                if unit_is_allowed_for_property(prop_name, u)
            ]
            candidate_values = unit_matched_values or values

            after = [(v, u, p) for v, u, p in candidate_values if p >= prop_pos]
            if after:
                nearest_val, nearest_unit, _ = min(
                    after, key=lambda vup: vup[2] - prop_pos
                )
            else:
                nearest_val, nearest_unit, _ = min(
                    candidate_values, key=lambda vup: prop_pos - vup[2]
                )

            key = (nearest_mat, prop_name, nearest_val)
            if key in seen:
                continue
            seen.add(key)

            claims.append({
                "material": nearest_mat,
                "property": prop_name,
                "value": nearest_val,
                "unit": nearest_unit,
                "context": unit[:200],
            })

    return claims


class Severity(str, enum.Enum):
    """Validation issue severity."""

    ERROR = "error"
    WARNING = "warning"


@dataclass
class ValidationIssue:
    """A single validation finding."""

    rule: str
    severity: Severity
    message: str
    row: int | None = None
    context: dict[str, Any] = field(default_factory=dict)


@dataclass
class ValidationReport:
    """Aggregated validation report for a figure package."""

    package: str
    errors: list[ValidationIssue] = field(default_factory=list)
    warnings: list[ValidationIssue] = field(default_factory=list)

    def add(self, issue: ValidationIssue) -> None:
        if issue.severity == Severity.ERROR:
            self.errors.append(issue)
        else:
            self.warnings.append(issue)

    def summary(self) -> str:
        return f"{len(self.errors)} errors, {len(self.warnings)} warnings"

    def exit_code(self) -> int:
        if any(i.rule == "package_files_missing" for i in self.errors):
            return 2
        if self.errors:
            return 1
        return 0


def _load_kb(kb_path: Path) -> dict[str, Any]:
    with kb_path.open(encoding="utf-8") as f:
        return yaml.safe_load(f) or {}


def load_kb(kb_path: Path) -> dict[str, Any]:
    """Compatibility wrapper for tests and small validation utilities."""

    return _load_kb(kb_path)


def validate_contract(text: str, kb: dict[str, Any]) -> dict[str, Any]:
    """Validate contract prose and return a compact compatibility report."""

    report = ValidationReport(package="<contract-text>")
    _check_contract_text(text, kb, report)
    issues = report.errors + report.warnings
    return {
        "status": "fail" if report.errors else "pass",
        "checks": [
            {
                "rule": issue.rule,
                "result": "error" if issue.severity == Severity.ERROR else "warning",
                "message": issue.message,
                "context": issue.context,
            }
            for issue in issues
        ] or [{"rule": "contract_text", "result": "confirmed"}],
    }


def _read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        return list(reader)


def _check_xrd_peak_phase(
    rows: list[dict[str, str]],
    kb: dict[str, Any],
    report: ValidationReport,
) -> None:
    """Verify declared XRD phase matches the peak positions in the KB.

    Phase names from the CSV are first passed through :func:`resolve_phase_alias`
    so that aliases like ``"alumina"`` resolve to the canonical
    ``"Al2O3 (alpha-corundum)"`` entry in the KB before the peak-position
    check is performed.
    """
    family_phases: dict[str, list[dict[str, Any]]] = {}
    for _family, payload in (kb.get("families") or {}).items():
        for entry in payload.get("xrd_peaks") or []:
            family_phases.setdefault(entry["phase"], []).append(entry)

    def _find_better_match(two_theta: float, exclude: str) -> str | None:
        for candidate, c_peaks in family_phases.items():
            if candidate == exclude:
                continue
            for cp in c_peaks:
                tol = float(cp.get("tolerance_deg", 0.5))
                if any(abs(two_theta - float(p)) <= tol for p in cp["peaks_2theta"]):
                    return candidate
        return None

    for idx, row in enumerate(rows, start=2):  # header is row 1
        if "phase" not in row or "two_theta" not in row:
            continue
        declared = row["phase"].strip()
        try:
            two_theta = float(row["two_theta"])
        except ValueError:
            continue
        # Prefer an exact match against the KB. Only fall back to alias
        # resolution when the declared phase is not directly present, so
        # we do not break figure packages that already use canonical
        # names like ``"t-ZrO2"``.
        if declared in family_phases:
            canonical = declared
        else:
            canonical = resolve_phase_alias(declared) or declared
        if canonical not in family_phases:
            # Declared phase not in KB: still flag if a 2θ match exists elsewhere.
            better = _find_better_match(two_theta, exclude=canonical)
            if better is not None:
                report.add(
                    ValidationIssue(
                        rule="xrd_peak_phase_mismatch",
                        severity=Severity.ERROR,
                        message=(
                            f"Declared phase '{declared}' does not match peak "
                            f"2θ={two_theta}; better match is '{better}'."
                        ),
                        row=idx,
                        context={
                            "declared": declared,
                            "expected_phase": better,
                            "two_theta": two_theta,
                        },
                    )
                )
            continue
        peaks = family_phases[canonical]
        if not peaks:
            continue
        first_phase = peaks[0]
        tolerance = float(first_phase.get("tolerance_deg", 0.5))
        expected = [float(p) for p in first_phase["peaks_2theta"]]
        if not any(abs(two_theta - e) <= tolerance for e in expected):
            better = _find_better_match(two_theta, exclude=canonical)
            if better is not None:
                report.add(
                    ValidationIssue(
                        rule="xrd_peak_phase_mismatch",
                        severity=Severity.ERROR,
                        message=(
                            f"Declared phase '{declared}' does not match peak "
                            f"2θ={two_theta}; better match is '{better}'."
                        ),
                        row=idx,
                        context={
                            "declared": declared,
                            "expected_phase": better,
                            "two_theta": two_theta,
                            "tolerance": tolerance,
                        },
                    )
                )


def _check_performance_range(
    rows: list[dict[str, str]],
    kb: dict[str, Any],
    report: ValidationReport,
) -> None:
    """Warn when a measured value falls outside the family's typical range."""
    name_to_range: dict[str, dict[str, Any]] = {}
    for _family, payload in (kb.get("families") or {}).items():
        for entry in payload.get("performance_ranges") or []:
            name_to_range[entry["name"]] = entry

    for idx, row in enumerate(rows, start=2):
        metric = row.get("metric", "").strip()
        if not metric or metric not in name_to_range:
            continue
        try:
            value = float(row["value"])
        except (ValueError, KeyError):
            continue
        entry = name_to_range[metric]
        lo = float(entry["typical_min"])
        hi = float(entry["typical_max"])
        threshold = float(entry.get("warning_threshold", 0.20))
        margin = (hi - lo) * threshold
        if value < lo - margin or value > hi + margin:
            report.add(
                ValidationIssue(
                    rule="performance_out_of_range",
                    severity=Severity.WARNING,
                    message=(
                        f"Metric '{metric}' value {value} is outside expected "
                        f"range [{lo}, {hi}] ±{threshold:.0%}."
                    ),
                    row=idx,
                    context={
                        "metric": metric,
                        "value": value,
                        "expected_range": [lo, hi],
                    },
                )
            )


def _check_ftir_wavenumber(
    rows: list[dict[str, str]],
    kb: dict[str, Any],
    report: ValidationReport,
) -> None:
    """Verify declared FTIR functional group matches the wavenumber in the KB.

    Looks for rows with a ``wavenumber`` column and a functional-group
    column (``functional_group`` / ``bond`` / ``assignment``). For each
    row, the script locates the KB bond entry within
    ``FTIR_TOLERANCE_CM1`` and compares its category to the declared
    group's category. A mismatch (e.g. claiming 915 cm⁻¹ as ``C=O`` when
    the KB puts 915 cm⁻¹ at the ``oxirane`` category) is reported as
    ``ftir_wavenumber_group_mismatch`` ERROR.
    """
    bond_columns = ("functional_group", "bond", "assignment", "group")
    # Build a flat list of (canonical_bond, wavenumber, tolerance) entries.
    bond_entries: list[tuple[str, float, float]] = []
    for _family, payload in (kb.get("families") or {}).items():
        for entry in payload.get("ftir_wavenumbers") or []:
            bond = entry.get("bond") or entry.get("functional_group")
            if not bond:
                continue
            tol = float(entry.get("tolerance", FTIR_TOLERANCE_CM1))
            for wn in entry.get("wavenumbers") or entry.get("peaks_cm1") or []:
                bond_entries.append((bond, float(wn), tol))

    if not bond_entries:
        return

    for idx, row in enumerate(rows, start=2):
        if "wavenumber" not in row:
            continue
        try:
            wn_val = float(row["wavenumber"])
        except ValueError:
            continue
        declared_group = ""
        for col in bond_columns:
            if col in row and row[col].strip():
                declared_group = row[col].strip()
                break
        if not declared_group:
            continue

        # Find any KB entry at this wavenumber.
        kb_at_wn: list[tuple[str, float]] = []
        for bond, kb_wn, tol in bond_entries:
            if abs(wn_val - kb_wn) <= tol:
                kb_at_wn.append((bond, kb_wn))

        if not kb_at_wn:
            # No KB entry close to this wavenumber; skip rather than error.
            continue

        declared_cat = categorise_ftir(declared_group)
        kb_categories = {
            categorise_ftir(bond) for bond, _ in kb_at_wn if categorise_ftir(bond)
        }
        # If categories match (or one side is uncategorisable) treat as pass.
        if declared_cat is None or not kb_categories or declared_cat in kb_categories:
            continue

        # Mismatch: declare a different category than the KB does.
        kb_bond_str = ", ".join(
            f"{b}@{int(w)}cm⁻¹" for b, w in kb_at_wn[:3]
        )
        report.add(
            ValidationIssue(
                rule="ftir_wavenumber_group_mismatch",
                severity=Severity.ERROR,
                message=(
                    f"Declared bond '{declared_group}' does not match "
                    f"wavenumber {int(wn_val)}cm⁻¹; KB assigns "
                    f"{kb_bond_str}."
                ),
                row=idx,
                context={
                    "declared_group": declared_group,
                    "declared_category": declared_cat,
                    "kb_categories": sorted(kb_categories),
                    "wavenumber": wn_val,
                },
            )
        )


def _check_unit_hint(
    rows: list[dict[str, str]],
    report: ValidationReport,
) -> None:
    """Warn when a performance row uses a unit outside the property's hint set.

    Metric / property names are first matched against ``PROPERTY_KEYWORDS``
    (via substring match, case-insensitive) to determine the canonical
    property. If the property has a hint set, the unit is checked. A unit
    outside the hint triggers ``unit_hint_mismatch`` WARNING.
    """
    for idx, row in enumerate(rows, start=2):
        metric = (row.get("metric") or row.get("property") or "").strip()
        if not metric:
            continue
        unit = (row.get("unit") or row.get("value_unit") or "").strip()
        if "value" not in row:
            continue
        # Identify the canonical property for this metric.
        prop_name: str | None = None
        for keyword, kb_prop in PROPERTY_KEYWORDS:
            if keyword in metric.lower():
                prop_name = kb_prop
                break
        if prop_name is None or prop_name not in PROPERTY_UNIT_HINTS:
            continue
        allowed = PROPERTY_UNIT_HINTS[prop_name]
        if unit_is_allowed_for_property(prop_name, unit):
            continue
        report.add(
            ValidationIssue(
                rule="unit_hint_mismatch",
                severity=Severity.WARNING,
                message=(
                    f"Metric '{metric}' uses unit '{unit}'; expected one of "
                    f"{sorted(allowed)} for property '{prop_name}'."
                ),
                row=idx,
                context={
                    "metric": metric,
                    "property": prop_name,
                    "unit": unit,
                    "allowed_units": sorted(allowed),
                },
            )
        )


def _check_contract_text(
    text: str,
    kb: dict[str, Any],
    report: ValidationReport,
) -> None:
    """Extract claims from ``figure_contract.md`` prose and validate them.

    Claims extracted:

    * XRD: 2θ peaks and phase names mentioned in prose.
    * FTIR: wavenumber + functional group pairs.
    * Performance: material + property + value + unit triples.

    XRD claims are checked against ``families.X.xrd_peaks``; FTIR claims
    are checked against ``families.X.ftir_wavenumbers``; performance
    claims trigger a ``unit_hint_mismatch`` warning when the unit does
    not match :data:`PROPERTY_UNIT_HINTS`.
    """
    family_phases: dict[str, list[dict[str, Any]]] = {}
    for _family, payload in (kb.get("families") or {}).items():
        for entry in payload.get("xrd_peaks") or []:
            family_phases.setdefault(entry["phase"], []).append(entry)

    bond_entries: list[tuple[str, float, float]] = []
    for _family, payload in (kb.get("families") or {}).items():
        for entry in payload.get("ftir_wavenumbers") or []:
            bond = entry.get("bond") or entry.get("functional_group")
            if not bond:
                continue
            tol = float(entry.get("tolerance", FTIR_TOLERANCE_CM1))
            for wn in entry.get("wavenumbers") or entry.get("peaks_cm1") or []:
                bond_entries.append((bond, float(wn), tol))

    def _find_better_phase(two_theta: float, exclude: str) -> str | None:
        for candidate, c_peaks in family_phases.items():
            if candidate == exclude:
                continue
            for cp in c_peaks:
                tol = float(cp.get("tolerance_deg", 0.5))
                if any(abs(two_theta - float(p)) <= tol for p in cp["peaks_2theta"]):
                    return candidate
        return None

    # XRD claims from prose.
    for claim in extract_xrd_claims(text):
        theta = claim["two_theta"]
        phase = claim["phase"]
        if not phase:
            continue
        if phase in family_phases:
            canonical = phase
        else:
            canonical = resolve_phase_alias(phase) or phase
        if canonical not in family_phases:
            better = _find_better_phase(theta, exclude=canonical)
            if better is not None:
                report.add(
                    ValidationIssue(
                        rule="xrd_peak_phase_mismatch",
                        severity=Severity.ERROR,
                        message=(
                            f"figure_contract.md: declared phase '{phase}' "
                            f"does not match 2θ={theta}°; better match is "
                            f"'{better}'."
                        ),
                        context={
                            "declared": phase,
                            "expected_phase": better,
                            "two_theta": theta,
                            "source": "figure_contract.md",
                        },
                    )
                )
            continue
        peaks = family_phases[canonical]
        if not peaks:
            continue
        first_phase = peaks[0]
        tolerance = float(first_phase.get("tolerance_deg", 0.5))
        expected = [float(p) for p in first_phase["peaks_2theta"]]
        if not any(abs(theta - e) <= tolerance for e in expected):
            better = _find_better_phase(theta, exclude=canonical)
            if better is not None:
                report.add(
                    ValidationIssue(
                        rule="xrd_peak_phase_mismatch",
                        severity=Severity.ERROR,
                        message=(
                            f"figure_contract.md: declared phase '{phase}' "
                            f"does not match 2θ={theta}°; better match is "
                            f"'{better}'."
                        ),
                        context={
                            "declared": phase,
                            "expected_phase": better,
                            "two_theta": theta,
                            "source": "figure_contract.md",
                        },
                    )
                )

    # FTIR claims from prose.
    for claim in extract_ftir_claims(text):
        wn = claim["wavenumber"]
        group = claim.get("functional_group")
        if not group:
            continue
        kb_at_wn = [
            (bond, kb_wn)
            for bond, kb_wn, tol in bond_entries
            if abs(wn - kb_wn) <= tol
        ]
        if not kb_at_wn:
            continue
        declared_cat = categorise_ftir(group)
        kb_categories = {
            categorise_ftir(bond) for bond, _ in kb_at_wn if categorise_ftir(bond)
        }
        if declared_cat is None or not kb_categories or declared_cat in kb_categories:
            continue
        kb_bond_str = ", ".join(
            f"{b}@{int(w)}cm⁻¹" for b, w in kb_at_wn[:3]
        )
        report.add(
            ValidationIssue(
                rule="ftir_wavenumber_group_mismatch",
                severity=Severity.ERROR,
                message=(
                    f"figure_contract.md: declared bond '{group}' does not "
                    f"match wavenumber {int(wn)}cm⁻¹; KB assigns "
                    f"{kb_bond_str}."
                ),
                context={
                    "declared_group": group,
                    "declared_category": declared_cat,
                    "kb_categories": sorted(kb_categories),
                    "wavenumber": wn,
                    "source": "figure_contract.md",
                },
            )
        )

    # Performance claims from prose (unit-hint only — range check needs
    # canonical performance_ranges; here we only catch unit mismatches
    # because prose extraction has no row index).
    for claim in extract_performance_claims(text):
        prop = claim["property"]
        unit = claim["unit"]
        if prop not in PROPERTY_UNIT_HINTS:
            continue
        allowed = PROPERTY_UNIT_HINTS[prop]
        if unit_is_allowed_for_property(prop, unit):
            continue
        report.add(
            ValidationIssue(
                rule="unit_hint_mismatch",
                severity=Severity.WARNING,
                message=(
                    f"figure_contract.md: {claim['material']} {prop} value "
                    f"{claim['value']} uses unit '{unit}'; expected one of "
                    f"{sorted(allowed)}."
                ),
                context={
                    "material": claim["material"],
                    "property": prop,
                    "value": claim["value"],
                    "unit": unit,
                    "allowed_units": sorted(allowed),
                    "source": "figure_contract.md",
                },
            )
        )


def validate_figure_package(
    package_dir: Path,
    kb_path: Path | None = None,
    output: Path | None = None,
) -> ValidationReport:
    """Validate a figure-package directory against the materials KB.

    Parameters
    ----------
    package_dir
        Path to a figure-package directory.
    kb_path
        Path to the materials KB YAML. Defaults to
        ``<skills_root>/static/core/materials_kb.yaml``.
    output
        Optional path to write a JSON report.

    Returns
    -------
    ValidationReport
    """
    package_dir = Path(package_dir)
    report = ValidationReport(package=str(package_dir))

    if kb_path is None:
        kb_path = KB_PATH
    kb_path = Path(kb_path)
    if not kb_path.is_file():
        report.add(
            ValidationIssue(
                rule="package_files_missing",
                severity=Severity.ERROR,
                message=f"Materials KB not found at {kb_path}.",
            )
        )
        return _finalize(report, output)

    if not package_dir.is_dir():
        report.add(
            ValidationIssue(
                rule="package_files_missing",
                severity=Severity.ERROR,
                message=f"Package directory not found: {package_dir}.",
            )
        )
        return _finalize(report, output)

    csv_path = package_dir / "source_data.csv"
    if not csv_path.is_file():
        report.add(
            ValidationIssue(
                rule="package_files_missing",
                severity=Severity.ERROR,
                message=f"source_data.csv not found in {package_dir}.",
            )
        )
        return _finalize(report, output)

    kb = _load_kb(kb_path)
    rows = _read_csv(csv_path)
    _check_xrd_peak_phase(rows, kb, report)
    _check_ftir_wavenumber(rows, kb, report)
    _check_performance_range(rows, kb, report)
    _check_unit_hint(rows, report)

    # If a figure_contract.md is present, extract prose claims and
    # validate them against the same KB.
    contract_path = package_dir / "figure_contract.md"
    if contract_path.is_file():
        contract_text = contract_path.read_text(encoding="utf-8")
        _check_contract_text(contract_text, kb, report)

    return _finalize(report, output)


def _finalize(report: ValidationReport, output: Path | None) -> ValidationReport:
    if output is not None:
        import json

        with Path(output).open("w", encoding="utf-8") as f:
            json.dump(
                {
                    "package": report.package,
                    "errors": [
                        {
                            "rule": i.rule,
                            "severity": i.severity.value,
                            "message": i.message,
                            "row": i.row,
                            "context": i.context,
                        }
                        for i in report.errors
                    ],
                    "warnings": [
                        {
                            "rule": i.rule,
                            "severity": i.severity.value,
                            "message": i.message,
                            "row": i.row,
                            "context": i.context,
                        }
                        for i in report.warnings
                    ],
                    "summary": report.summary(),
                },
                f,
                indent=2,
                ensure_ascii=False,
            )
    return report


def _build_argparser():
    import argparse

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("package_dir", type=Path)
    p.add_argument(
        "--kb",
        type=Path,
        default=None,
        help="Path to materials_kb.yaml (default: <skill>/static/core/materials_kb.yaml).",
    )
    p.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Optional path to write JSON report.",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_argparser().parse_args(argv)
    report = validate_figure_package(args.package_dir, kb_path=args.kb, output=args.output)
    print(report.summary())
    for issue in report.errors + report.warnings:
        loc = f"row {issue.row}: " if issue.row is not None else ""
        print(f"  [{issue.severity.value}] {issue.rule} — {loc}{issue.message}")
    return report.exit_code()


if __name__ == "__main__":
    raise SystemExit(main())
