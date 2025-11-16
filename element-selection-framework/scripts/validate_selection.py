#!/usr/bin/env python3
"""
Element Selection Validation Script

Validates element selections for a given stage against the 6 validation criteria:
1. Condition Coverage
2. Necessity
3. Sufficiency
4. Causal Flow
5. Interference
6. Reality Test (requires actual data)

Usage:
    python validate_selection.py <stage_number> <elements_file>

Example:
    python validate_selection.py 3 stage3_elements.json
"""

import json
import sys
from dataclasses import dataclass
from typing import List, Dict, Any, Set, Tuple
from enum import Enum


class ValidationStatus(Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    WARNING = "WARNING"


@dataclass
class Element:
    """Represents a single element in a system."""
    name: str
    system: str
    conditions_optimized: List[int]
    contributions: Dict[str, float]  # threshold_name -> rate
    prerequisites: List[str]  # required system outputs


@dataclass
class StageConfig:
    """Configuration for a specific stage."""
    number: int
    goal: str
    critical_conditions: List[int]
    important_conditions: List[int]
    thresholds: Dict[str, float]  # threshold_name -> target_value
    max_reasonable_cycles: int = 100


# Causal sequence of systems
CAUSAL_ORDER = [
    "Rich Soil",
    "Root Network",
    "Conscious Trunk",
    "Living Branches",
    "Dancing Leaves",
    "Photosynthesis",
    "Seed Production",
    "Fruiting Process",
    "Wise Gardener",
    "Cognitive Tools",
    "DKE",
    "Living Partnership",
    "Forest Intelligence"
]

# Condition to System Mapping
CONDITION_TO_SYSTEMS = {
    1: ["Rich Soil", "Living Branches", "Dancing Leaves"],  # Existence
    2: ["Root Network", "Conscious Trunk", "Photosynthesis"],  # Coupling
    3: ["Dancing Leaves", "Photosynthesis", "DKE"],  # Compatibility
    4: ["Rich Soil", "Wise Gardener", "DKE"],  # Edge of Chaos
    5: ["Conscious Trunk", "Cognitive Tools", "DKE"],  # Free Energy
    6: ["DKE", "Forest Intelligence", "Wise Gardener"],  # Temporal Duration
}

# Stage configurations
STAGE_CONFIGS = {
    0: StageConfig(
        number=0,
        goal="Maximize M = I(U; P(U))",
        critical_conditions=[1, 4],
        important_conditions=[5],
        thresholds={
            "meta_awareness_score": 0.7,
            "self_assessment_accuracy": 0.8,
        },
        max_reasonable_cycles=30
    ),
    1: StageConfig(
        number=1,
        goal="Maximize H(K) measurement precision",
        critical_conditions=[1, 4, 5],
        important_conditions=[6],
        thresholds={
            "confusion_points": 20,
            "baseline_clarity": 0.7,
            "gaps_mapped": 10,
        },
        max_reasonable_cycles=40
    ),
    2: StageConfig(
        number=2,
        goal="Maximize β·E(N)",
        critical_conditions=[1, 3],
        important_conditions=[2, 4, 6],
        thresholds={
            "information_pieces": 50,
            "quality_score": 0.7,
            "source_diversity": 5,
            "modal_coverage": 3,
        },
        max_reasonable_cycles=50
    ),
    3: StageConfig(
        number=3,
        goal="Maximize I(K;N) = H(K) - H(K|N)",
        critical_conditions=[1, 2, 3, 4, 5, 6],  # All critical
        important_conditions=[],
        thresholds={
            "mutual_information_increase": 5.0,
            "uncertainty_reduction": 0.6,
            "new_connections": 10,
            "confidence": 0.8,
        },
        max_reasonable_cycles=40
    ),
    4: StageConfig(
        number=4,
        goal="Maximize Corr(U,R)",
        critical_conditions=[3, 4],
        important_conditions=[1, 5],
        thresholds={
            "reality_alignment": 0.85,
            "prediction_accuracy": 0.8,
            "error_detection_rate": 0.9,
        },
        max_reasonable_cycles=50
    ),
    5: StageConfig(
        number=5,
        goal="Minimize Access_Time, Maximize Fluency",
        critical_conditions=[5, 6],
        important_conditions=[2, 3],
        thresholds={
            "access_time": 0.5,  # seconds (minimize)
            "fluency_score": 0.9,
            "automaticity_index": 0.8,
        },
        max_reasonable_cycles=100
    ),
}


def validate_condition_coverage(
    stage: StageConfig,
    elements: List[Element]
) -> Tuple[ValidationStatus, str, List[str]]:
    """
    Validation 1: Check if all critical conditions have optimizing elements.
    """
    missing_conditions = []

    for condition in stage.critical_conditions:
        optimizing_elements = [
            e for e in elements if condition in e.conditions_optimized
        ]
        if not optimizing_elements:
            missing_conditions.append(condition)

    if missing_conditions:
        recommendations = [
            f"Add elements from {CONDITION_TO_SYSTEMS[c]} for condition {c}"
            for c in missing_conditions
        ]
        return (
            ValidationStatus.FAIL,
            f"Missing coverage for conditions: {missing_conditions}",
            recommendations
        )

    return (
        ValidationStatus.PASS,
        "All critical conditions have optimizing elements",
        []
    )


def validate_necessity(
    stage: StageConfig,
    elements: List[Element]
) -> Tuple[ValidationStatus, str, List[str]]:
    """
    Validation 2: Check if all elements are necessary.
    """
    redundant_elements = []

    for i, element in enumerate(elements):
        # Try removing this element
        remaining = elements[:i] + elements[i+1:]

        # Check condition coverage without this element
        still_covered = True
        for condition in stage.critical_conditions:
            if not any(condition in e.conditions_optimized for e in remaining):
                still_covered = False
                break

        # Check threshold reachability without this element
        thresholds_reachable = True
        for threshold_name, target in stage.thresholds.items():
            total_rate = sum(
                e.contributions.get(threshold_name, 0) for e in remaining
            )
            if total_rate <= 0:
                thresholds_reachable = False
                break

        # If both still pass, element may be redundant
        if still_covered and thresholds_reachable:
            # Check if element significantly enhances any metric
            element_contribution = sum(element.contributions.values())
            if element_contribution < 0.1:  # Low contribution threshold
                redundant_elements.append(element.name)

    if redundant_elements:
        return (
            ValidationStatus.WARNING,
            f"Potentially redundant elements: {redundant_elements}",
            ["Consider removing low-impact elements to reduce complexity"]
        )

    return (
        ValidationStatus.PASS,
        "All elements contribute meaningfully",
        []
    )


def validate_sufficiency(
    stage: StageConfig,
    elements: List[Element]
) -> Tuple[ValidationStatus, str, List[str]]:
    """
    Validation 3: Check if thresholds are reachable.
    """
    unreachable_thresholds = []
    threshold_analysis = {}

    for threshold_name, target in stage.thresholds.items():
        total_rate = sum(
            e.contributions.get(threshold_name, 0) for e in elements
        )

        if total_rate <= 0:
            unreachable_thresholds.append(threshold_name)
            threshold_analysis[threshold_name] = {
                "status": "NO_PROGRESS",
                "rate": 0,
                "cycles_needed": float('inf')
            }
        else:
            cycles_needed = target / total_rate
            if cycles_needed > stage.max_reasonable_cycles:
                unreachable_thresholds.append(threshold_name)
                threshold_analysis[threshold_name] = {
                    "status": "TOO_SLOW",
                    "rate": total_rate,
                    "cycles_needed": cycles_needed
                }
            else:
                threshold_analysis[threshold_name] = {
                    "status": "REACHABLE",
                    "rate": total_rate,
                    "cycles_needed": cycles_needed
                }

    if unreachable_thresholds:
        recommendations = []
        for t in unreachable_thresholds:
            analysis = threshold_analysis[t]
            if analysis["status"] == "NO_PROGRESS":
                recommendations.append(f"Add elements contributing to {t}")
            else:
                recommendations.append(
                    f"Increase contribution to {t} (current rate: {analysis['rate']:.3f})"
                )

        return (
            ValidationStatus.FAIL,
            f"Unreachable thresholds: {unreachable_thresholds}",
            recommendations
        )

    # Find limiting threshold
    limiting = max(
        threshold_analysis.items(),
        key=lambda x: x[1]["cycles_needed"]
    )

    return (
        ValidationStatus.PASS,
        f"All thresholds reachable. Limiting: {limiting[0]} at {limiting[1]['cycles_needed']:.1f} cycles",
        []
    )


def validate_causal_flow(
    stage: StageConfig,
    elements: List[Element]
) -> Tuple[ValidationStatus, str, List[str]]:
    """
    Validation 4: Check if causal sequence is respected.
    """
    violations = []

    for element in elements:
        system_index = CAUSAL_ORDER.index(element.system)

        for prereq_system in element.prerequisites:
            prereq_index = CAUSAL_ORDER.index(prereq_system)

            # Check if prerequisite system has elements active
            prereq_active = any(
                e.system == prereq_system for e in elements
            )

            # If prereq system is after current system in causal order, violation
            if prereq_index > system_index and not prereq_active:
                violations.append(
                    f"{element.name} requires {prereq_system} which is not active"
                )

    if violations:
        return (
            ValidationStatus.FAIL,
            f"Causal flow violations detected",
            violations
        )

    return (
        ValidationStatus.PASS,
        "All causal dependencies satisfied",
        []
    )


def validate_interference(
    elements: List[Element]
) -> Tuple[ValidationStatus, str, List[str]]:
    """
    Validation 5: Check for harmful interference between elements.
    """
    # Define known interference patterns
    INTERFERING_PATTERNS = [
        ("Rapid Capture", "Deep Analysis"),
        ("Strict Filtering", "Broad Discovery"),
        ("Heavy Load", "Energy Conservation"),
        ("Fixed Structure", "Flexible Reorganization"),
    ]

    conflicts = []
    element_names = [e.name for e in elements]

    for pattern in INTERFERING_PATTERNS:
        if pattern[0] in element_names and pattern[1] in element_names:
            conflicts.append(f"{pattern[0]} ↔ {pattern[1]}")

    # Calculate interference score (simplified)
    interference_score = len(conflicts) * 0.1
    threshold = len(elements) * 0.1

    if interference_score > threshold:
        return (
            ValidationStatus.FAIL,
            f"Excessive interference detected (score: {interference_score:.2f})",
            [f"Resolve conflict: {c}" for c in conflicts]
        )

    if conflicts:
        return (
            ValidationStatus.WARNING,
            f"Minor interference detected: {conflicts}",
            ["Monitor for performance impact"]
        )

    return (
        ValidationStatus.PASS,
        "Harmonic coordination achieved",
        []
    )


def generate_validation_report(
    stage_number: int,
    elements: List[Element]
) -> Dict[str, Any]:
    """
    Generate comprehensive validation report for element selection.
    """
    if stage_number not in STAGE_CONFIGS:
        return {
            "error": f"Stage {stage_number} not configured",
            "available_stages": list(STAGE_CONFIGS.keys())
        }

    stage = STAGE_CONFIGS[stage_number]

    report = {
        "stage": stage_number,
        "goal": stage.goal,
        "total_elements": len(elements),
        "validations": {}
    }

    # Run all validations
    validations = [
        ("condition_coverage", validate_condition_coverage(stage, elements)),
        ("necessity", validate_necessity(stage, elements)),
        ("sufficiency", validate_sufficiency(stage, elements)),
        ("causal_flow", validate_causal_flow(stage, elements)),
        ("interference", validate_interference(elements)),
    ]

    all_passed = True
    for name, (status, message, recommendations) in validations:
        report["validations"][name] = {
            "status": status.value,
            "message": message,
            "recommendations": recommendations
        }
        if status == ValidationStatus.FAIL:
            all_passed = False

    report["overall_status"] = "PASS" if all_passed else "FAIL"
    report["reality_test_pending"] = True  # Always needs actual testing

    return report


def load_elements_from_file(filepath: str) -> List[Element]:
    """Load element definitions from JSON file."""
    with open(filepath, 'r') as f:
        data = json.load(f)

    elements = []
    for elem_data in data:
        elements.append(Element(
            name=elem_data["name"],
            system=elem_data["system"],
            conditions_optimized=elem_data["conditions_optimized"],
            contributions=elem_data.get("contributions", {}),
            prerequisites=elem_data.get("prerequisites", [])
        ))

    return elements


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        print("\nExample element JSON format:")
        example = [
            {
                "name": "Pattern Recognizer",
                "system": "Photosynthesis",
                "conditions_optimized": [2, 3],
                "contributions": {
                    "mutual_information_increase": 0.3,
                    "new_connections": 0.5
                },
                "prerequisites": ["Dancing Leaves"]
            }
        ]
        print(json.dumps(example, indent=2))
        sys.exit(1)

    stage_number = int(sys.argv[1])
    elements_file = sys.argv[2]

    print(f"Validating element selection for Stage {stage_number}...")
    print("-" * 50)

    elements = load_elements_from_file(elements_file)
    report = generate_validation_report(stage_number, elements)

    print(json.dumps(report, indent=2))

    # Exit with appropriate code
    if report.get("overall_status") == "PASS":
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
