#!/usr/bin/env python3
"""
Risk Matrix Calculator

Calculate risk levels based on probability and severity ratings per ISO 14971.
Supports multiple risk matrix configurations and FMEA RPN calculations.

Usage:
    python risk_matrix_calculator.py --probability 3 --severity 4
    python risk_matrix_calculator.py --fmea --severity 8 --occurrence 5 --detection 6
    python risk_matrix_calculator.py --interactive
    python risk_matrix_calculator.py --list-criteria
"""

import argparse
import json
import sys
from typing import Tuple, Optional


# Standard 5x5 Risk Matrix per ISO 14971 common practice
PROBABILITY_LEVELS = {
    1: {"name": "Improbable", "description": "Very unlikely to occur", "frequency": "<10^-6"},
    2: {"name": "Remote", "description": "Unlikely to occur", "frequency": "10^-5 to 10^-6"},
    3: {"name": "Occasional", "description": "May occur", "frequency": "10^-4 to 10^-5"},
    4: {"name": "Probable", "description": "Likely to occur", "frequency": "10^-3 to 10^-4"},
    5: {"name": "Frequent", "description": "Expected to occur", "frequency": ">10^-3"}
}

SEVERITY_LEVELS = {
    1: {"name": "Negligible", "description": "Inconvenience or temporary discomfort", "harm": "No injury"},
    2: {"name": "Minor", "description": "Temporary injury not requiring intervention", "harm": "Temporary discomfort"},
    3: {"name": "Serious", "description": "Injury requiring professional intervention", "harm": "Reversible injury"},
    4: {"name": "Critical", "description": "Permanent impairment or life-threatening", "harm": "Permanent impairment"},
    5: {"name": "Catastrophic", "description": "Death", "harm": "Death"}
}

# Risk matrix: RISK_MATRIX[probability][severity] = risk_level
RISK_MATRIX = {
    1: {1: "Low", 2: "Low", 3: "Low", 4: "Medium", 5: "Medium"},
    2: {1: "Low", 2: "Low", 3: "Medium", 4: "Medium", 5: "High"},
    3: {1: "Low", 2: "Medium", 3: "Medium", 4: "High", 5: "High"},
    4: {1: "Medium", 2: "Medium", 3: "High", 4: "High", 5: "Unacceptable"},
    5: {1: "Medium", 2: "High", 3: "High", 4: "Unacceptable", 5: "Unacceptable"}
}

# Risk level definitions and required actions
RISK_ACTIONS = {
    "Low": {
        "acceptable": True,
        "action": "Document and accept. No further action required.",
        "color": "green"
    },
    "Medium": {
        "acceptable": "AFAP",
        "action": "Reduce as far as possible (AFAP). Document why further reduction is impossible. EU MDR: no economic considerations in acceptability (MDR Annex I GSPR 1-4; EN ISO 14971:2019/A11:2021).",
        "color": "yellow"
    },
    "High": {
        "acceptable": "AFAP",
        "action": "Risk reduction required. Must demonstrate reduction as far as possible (AFAP) if residual risk remains high. EU MDR: no economic considerations in acceptability.",
        "color": "orange"
    },
    "Unacceptable": {
        "acceptable": False,
        "action": "Risk reduction mandatory. Design change required before proceeding.",
        "color": "red"
    }
}

# FMEA scales (1-10)
FMEA_SEVERITY = {
    1: "No effect",
    2: "Very minor effect",
    3: "Minor effect",
    4: "Very low effect",
    5: "Low effect",
    6: "Moderate effect",
    7: "High effect",
    8: "Very high effect",
    9: "Hazardous with warning",
    10: "Hazardous without warning"
}

FMEA_OCCURRENCE = {
    1: "Remote (<1 in 1,500,000)",
    2: "Very low (1 in 150,000)",
    3: "Low (1 in 15,000)",
    4: "Moderately low (1 in 2,000)",
    5: "Moderate (1 in 400)",
    6: "Moderately high (1 in 80)",
    7: "High (1 in 20)",
    8: "Very high (1 in 8)",
    9: "Extremely high (1 in 3)",
    10: "Almost certain (>1 in 2)"
}

FMEA_DETECTION = {
    1: "Almost certain detection",
    2: "Very high detection",
    3: "High detection",
    4: "Moderately high detection",
    5: "Moderate detection",
    6: "Low detection",
    7: "Very low detection",
    8: "Remote detection",
    9: "Very remote detection",
    10: "Cannot detect"
}


def calculate_risk_level(probability: int, severity: int) -> dict:
    """Calculate risk level from probability and severity ratings."""
    if probability < 1 or probability > 5:
        return {"error": f"Probability must be 1-5, got {probability}"}
    if severity < 1 or severity > 5:
        return {"error": f"Severity must be 1-5, got {severity}"}

    risk_level = RISK_MATRIX[probability][severity]
    risk_info = RISK_ACTIONS[risk_level]

    return {
        "probability": {
            "rating": probability,
            **PROBABILITY_LEVELS[probability]
        },
        "severity": {
            "rating": severity,
            **SEVERITY_LEVELS[severity]
        },
        "risk_level": risk_level,
        "acceptable": risk_info["acceptable"],
        "action_required": risk_info["action"],
        "risk_index": probability * severity
    }


def calculate_rpn(severity: int, occurrence: int, detection: int) -> dict:
    """Calculate FMEA Risk Priority Number."""
    if not all(1 <= x <= 10 for x in [severity, occurrence, detection]):
        return {"error": "All FMEA ratings must be 1-10"}

    rpn = severity * occurrence * detection

    # Determine priority level
    if rpn > 200:
        priority = "Critical"
        action = "Immediate action required"
    elif rpn > 100:
        priority = "High"
        action = "Action plan required"
    elif rpn > 50:
        priority = "Medium"
        action = "Consider risk reduction"
    else:
        priority = "Low"
        action = "Monitor"

    return {
        "severity": {
            "rating": severity,
            "description": FMEA_SEVERITY[severity]
        },
        "occurrence": {
            "rating": occurrence,
            "description": FMEA_OCCURRENCE[occurrence]
        },
        "detection": {
            "rating": detection,
            "description": FMEA_DETECTION[detection]
        },
        "rpn": rpn,
        "priority": priority,
        "action_required": action,
        "max_rpn": 1000,
        "rpn_percentage": round(rpn / 10, 1)
    }


def display_risk_matrix():
    """Display the full risk matrix."""
    print("\n" + "=" * 70)
    print("ISO 14971 RISK MATRIX (5x5)")
    print("=" * 70)

    # Header
    print("\n" + " " * 15, end="")
    for s in range(1, 6):
        print(f"S{s:^10}", end="")
    print()

    print(" " * 15, end="")
    for s in range(1, 6):
        print(f"{SEVERITY_LEVELS[s]['name'][:10]:^10}", end="")
    print()

    print("-" * 70)

    # Matrix rows
    for p in range(5, 0, -1):
        print(f"P{p} {PROBABILITY_LEVELS[p]['name'][:10]:>10} |", end="")
        for s in range(1, 6):
            level = RISK_MATRIX[p][s]
            print(f"{level:^10}", end="")
        print()

    print("\n" + "-" * 70)
    print("Risk Levels: Low (Acceptable) | Medium (reduce AFAP) | High (reduce AFAP) | Unacceptable")
    print("EU MDR: reduce as far as possible (AFAP), no economic considerations in acceptability.")
    print("=" * 70)


def display_criteria():
    """Display probability and severity criteria."""
    print("\n" + "=" * 70)
    print("PROBABILITY CRITERIA")
    print("=" * 70)
    for level, info in PROBABILITY_LEVELS.items():
        print(f"\nP{level}: {info['name']}")
        print(f"   Description: {info['description']}")
        print(f"   Frequency: {info['frequency']}")

    print("\n" + "=" * 70)
    print("SEVERITY CRITERIA")
    print("=" * 70)
    for level, info in SEVERITY_LEVELS.items():
        print(f"\nS{level}: {info['name']}")
        print(f"   Description: {info['description']}")
        print(f"   Harm: {info['harm']}")

    print("\n" + "=" * 70)
    print("RISK LEVEL ACTIONS")
    print("=" * 70)
    for level, info in RISK_ACTIONS.items():
        acceptable = "Yes" if info['acceptable'] == True else ("After reduction AFAP" if info['acceptable'] == "AFAP" else "No")
        print(f"\n{level}:")
        print(f"   Acceptable: {acceptable}")
        print(f"   Action: {info['action']}")


def format_result_text(result: dict, analysis_type: str) -> str:
    """Format result for text output."""
    lines = []
    lines.append("\n" + "=" * 50)

    if analysis_type == "risk":
        lines.append("RISK ASSESSMENT RESULT")
        lines.append("=" * 50)
        lines.append(f"\nProbability: P{result['probability']['rating']} - {result['probability']['name']}")
        lines.append(f"  {result['probability']['description']}")
        lines.append(f"\nSeverity: S{result['severity']['rating']} - {result['severity']['name']}")
        lines.append(f"  {result['severity']['description']}")
        lines.append(f"\n{'-' * 50}")
        lines.append(f"RISK LEVEL: {result['risk_level']}")
        lines.append(f"Risk Index: {result['risk_index']} (P × S)")
        lines.append(f"Acceptable: {result['acceptable']}")
        lines.append(f"\nAction Required:")
        lines.append(f"  {result['action_required']}")

    elif analysis_type == "fmea":
        lines.append("FMEA RPN CALCULATION")
        lines.append("=" * 50)
        lines.append(f"\nSeverity: {result['severity']['rating']}/10")
        lines.append(f"  {result['severity']['description']}")
        lines.append(f"\nOccurrence: {result['occurrence']['rating']}/10")
        lines.append(f"  {result['occurrence']['description']}")
        lines.append(f"\nDetection: {result['detection']['rating']}/10")
        lines.append(f"  {result['detection']['description']}")
        lines.append(f"\n{'-' * 50}")
        lines.append(f"RPN: {result['rpn']} / {result['max_rpn']} ({result['rpn_percentage']}%)")
        lines.append(f"Priority: {result['priority']}")
        lines.append(f"\nAction Required:")
        lines.append(f"  {result['action_required']}")

    lines.append("=" * 50)
    return "\n".join(lines)


def interactive_mode():
    """Run interactive risk assessment."""
    print("\n" + "=" * 50)
    print("RISK MATRIX CALCULATOR - Interactive Mode")
    print("=" * 50)

    print("\nSelect analysis type:")
    print("1. Risk Matrix (ISO 14971 style)")
    print("2. FMEA RPN Calculation")
    print("3. Display Risk Matrix")
    print("4. Display Criteria")
    print("5. Exit")

    choice = input("\nEnter choice (1-5): ").strip()

    if choice == "1":
        display_criteria()
        print("\n" + "-" * 50)
        try:
            p = int(input("Enter Probability (1-5): "))
            s = int(input("Enter Severity (1-5): "))
            result = calculate_risk_level(p, s)
            if "error" in result:
                print(f"\nError: {result['error']}")
            else:
                print(format_result_text(result, "risk"))
        except ValueError:
            print("Invalid input. Please enter numbers.")

    elif choice == "2":
        print("\nFMEA Scales:")
        print("  Severity: 1 (No effect) to 10 (Hazardous without warning)")
        print("  Occurrence: 1 (Remote) to 10 (Almost certain)")
        print("  Detection: 1 (Almost certain) to 10 (Cannot detect)")
        print("-" * 50)
        try:
            s = int(input("Enter Severity (1-10): "))
            o = int(input("Enter Occurrence (1-10): "))
            d = int(input("Enter Detection (1-10): "))
            result = calculate_rpn(s, o, d)
            if "error" in result:
                print(f"\nError: {result['error']}")
            else:
                print(format_result_text(result, "fmea"))
        except ValueError:
            print("Invalid input. Please enter numbers.")

    elif choice == "3":
        display_risk_matrix()

    elif choice == "4":
        display_criteria()

    elif choice == "5":
        print("Exiting.")
        return

    else:
        print("Invalid choice.")


def main():
    parser = argparse.ArgumentParser(
        description="Calculate risk levels per ISO 14971 or FMEA RPN",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # ISO 14971 risk matrix calculation
  python risk_matrix_calculator.py --probability 3 --severity 4

  # FMEA RPN calculation
  python risk_matrix_calculator.py --fmea --severity 8 --occurrence 5 --detection 6

  # Interactive mode
  python risk_matrix_calculator.py --interactive

  # Display risk matrix
  python risk_matrix_calculator.py --show-matrix

  # Display criteria definitions
  python risk_matrix_calculator.py --list-criteria

  # JSON output
  python risk_matrix_calculator.py -p 4 -s 3 --output json
        """
    )

    parser.add_argument("-p", "--probability", type=int, help="Probability rating (1-5)")
    parser.add_argument("-s", "--severity", type=int, help="Severity rating (1-5 for risk, 1-10 for FMEA)")
    parser.add_argument("-o", "--occurrence", type=int, help="FMEA occurrence rating (1-10)")
    parser.add_argument("-d", "--detection", type=int, help="FMEA detection rating (1-10)")
    parser.add_argument("--fmea", action="store_true", help="Use FMEA RPN calculation")
    parser.add_argument("--output", choices=["text", "json"], default="text", help="Output format")
    parser.add_argument("--show-matrix", action="store_true", help="Display risk matrix")
    parser.add_argument("--list-criteria", action="store_true", help="Display probability and severity criteria")
    parser.add_argument("--interactive", action="store_true", help="Run in interactive mode")

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.show_matrix:
        display_risk_matrix()
        return

    if args.list_criteria:
        display_criteria()
        return

    if args.fmea:
        if not all([args.severity, args.occurrence, args.detection]):
            parser.error("FMEA requires --severity, --occurrence, and --detection")

        result = calculate_rpn(args.severity, args.occurrence, args.detection)
        if "error" in result:
            print(f"Error: {result['error']}")
            sys.exit(1)

        if args.output == "json":
            print(json.dumps(result, indent=2))
        else:
            print(format_result_text(result, "fmea"))

    else:
        if not all([args.probability, args.severity]):
            parser.error("Risk calculation requires --probability and --severity")

        result = calculate_risk_level(args.probability, args.severity)
        if "error" in result:
            print(f"Error: {result['error']}")
            sys.exit(1)

        if args.output == "json":
            print(json.dumps(result, indent=2))
        else:
            print(format_result_text(result, "risk"))


if __name__ == "__main__":
    main()
