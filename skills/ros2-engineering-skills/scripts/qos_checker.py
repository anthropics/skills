#!/usr/bin/env python3
"""Check QoS compatibility between publisher and subscriber profiles.

Usage:
    python qos_checker.py --pub reliable,transient_local,keep_last,5 --sub best_effort,volatile,keep_last,10
    python qos_checker.py --pub reliable,volatile,keep_last,1 --sub reliable,volatile,keep_last,1
    python qos_checker.py --preset sensor
    python qos_checker.py --preset command

Profiles are specified as: reliability,durability,history,depth
"""

import argparse
import sys
from dataclasses import dataclass
from enum import Enum
from typing import Optional


class Reliability(Enum):
    RELIABLE = "reliable"
    BEST_EFFORT = "best_effort"


class Durability(Enum):
    TRANSIENT_LOCAL = "transient_local"
    VOLATILE = "volatile"


class History(Enum):
    KEEP_LAST = "keep_last"
    KEEP_ALL = "keep_all"


@dataclass
class QoSProfile:
    reliability: Reliability
    durability: Durability
    history: History
    depth: int
    label: str = ""

    def __str__(self) -> str:
        parts = [
            f"  reliability:  {self.reliability.value}",
            f"  durability:   {self.durability.value}",
            f"  history:      {self.history.value}",
            f"  depth:        {self.depth}",
        ]
        header = f"[{self.label}]" if self.label else "[QoS Profile]"
        return header + "\n" + "\n".join(parts)


# Pre-defined presets matching common ROS 2 usage patterns
PRESETS = {
    "sensor": {
        "pub": QoSProfile(Reliability.BEST_EFFORT, Durability.VOLATILE, History.KEEP_LAST, 5, "Sensor Publisher"),
        "sub": QoSProfile(Reliability.BEST_EFFORT, Durability.VOLATILE, History.KEEP_LAST, 5, "Sensor Subscriber"),
    },
    "command": {
        "pub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1, "Command Publisher"),
        "sub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1, "Command Subscriber"),
    },
    "map": {
        "pub": QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL, History.KEEP_LAST, 1, "Map Publisher"),
        "sub": QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL, History.KEEP_LAST, 1, "Map Subscriber"),
    },
    "diagnostics": {
        "pub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10, "Diagnostics Publisher"),
        "sub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10, "Diagnostics Subscriber"),
    },
}


def parse_qos_string(qos_str: str, label: str = "") -> QoSProfile:
    """Parse a QoS string like 'reliable,volatile,keep_last,10'."""
    parts = [p.strip().lower() for p in qos_str.split(",")]
    if len(parts) != 4:
        print(f"Error: QoS profile must have 4 comma-separated values: "
              f"reliability,durability,history,depth", file=sys.stderr)
        print(f"Got: {qos_str!r}", file=sys.stderr)
        sys.exit(1)

    try:
        reliability = Reliability(parts[0])
    except ValueError:
        print(f"Error: Invalid reliability '{parts[0]}'. "
              f"Choose from: reliable, best_effort", file=sys.stderr)
        sys.exit(1)

    try:
        durability = Durability(parts[1])
    except ValueError:
        print(f"Error: Invalid durability '{parts[1]}'. "
              f"Choose from: transient_local, volatile", file=sys.stderr)
        sys.exit(1)

    try:
        history = History(parts[2])
    except ValueError:
        print(f"Error: Invalid history '{parts[2]}'. "
              f"Choose from: keep_last, keep_all", file=sys.stderr)
        sys.exit(1)

    try:
        depth = int(parts[3])
        if depth < 0:
            raise ValueError("depth must be non-negative")
    except ValueError as e:
        print(f"Error: Invalid depth '{parts[3]}': {e}", file=sys.stderr)
        sys.exit(1)

    return QoSProfile(reliability, durability, history, depth, label)


@dataclass
class CompatibilityResult:
    compatible: bool
    issues: list
    warnings: list
    suggestions: list


def check_compatibility(pub: QoSProfile, sub: QoSProfile) -> CompatibilityResult:
    """Check QoS compatibility between a publisher and subscriber."""
    issues = []
    warnings = []
    suggestions = []

    # Reliability compatibility
    if pub.reliability == Reliability.BEST_EFFORT and sub.reliability == Reliability.RELIABLE:
        issues.append(
            "INCOMPATIBLE RELIABILITY: Publisher is BEST_EFFORT but subscriber "
            "demands RELIABLE. The subscriber requires delivery guarantees that "
            "the publisher cannot provide. Connection will silently fail."
        )
        suggestions.append(
            "Fix: Either change the publisher to RELIABLE, or change the "
            "subscriber to BEST_EFFORT."
        )

    if pub.reliability == Reliability.RELIABLE and sub.reliability == Reliability.BEST_EFFORT:
        warnings.append(
            "Publisher is RELIABLE but subscriber is BEST_EFFORT. This is compatible "
            "but the subscriber won't benefit from the publisher's reliability "
            "guarantees — messages may still be dropped on the subscriber side."
        )

    # Durability compatibility
    if pub.durability == Durability.VOLATILE and sub.durability == Durability.TRANSIENT_LOCAL:
        issues.append(
            "INCOMPATIBLE DURABILITY: Publisher is VOLATILE but subscriber expects "
            "TRANSIENT_LOCAL. Late-joining subscribers will NOT receive the last "
            "published message. Connection will silently fail."
        )
        suggestions.append(
            "Fix: Change the publisher to TRANSIENT_LOCAL (it will retain the "
            "last message for late subscribers), or change the subscriber to VOLATILE."
        )

    # History / depth warnings
    if pub.history == History.KEEP_ALL:
        warnings.append(
            "Publisher uses KEEP_ALL history. This can lead to unbounded memory "
            "growth if the subscriber is slow. Consider KEEP_LAST with explicit depth."
        )

    if sub.history == History.KEEP_ALL:
        warnings.append(
            "Subscriber uses KEEP_ALL history. Memory will grow if messages "
            "arrive faster than they are processed. Consider KEEP_LAST."
        )

    if (pub.history == History.KEEP_LAST and sub.history == History.KEEP_LAST
            and sub.depth < pub.depth):
        warnings.append(
            f"Subscriber depth ({sub.depth}) is less than publisher depth "
            f"({pub.depth}). The subscriber may drop messages during bursts. "
            f"Consider increasing subscriber depth to >= {pub.depth}."
        )

    if sub.history == History.KEEP_LAST and sub.depth == 1:
        warnings.append(
            "Subscriber depth is 1. Only the latest message is kept; older "
            "messages are dropped if the callback is slow."
        )

    compatible = len(issues) == 0
    return CompatibilityResult(compatible, issues, warnings, suggestions)


def print_result(pub: QoSProfile, sub: QoSProfile, result: CompatibilityResult) -> None:
    """Print compatibility check results."""
    print("=" * 60)
    print("QoS Compatibility Check")
    print("=" * 60)
    print()
    print(pub)
    print()
    print(sub)
    print()
    print("-" * 60)

    if result.compatible:
        print("Result: COMPATIBLE")
    else:
        print("Result: INCOMPATIBLE")

    if result.issues:
        print()
        print("Issues:")
        for issue in result.issues:
            print(f"  [ERROR] {issue}")

    if result.warnings:
        print()
        print("Warnings:")
        for warning in result.warnings:
            print(f"  [WARN]  {warning}")

    if result.suggestions:
        print()
        print("Suggestions:")
        for suggestion in result.suggestions:
            print(f"  -> {suggestion}")

    print("=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Check QoS compatibility between publisher and subscriber profiles",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --pub reliable,volatile,keep_last,1 --sub reliable,volatile,keep_last,1
  %(prog)s --pub best_effort,volatile,keep_last,5 --sub reliable,volatile,keep_last,5
  %(prog)s --preset sensor
  %(prog)s --preset command

Presets: sensor, command, map, diagnostics
        """)
    parser.add_argument("--pub", help="Publisher QoS: reliability,durability,history,depth")
    parser.add_argument("--sub", help="Subscriber QoS: reliability,durability,history,depth")
    parser.add_argument("--preset", choices=PRESETS.keys(),
                        help="Use a predefined QoS preset")
    args = parser.parse_args()

    if args.preset:
        pub = PRESETS[args.preset]["pub"]
        sub = PRESETS[args.preset]["sub"]
        print(f"Using preset: {args.preset}")
    elif args.pub and args.sub:
        pub = parse_qos_string(args.pub, "Publisher")
        sub = parse_qos_string(args.sub, "Subscriber")
    else:
        parser.print_help()
        print("\nError: Provide either --preset or both --pub and --sub", file=sys.stderr)
        sys.exit(1)

    result = check_compatibility(pub, sub)
    print_result(pub, sub, result)

    sys.exit(0 if result.compatible else 1)


if __name__ == "__main__":
    main()
