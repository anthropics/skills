#!/usr/bin/env python3
"""Check QoS compatibility between publisher and subscriber profiles.

Usage:
    python qos_checker.py --pub reliable,transient_local,keep_last,5 --sub best_effort,volatile,keep_last,10
    python qos_checker.py --pub reliable,volatile,keep_last,1 --sub reliable,volatile,keep_last,1
    python qos_checker.py --preset sensor
    python qos_checker.py --preset command
    python qos_checker.py --pub reliable,volatile,keep_last,1 --sub reliable,volatile,keep_last,1 --json

Profiles are specified as: reliability,durability,history,depth[,deadline_ms,lifespan_ms,liveliness,liveliness_lease_ms]
"""

import argparse
import json
import sys
from dataclasses import dataclass
from enum import Enum

__version__ = "0.1.0"


class DDSVendor(Enum):
    AUTO = "auto"
    FASTDDS = "fastdds"
    CYCLONEDDS = "cyclonedds"
    CONNEXT = "connext"


class Reliability(Enum):
    RELIABLE = "reliable"
    BEST_EFFORT = "best_effort"


class Durability(Enum):
    TRANSIENT_LOCAL = "transient_local"
    VOLATILE = "volatile"


class History(Enum):
    KEEP_LAST = "keep_last"
    KEEP_ALL = "keep_all"


class Liveliness(Enum):
    AUTOMATIC = "automatic"
    MANUAL_BY_TOPIC = "manual_by_topic"


@dataclass
class QoSProfile:
    reliability: Reliability
    durability: Durability
    history: History
    depth: int
    label: str = ""
    deadline_ms: int = 0
    lifespan_ms: int = 0
    liveliness: Liveliness = Liveliness.AUTOMATIC
    liveliness_lease_ms: int = 0

    def __str__(self) -> str:
        parts = [
            f"  reliability:         {self.reliability.value}",
            f"  durability:          {self.durability.value}",
            f"  history:             {self.history.value}",
            f"  depth:               {self.depth}",
            f"  deadline_ms:         {self.deadline_ms}",
            f"  lifespan_ms:         {self.lifespan_ms}",
            f"  liveliness:          {self.liveliness.value}",
            f"  liveliness_lease_ms: {self.liveliness_lease_ms}",
        ]
        header = f"[{self.label}]" if self.label else "[QoS Profile]"
        return header + "\n" + "\n".join(parts)

    def to_dict(self) -> dict:
        return {
            "reliability": self.reliability.value,
            "durability": self.durability.value,
            "history": self.history.value,
            "depth": self.depth,
            "label": self.label,
            "deadline_ms": self.deadline_ms,
            "lifespan_ms": self.lifespan_ms,
            "liveliness": self.liveliness.value,
            "liveliness_lease_ms": self.liveliness_lease_ms,
        }


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
    "parameter_events": {
        "pub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1000,
                          "Parameter Events Publisher"),
        "sub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1000,
                          "Parameter Events Subscriber"),
    },
    "action_feedback": {
        "pub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                          "Action Feedback Publisher"),
        "sub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                          "Action Feedback Subscriber"),
    },
    "safety_heartbeat": {
        "pub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                          "Safety Heartbeat Publisher",
                          deadline_ms=500, lifespan_ms=1000),
        "sub": QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                          "Safety Heartbeat Subscriber",
                          deadline_ms=500, lifespan_ms=1000),
    },
}


# Shorthand mappings: single keyword → full default QoS profile string
QOS_SHORTHANDS = {
    "reliable": "reliable,volatile,keep_last,10",
    "best_effort": "best_effort,volatile,keep_last,10",
    "transient_local": "reliable,transient_local,keep_last,1",
    "volatile": "reliable,volatile,keep_last,10",
    "keep_all": "reliable,volatile,keep_all,0",
    "keep_last": "reliable,volatile,keep_last,10",
}


def _expand_qos_shorthand(qos_str: str) -> str:
    """Expand single-keyword QoS shorthand to full profile string.

    Supports keywords like 'reliable', 'best_effort', 'transient_local', etc.
    Returns the original string unchanged if it's not a recognized shorthand.
    """
    normalized = qos_str.strip().lower().replace("-", "_")
    if normalized in QOS_SHORTHANDS:
        return QOS_SHORTHANDS[normalized]
    return qos_str


def parse_qos_string(qos_str: str, label: str = "") -> QoSProfile:
    """Parse a QoS string like 'reliable,volatile,keep_last,10[,...]'.

    Also accepts single-keyword shorthands like 'reliable' or 'best_effort'
    which expand to sensible default profiles.
    """
    qos_str = _expand_qos_shorthand(qos_str)
    parts = [p.strip().lower() for p in qos_str.split(",")]
    if len(parts) not in (4, 8):
        print("Error: QoS profile must have 4 or 8 comma-separated values: "
              "reliability,durability,history,depth"
              "[,deadline_ms,lifespan_ms,liveliness,liveliness_lease_ms]",
              file=sys.stderr)
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

    deadline_ms = 0
    lifespan_ms = 0
    liveliness = Liveliness.AUTOMATIC
    liveliness_lease_ms = 0

    if len(parts) == 8:
        try:
            deadline_ms = int(parts[4])
            if deadline_ms < 0:
                raise ValueError("deadline_ms must be non-negative")
        except ValueError as e:
            print(f"Error: Invalid deadline_ms '{parts[4]}': {e}", file=sys.stderr)
            sys.exit(1)

        try:
            lifespan_ms = int(parts[5])
            if lifespan_ms < 0:
                raise ValueError("lifespan_ms must be non-negative")
        except ValueError as e:
            print(f"Error: Invalid lifespan_ms '{parts[5]}': {e}", file=sys.stderr)
            sys.exit(1)

        try:
            liveliness = Liveliness(parts[6])
        except ValueError:
            print(f"Error: Invalid liveliness '{parts[6]}'. "
                  f"Choose from: automatic, manual_by_topic", file=sys.stderr)
            sys.exit(1)

        try:
            liveliness_lease_ms = int(parts[7])
            if liveliness_lease_ms < 0:
                raise ValueError("liveliness_lease_ms must be non-negative")
        except ValueError as e:
            print(f"Error: Invalid liveliness_lease_ms '{parts[7]}': {e}", file=sys.stderr)
            sys.exit(1)

    return QoSProfile(reliability, durability, history, depth, label,
                      deadline_ms, lifespan_ms, liveliness, liveliness_lease_ms)


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
            "guarantees -- messages may still be dropped on the subscriber side."
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

    # depth=0 with KEEP_LAST validation
    if pub.history == History.KEEP_LAST and pub.depth == 0:
        warnings.append(
            "depth=0 with KEEP_LAST is undefined behavior in some DDS implementations."
        )
    if sub.history == History.KEEP_LAST and sub.depth == 0:
        warnings.append(
            "depth=0 with KEEP_LAST is undefined behavior in some DDS implementations."
        )

    # Deadline compatibility (DDS RxO: offered_deadline <= requested_deadline)
    # deadline=0 means "no deadline" (infinite). If subscriber expects a deadline
    # but publisher offers none, the connection is incompatible.
    if sub.deadline_ms > 0 and pub.deadline_ms == 0:
        issues.append(
            f"INCOMPATIBLE DEADLINE: Publisher has no deadline (infinite) but "
            f"subscriber requires {sub.deadline_ms}ms. DDS requires the publisher "
            f"to offer a deadline <= the subscriber's requested deadline. "
            f"Connection will silently fail."
        )
        suggestions.append(
            f"Fix: Set the publisher deadline to <= {sub.deadline_ms}ms, "
            f"or remove the subscriber deadline constraint."
        )
    elif pub.deadline_ms > 0 and sub.deadline_ms > 0 and pub.deadline_ms > sub.deadline_ms:
        issues.append(
            f"INCOMPATIBLE DEADLINE: Publisher offered deadline ({pub.deadline_ms}ms) "
            f"exceeds subscriber requested deadline ({sub.deadline_ms}ms). "
            f"DDS requires offered <= requested. Connection will silently fail."
        )
        suggestions.append(
            f"Fix: Either decrease the publisher deadline to <= {sub.deadline_ms}ms, "
            f"or increase the subscriber deadline to >= {pub.deadline_ms}ms."
        )

    # Lifespan vs deadline check
    if pub.lifespan_ms > 0 and sub.deadline_ms > 0 and pub.lifespan_ms < sub.deadline_ms:
        warnings.append(
            f"Publisher lifespan ({pub.lifespan_ms}ms) is shorter than subscriber "
            f"deadline ({sub.deadline_ms}ms). Messages may expire before the "
            f"subscriber's deadline triggers, causing missed deadline events."
        )

    # Liveliness compatibility (kind)
    if (pub.liveliness == Liveliness.AUTOMATIC
            and sub.liveliness == Liveliness.MANUAL_BY_TOPIC):
        issues.append(
            "INCOMPATIBLE LIVELINESS: Publisher uses AUTOMATIC liveliness but "
            "subscriber requires MANUAL_BY_TOPIC. The subscriber expects the "
            "publisher to manually assert its liveliness, which it will not do. "
            "Connection will silently fail."
        )
        suggestions.append(
            "Fix: Either change the publisher to MANUAL_BY_TOPIC, or change the "
            "subscriber to AUTOMATIC."
        )

    # Liveliness lease duration (DDS RxO: offered_lease <= requested_lease)
    # lease=0 means "infinite". If subscriber expects a specific lease but
    # publisher offers none (infinite), the connection is incompatible.
    if sub.liveliness_lease_ms > 0 and pub.liveliness_lease_ms == 0:
        issues.append(
            f"INCOMPATIBLE LIVELINESS LEASE: Publisher has no lease duration "
            f"(infinite) but subscriber requires {sub.liveliness_lease_ms}ms. "
            f"DDS requires offered lease <= requested lease. "
            f"Connection will silently fail."
        )
        suggestions.append(
            f"Fix: Set the publisher liveliness lease to "
            f"<= {sub.liveliness_lease_ms}ms, or remove the subscriber lease "
            f"constraint."
        )
    elif (pub.liveliness_lease_ms > 0 and sub.liveliness_lease_ms > 0
            and pub.liveliness_lease_ms > sub.liveliness_lease_ms):
        issues.append(
            f"INCOMPATIBLE LIVELINESS LEASE: Publisher lease ({pub.liveliness_lease_ms}ms) "
            f"exceeds subscriber lease ({sub.liveliness_lease_ms}ms). "
            f"DDS requires offered lease <= requested lease. Connection will silently fail."
        )
        suggestions.append(
            f"Fix: Either decrease the publisher liveliness lease to "
            f"<= {sub.liveliness_lease_ms}ms, or increase the subscriber lease "
            f"to >= {pub.liveliness_lease_ms}ms."
        )

    compatible = len(issues) == 0
    return CompatibilityResult(compatible, issues, warnings, suggestions)


def check_vendor_specific(pub: QoSProfile, sub: QoSProfile,
                          vendor: DDSVendor) -> list[str]:
    """Return vendor-specific warnings for known DDS implementation quirks.

    These are behaviors that differ between DDS vendors and can cause
    subtle production issues even when QoS profiles are technically compatible.
    """
    warnings = []

    if vendor == DDSVendor.FASTDDS:
        # FastDDS specific quirks
        if pub.history == History.KEEP_LAST and pub.depth > 5000:
            warnings.append(
                f"[FastDDS] Publisher depth ({pub.depth}) is very large. "
                f"FastDDS allocates history depth upfront in PREALLOCATED mode, "
                f"causing high memory usage. Consider PREALLOCATED_WITH_REALLOC "
                f"or reduce depth.")

        if (pub.reliability == Reliability.RELIABLE
                and pub.history == History.KEEP_LAST and pub.depth == 1):
            warnings.append(
                "[FastDDS] RELIABLE + KEEP_LAST(1): FastDDS may block the "
                "publisher if the subscriber is slow to acknowledge. "
                "Increase depth or use asynchronous publish mode.")

        if pub.durability == Durability.TRANSIENT_LOCAL:
            warnings.append(
                "[FastDDS] TRANSIENT_LOCAL durability: FastDDS stores samples "
                "in the DataWriter history cache. With large messages, this "
                "increases memory significantly. Monitor with 'fastdds shm'.")

        if (pub.liveliness == Liveliness.MANUAL_BY_TOPIC
                and pub.liveliness_lease_ms > 0
                and pub.liveliness_lease_ms < 100):
            warnings.append(
                f"[FastDDS] MANUAL_BY_TOPIC with lease {pub.liveliness_lease_ms}ms: "
                f"FastDDS liveliness assertion granularity can be coarse. "
                f"Leases under 100ms may trigger false liveliness-lost events.")

    elif vendor == DDSVendor.CYCLONEDDS:
        # CycloneDDS specific quirks
        if pub.history == History.KEEP_ALL:
            warnings.append(
                "[CycloneDDS] KEEP_ALL history: CycloneDDS uses a shared memory "
                "pool (max_samples). Default is 256 samples across ALL topics. "
                "Set CYCLONEDDS_URI to increase MaxSamples for high-throughput "
                "topics.")

        if (pub.reliability == Reliability.RELIABLE
                and sub.reliability == Reliability.RELIABLE):
            warnings.append(
                "[CycloneDDS] RELIABLE+RELIABLE: CycloneDDS uses a synchronous "
                "delivery model. Large messages with RELIABLE can cause "
                "head-of-line blocking. Set WHC (Writer History Cache) "
                "high_watermark in CYCLONEDDS_URI for large payloads.")

        if pub.deadline_ms > 0 and pub.deadline_ms < 10:
            warnings.append(
                f"[CycloneDDS] Deadline {pub.deadline_ms}ms: CycloneDDS deadline "
                f"check resolution depends on the internal timer. Sub-10ms "
                f"deadlines may not trigger missed-deadline events reliably.")

    elif vendor == DDSVendor.CONNEXT:
        # RTI Connext specific quirks
        if pub.history == History.KEEP_LAST and pub.depth > 10000:
            warnings.append(
                f"[Connext] Publisher depth ({pub.depth}) exceeds typical "
                f"Connext resource limits. Check max_samples_per_instance "
                f"in QOS XML profile. Default is 32 in some configurations.")

        if (pub.durability == Durability.TRANSIENT_LOCAL
                and sub.durability == Durability.TRANSIENT_LOCAL):
            warnings.append(
                "[Connext] Both TRANSIENT_LOCAL: Connext implements durable "
                "subscriptions via a built-in persistence service. Ensure "
                "DurabilityService.history_depth is configured in the XML "
                "QoS profile.")

        if (pub.reliability == Reliability.RELIABLE
                and pub.history == History.KEEP_ALL):
            warnings.append(
                "[Connext] RELIABLE + KEEP_ALL: Connext will block the writer "
                "when resource limits are reached (max_samples). Set "
                "reliability.max_blocking_time in QoS XML to avoid "
                "indefinite blocking.")

    return warnings


def print_result(pub: QoSProfile, sub: QoSProfile, result: CompatibilityResult,
                 vendor_warnings: list | None = None) -> None:
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

    if vendor_warnings:
        print()
        print("DDS Vendor Warnings:")
        for vw in vendor_warnings:
            print(f"  [DDS]   {vw}")

    if result.suggestions:
        print()
        print("Suggestions:")
        for suggestion in result.suggestions:
            print(f"  -> {suggestion}")

    print("=" * 60)


def print_result_json(pub: QoSProfile, sub: QoSProfile, result: CompatibilityResult,
                      vendor_warnings: list | None = None) -> None:
    """Print compatibility check results as JSON."""
    output = {
        "compatible": result.compatible,
        "warnings": result.warnings,
        "errors": result.issues,
        "suggestions": result.suggestions,
        "vendor_warnings": vendor_warnings or [],
        "publisher": pub.to_dict(),
        "subscriber": sub.to_dict(),
    }
    print(json.dumps(output, indent=2))


def main():
    parser = argparse.ArgumentParser(
        description="Check QoS compatibility between publisher and subscriber profiles",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
Examples:
  %(prog)s --pub reliable,volatile,keep_last,1 --sub reliable,volatile,keep_last,1
  %(prog)s --preset sensor
  %(prog)s --preset command
  %(prog)s --pub reliable,volatile,keep_last,1,100,0,automatic,0 \\
           --sub reliable,volatile,keep_last,1,50,0,automatic,0 --json

Extended format: reliability,durability,history,depth,deadline_ms,
                 lifespan_ms,liveliness,liveliness_lease_ms
Presets: sensor, command, map, diagnostics, parameter_events, action_feedback, safety_heartbeat
        """)
    parser.add_argument("--version", action="version",
                        version=f"%(prog)s {__version__}")
    parser.add_argument(
        "--pub",
        help="Publisher QoS: reliability,durability,history,depth"
             "[,deadline_ms,lifespan_ms,liveliness,liveliness_lease_ms] "
             "or shorthand: reliable, best_effort, transient_local, volatile")
    parser.add_argument(
        "--sub",
        help="Subscriber QoS: reliability,durability,history,depth"
             "[,deadline_ms,lifespan_ms,liveliness,liveliness_lease_ms] "
             "or shorthand: reliable, best_effort, transient_local, volatile")
    parser.add_argument("--preset", choices=PRESETS.keys(),
                        help="Use a predefined QoS preset")
    parser.add_argument("--json", action="store_true", default=False,
                        help="Output results as JSON")
    parser.add_argument("--dds-vendor",
                        choices=["auto", "fastdds", "cyclonedds", "connext"],
                        default="auto",
                        help="DDS vendor for implementation-specific warnings "
                             "(default: auto = no vendor-specific checks)")
    args = parser.parse_args()

    if args.preset:
        pub = PRESETS[args.preset]["pub"]
        sub = PRESETS[args.preset]["sub"]
        if not args.json:
            print(f"Using preset: {args.preset}")
    elif args.pub and args.sub:
        pub = parse_qos_string(args.pub, "Publisher")
        sub = parse_qos_string(args.sub, "Subscriber")
    else:
        parser.print_help()
        print("\nError: Provide either --preset or both --pub and --sub", file=sys.stderr)
        sys.exit(1)

    result = check_compatibility(pub, sub)

    vendor = DDSVendor(args.dds_vendor)
    vendor_warnings = []
    if vendor != DDSVendor.AUTO:
        vendor_warnings = check_vendor_specific(pub, sub, vendor)

    if args.json:
        print_result_json(pub, sub, result, vendor_warnings)
    else:
        print_result(pub, sub, result, vendor_warnings)

    sys.exit(0 if result.compatible else 1)


if __name__ == "__main__":
    main()
