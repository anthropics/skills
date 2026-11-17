#!/usr/bin/env python3
"""Validate QoS compatibility for rosbag2 recording/playback.

When replaying a rosbag, the bag's recorded QoS profiles (stored in
metadata.yaml) must be compatible with live subscribers. This tool
checks for mismatches before you discover them at runtime.

Usage:
    python rosbag2_qos_checker.py path/to/metadata.yaml
    python rosbag2_qos_checker.py path/to/metadata.yaml --sub reliable,transient_local,keep_last,1
    python rosbag2_qos_checker.py path/to/metadata.yaml --json
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Optional

try:
    import yaml  # type: ignore[import-untyped]
    HAS_YAML = True
except ImportError:
    HAS_YAML = False

__version__ = "0.1.0"

# Import QoS types from the main checker
import os
sys.path.insert(0, os.path.dirname(__file__))
from qos_checker import (  # noqa: E402
    QoSProfile, Reliability, Durability, History, Liveliness,
    check_compatibility,
)


def _parse_yaml_qos(qos_dict: dict, label: str = "") -> Optional[QoSProfile]:
    """Parse a QoS profile from rosbag2 metadata YAML format."""
    try:
        reliability_map = {
            "reliable": Reliability.RELIABLE,
            "best_effort": Reliability.BEST_EFFORT,
            1: Reliability.RELIABLE,
            2: Reliability.BEST_EFFORT,
        }
        durability_map = {
            "transient_local": Durability.TRANSIENT_LOCAL,
            "volatile": Durability.VOLATILE,
            1: Durability.TRANSIENT_LOCAL,
            2: Durability.VOLATILE,
        }
        history_map = {
            "keep_last": History.KEEP_LAST,
            "keep_all": History.KEEP_ALL,
            1: History.KEEP_LAST,
            2: History.KEEP_ALL,
        }
        liveliness_map = {
            "automatic": Liveliness.AUTOMATIC,
            "manual_by_topic": Liveliness.MANUAL_BY_TOPIC,
            1: Liveliness.AUTOMATIC,
            2: Liveliness.MANUAL_BY_TOPIC,
        }

        reliability_val = qos_dict.get("reliability", "reliable")
        if isinstance(reliability_val, str):
            reliability_val = reliability_val.lower()
        reliability = reliability_map.get(reliability_val, Reliability.RELIABLE)

        durability_val = qos_dict.get("durability", "volatile")
        if isinstance(durability_val, str):
            durability_val = durability_val.lower()
        durability = durability_map.get(durability_val, Durability.VOLATILE)

        history_val = qos_dict.get("history", "keep_last")
        if isinstance(history_val, str):
            history_val = history_val.lower()
        history = history_map.get(history_val, History.KEEP_LAST)

        depth = int(qos_dict.get("depth", 10))

        liveliness_val = qos_dict.get("liveliness", "automatic")
        if isinstance(liveliness_val, str):
            liveliness_val = liveliness_val.lower()
        liveliness = liveliness_map.get(liveliness_val, Liveliness.AUTOMATIC)

        # Deadline/lifespan can be stored as nanoseconds or dict
        deadline_ms = _extract_duration_ms(qos_dict.get("deadline", 0))
        lifespan_ms = _extract_duration_ms(qos_dict.get("lifespan", 0))
        lease_ms = _extract_duration_ms(
            qos_dict.get("liveliness_lease_duration", 0))

        return QoSProfile(
            reliability=reliability,
            durability=durability,
            history=history,
            depth=depth,
            label=label,
            deadline_ms=deadline_ms,
            lifespan_ms=lifespan_ms,
            liveliness=liveliness,
            liveliness_lease_ms=lease_ms,
        )
    except (KeyError, ValueError, TypeError):
        return None


def _extract_duration_ms(val: object) -> int:
    """Extract milliseconds from rosbag2 duration formats.

    rosbag2 metadata stores durations as nanoseconds (int) or as
    {"sec": N, "nsec": N} dicts.  We always convert to milliseconds.
    """
    if isinstance(val, (int, float)):
        # rosbag2 stores durations in nanoseconds
        return int(val / 1_000_000)
    if isinstance(val, dict):
        sec = int(val.get("sec", 0))
        nsec = int(val.get("nsec", 0) or val.get("nanosec", 0))
        return int(sec * 1000 + nsec / 1_000_000)
    return 0


def parse_metadata(metadata_path: str) -> list[dict]:
    """Parse rosbag2 metadata.yaml and extract topic QoS profiles.

    Returns a list of dicts with keys: topic, type, qos_profiles.
    """
    if not HAS_YAML:
        print("Error: PyYAML is required. Install with: pip install pyyaml",
              file=sys.stderr)
        sys.exit(1)

    path = Path(metadata_path)
    if not path.exists():
        print(f"Error: File not found: {metadata_path}", file=sys.stderr)
        sys.exit(1)

    content = path.read_text()
    data = yaml.safe_load(content)

    if data is None:
        return []

    # Handle both rosbag2 metadata formats
    if "rosbag2_bagfile_information" in data:
        bag_info = data["rosbag2_bagfile_information"]
    else:
        bag_info = data

    topics_with_qos = []
    topics = bag_info.get("topics_with_message_count", [])
    for topic_entry in topics:
        topic_meta = topic_entry.get("topic_metadata", topic_entry)
        topic_name = topic_meta.get("name", topic_meta.get("topic", ""))
        msg_type = topic_meta.get("type", "")

        # QoS profiles can be a YAML string or a list of dicts
        offered_qos = topic_meta.get(
            "offered_qos_profiles",
            topic_meta.get("qos_profile", ""))

        qos_profiles = []
        if isinstance(offered_qos, str) and offered_qos:
            try:
                parsed = yaml.safe_load(offered_qos)
                if isinstance(parsed, list):
                    qos_profiles = parsed
                elif isinstance(parsed, dict):
                    qos_profiles = [parsed]
            except yaml.YAMLError:
                pass
        elif isinstance(offered_qos, list):
            qos_profiles = offered_qos
        elif isinstance(offered_qos, dict):
            qos_profiles = [offered_qos]

        topics_with_qos.append({
            "topic": topic_name,
            "type": msg_type,
            "qos_profiles": qos_profiles,
        })

    return topics_with_qos


def check_playback_compatibility(
    topics_qos: list[dict],
    subscriber_qos: Optional[QoSProfile] = None,
) -> dict:
    """Check if recorded QoS profiles are compatible with playback.

    Returns a dict with per-topic results and an overall summary.
    """
    topic_results: list[dict] = []
    global_warnings: list[str] = []
    compatible_count = 0
    incompatible_count = 0

    for topic_info in topics_qos:
        topic_name = topic_info["topic"]
        msg_type = topic_info["type"]
        qos_profiles = topic_info["qos_profiles"]

        topic_issues: list[str] = []
        topic_warnings: list[str] = []
        topic_result = {
            "topic": topic_name,
            "type": msg_type,
            "recorded_profiles": len(qos_profiles),
            "issues": topic_issues,
            "warnings": topic_warnings,
        }

        if not qos_profiles:
            topic_warnings.append(
                "No QoS profile recorded. rosbag2 will use default QoS "
                "for playback, which may not match the original publisher.")
            global_warnings.append(
                f"Topic '{topic_name}': no recorded QoS profile.")
        else:
            for i, qos_dict in enumerate(qos_profiles):
                pub_profile = _parse_yaml_qos(
                    qos_dict,
                    label=f"Recorded[{topic_name}][{i}]")
                if pub_profile is None:
                    topic_warnings.append(
                        f"Could not parse QoS profile #{i}.")
                    continue

                # Check against subscriber QoS if provided
                if subscriber_qos:
                    compat = check_compatibility(pub_profile, subscriber_qos)
                    if not compat.compatible:
                        topic_issues.extend(compat.issues)
                    topic_warnings.extend(compat.warnings)

                # Check for playback-specific concerns
                if pub_profile.durability == Durability.TRANSIENT_LOCAL:
                    topic_warnings.append(
                        "TRANSIENT_LOCAL recorded: on playback, rosbag2 "
                        "publishes with the same durability. Late-joining "
                        "subscribers will receive the last message.")

        has_issues = len(topic_issues) > 0
        if has_issues:
            incompatible_count += 1
        else:
            compatible_count += 1
        topic_results.append(topic_result)

    return {
        "topics": topic_results,
        "total_topics": len(topics_qos),
        "compatible_topics": compatible_count,
        "incompatible_topics": incompatible_count,
        "warnings": global_warnings,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Validate QoS compatibility for rosbag2 playback",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
Examples:
  %(prog)s path/to/metadata.yaml
  %(prog)s path/to/metadata.yaml --sub reliable,transient_local,keep_last,1
  %(prog)s path/to/metadata.yaml --json
        """)
    parser.add_argument("--version", action="version",
                        version=f"%(prog)s {__version__}")
    parser.add_argument("metadata", help="Path to rosbag2 metadata.yaml")
    parser.add_argument(
        "--sub",
        help="Subscriber QoS to check against: "
             "reliability,durability,history,depth "
             "or shorthand: reliable, best_effort, transient_local, volatile")
    parser.add_argument("--json", action="store_true", default=False,
                        help="Output results as JSON")
    args = parser.parse_args()

    topics_qos = parse_metadata(args.metadata)

    sub_qos = None
    if args.sub:
        from qos_checker import parse_qos_string
        sub_qos = parse_qos_string(args.sub, "Subscriber")

    results = check_playback_compatibility(topics_qos, sub_qos)

    if args.json:
        print(json.dumps(results, indent=2))
    else:
        print(f"Rosbag2 QoS Check: {results['total_topics']} topic(s)")
        print("=" * 60)
        for topic in results["topics"]:
            status = "OK" if not topic["issues"] else "INCOMPATIBLE"
            print(f"\n  [{status}] {topic['topic']} ({topic['type']})")
            print(f"         Recorded QoS profiles: {topic['recorded_profiles']}")
            for issue in topic["issues"]:
                print(f"         [ERROR] {issue}")
            for warn in topic["warnings"]:
                print(f"         [WARN]  {warn}")
        print()
        print(f"Summary: {results['compatible_topics']} compatible, "
              f"{results['incompatible_topics']} incompatible")
        if results["warnings"]:
            print(f"         {len(results['warnings'])} global warning(s)")

    sys.exit(1 if results["incompatible_topics"] > 0 else 0)


if __name__ == "__main__":
    main()
