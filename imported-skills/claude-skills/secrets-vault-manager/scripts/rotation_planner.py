#!/usr/bin/env python3
"""Create a rotation schedule from a secret inventory file.

Reads a JSON inventory of secrets and produces a rotation plan based on
the selected policy (30d, 60d, 90d) with urgency classification.

Usage:
    python rotation_planner.py --inventory secrets.json --policy 30d
    python rotation_planner.py --inventory secrets.json --policy 90d --json

Inventory file format (JSON):
[
  {
    "name": "prod-db-password",
    "type": "database",
    "store": "vault",
    "last_rotated": "2026-01-15",
    "owner": "platform-team",
    "environment": "production"
  },
  ...
]
"""

import argparse
import json
import sys
import textwrap
from datetime import datetime, timedelta


POLICY_DAYS = {
    "30d": 30,
    "60d": 60,
    "90d": 90,
}

# Default rotation period by secret type if not overridden by policy
TYPE_DEFAULTS = {
    "database": 30,
    "api-key": 90,
    "tls-certificate": 60,
    "ssh-key": 90,
    "service-token": 1,
    "encryption-key": 90,
    "oauth-secret": 90,
    "password": 30,
}

URGENCY_THRESHOLDS = {
    "critical": 0,    # Already overdue
    "high": 7,         # Due within 7 days
    "medium": 14,      # Due within 14 days
    "low": 30,         # Due within 30 days
}


def load_inventory(path):
    """Load and validate secret inventory from JSON file."""
    try:
        with open(path, "r") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: Inventory file not found: {path}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON in {path}: {e}", file=sys.stderr)
        sys.exit(1)

    if not isinstance(data, list):
        print("ERROR: Inventory must be a JSON array of secret objects", file=sys.stderr)
        sys.exit(1)

    validated = []
    for i, entry in enumerate(data):
        if not isinstance(entry, dict):
            print(f"WARNING: Skipping entry {i} — not an object", file=sys.stderr)
            continue

        name = entry.get("name", f"unnamed-{i}")
        secret_type = entry.get("type", "unknown")
        last_rotated = entry.get("last_rotated")

        if not last_rotated:
            print(f"WARNING: '{name}' has no last_rotated date — marking as overdue", file=sys.stderr)
            last_rotated_dt = None
        else:
            try:
                last_rotated_dt = datetime.strptime(last_rotated, "%Y-%m-%d")
            except ValueError:
                print(f"WARNING: '{name}' has invalid date '{last_rotated}' — marking as overdue", file=sys.stderr)
                last_rotated_dt = None

        validated.append({
            "name": name,
            "type": secret_type,
            "store": entry.get("store", "unknown"),
            "last_rotated": last_rotated_dt,
            "owner": entry.get("owner", "unassigned"),
            "environment": entry.get("environment", "unknown"),
        })

    return validated


def compute_schedule(inventory, policy_days):
    """Compute rotation schedule for each secret."""
    now = datetime.now()
    schedule = []

    for secret in inventory:
        # Determine rotation interval
        type_default = TYPE_DEFAULTS.get(secret["type"], 90)
        rotation_interval = min(policy_days, type_default)

        if secret["last_rotated"] is None:
            days_since = 999
            next_rotation = now  # Immediate
            days_until = -999
        else:
            days_since = (now - secret["last_rotated"]).days
            next_rotation = secret["last_rotated"] + timedelta(days=rotation_interval)
            days_until = (next_rotation - now).days

        # Classify urgency
        if days_until <= URGENCY_THRESHOLDS["critical"]:
            urgency = "CRITICAL"
        elif days_until <= URGENCY_THRESHOLDS["high"]:
            urgency = "HIGH"
        elif days_until <= URGENCY_THRESHOLDS["medium"]:
            urgency = "MEDIUM"
        else:
            urgency = "LOW"

        schedule.append({
            "name": secret["name"],
            "type": secret["type"],
            "store": secret["store"],
            "owner": secret["owner"],
            "environment": secret["environment"],
            "last_rotated": secret["last_rotated"].strftime("%Y-%m-%d") if secret["last_rotated"] else "NEVER",
            "rotation_interval_days": rotation_interval,
            "next_rotation": next_rotation.strftime("%Y-%m-%d"),
            "days_until_due": days_until,
            "days_since_rotation": days_since,
            "urgency": urgency,
        })

    # Sort by urgency (critical first), then by days until due
    urgency_order = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}
    schedule.sort(key=lambda x: (urgency_order.get(x["urgency"], 4), x["days_until_due"]))

    return schedule


def build_summary(schedule):
    """Build summary statistics."""
    total = len(schedule)
    by_urgency = {}
    by_type = {}
    by_owner = {}

    for entry in schedule:
        urg = entry["urgency"]
        by_urgency[urg] = by_urgency.get(urg, 0) + 1
        t = entry["type"]
        by_type[t] = by_type.get(t, 0) + 1
        o = entry["owner"]
        by_owner[o] = by_owner.get(o, 0) + 1

    return {
        "total_secrets": total,
        "by_urgency": by_urgency,
        "by_type": by_type,
        "by_owner": by_owner,
        "overdue_count": by_urgency.get("CRITICAL", 0),
        "due_within_7d": by_urgency.get("HIGH", 0),
    }


def print_human(schedule, summary, policy):
    """Print human-readable rotation plan."""
    print(f"=== Secret Rotation Plan (Policy: {policy}) ===")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"Total secrets: {summary['total_secrets']}")
    print()

    print("--- Urgency Summary ---")
    for urg in ["CRITICAL", "HIGH", "MEDIUM", "LOW"]:
        count = summary["by_urgency"].get(urg, 0)
        if count > 0:
            print(f"  {urg:10s}  {count}")
    print()

    if not schedule:
        print("No secrets in inventory.")
        return

    print("--- Rotation Schedule ---")
    print(f"  {'Name':30s}  {'Type':15s}  {'Urgency':10s}  {'Last Rotated':12s}  {'Next Due':12s}  {'Owner'}")
    print(f"  {'-'*30}  {'-'*15}  {'-'*10}  {'-'*12}  {'-'*12}  {'-'*15}")

    for entry in schedule:
        overdue_marker = " **OVERDUE**" if entry["urgency"] == "CRITICAL" else ""
        print(
            f"  {entry['name']:30s}  {entry['type']:15s}  {entry['urgency']:10s}  "
            f"{entry['last_rotated']:12s}  {entry['next_rotation']:12s}  "
            f"{entry['owner']}{overdue_marker}"
        )

    print()
    print("--- Action Items ---")
    critical = [e for e in schedule if e["urgency"] == "CRITICAL"]
    high = [e for e in schedule if e["urgency"] == "HIGH"]

    if critical:
        print(f"  IMMEDIATE: Rotate {len(critical)} overdue secret(s):")
        for e in critical:
            print(f"    - {e['name']} ({e['type']}, owner: {e['owner']})")
    if high:
        print(f"  THIS WEEK: Rotate {len(high)} secret(s) due within 7 days:")
        for e in high:
            print(f"    - {e['name']} (due: {e['next_rotation']}, owner: {e['owner']})")
    if not critical and not high:
        print("  No urgent rotations needed.")


def main():
    parser = argparse.ArgumentParser(
        description="Create rotation schedule from a secret inventory file.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Policies:
              30d   Aggressive — all secrets rotate within 30 days max
              60d   Standard — 60-day maximum rotation window
              90d   Relaxed — 90-day maximum rotation window

            Note: Some secret types (e.g., database passwords) have shorter
            built-in defaults that override the policy maximum.

            Example inventory file (secrets.json):
            [
              {"name": "prod-db", "type": "database", "store": "vault",
               "last_rotated": "2026-01-15", "owner": "platform-team",
               "environment": "production"}
            ]
        """),
    )
    parser.add_argument("--inventory", required=True, help="Path to JSON inventory file")
    parser.add_argument(
        "--policy",
        required=True,
        choices=["30d", "60d", "90d"],
        help="Rotation policy (maximum rotation interval)",
    )
    parser.add_argument("--json", action="store_true", dest="json_output", help="Output as JSON")

    args = parser.parse_args()

    policy_days = POLICY_DAYS[args.policy]
    inventory = load_inventory(args.inventory)
    schedule = compute_schedule(inventory, policy_days)
    summary = build_summary(schedule)

    result = {
        "policy": args.policy,
        "policy_days": policy_days,
        "generated_at": datetime.now().isoformat(),
        "summary": summary,
        "schedule": schedule,
    }

    if args.json_output:
        print(json.dumps(result, indent=2))
    else:
        print_human(schedule, summary, args.policy)


if __name__ == "__main__":
    main()
