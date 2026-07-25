#!/usr/bin/env python3
"""Analyze Vault or cloud secret manager audit logs for anomalies.

Reads JSON-lines or JSON-array audit log files and flags unusual access
patterns including volume spikes, off-hours access, new source IPs,
and failed authentication attempts.

Usage:
    python audit_log_analyzer.py --log-file vault-audit.log --threshold 5
    python audit_log_analyzer.py --log-file audit.json --threshold 3 --json

Expected log entry format (JSON lines or JSON array):
{
  "timestamp": "2026-03-20T14:32:00Z",
  "type": "request",
  "auth": {"accessor": "token-abc123", "entity_id": "eid-001", "display_name": "approle-payment-svc"},
  "request": {"path": "secret/data/production/payment/api-keys", "operation": "read"},
  "response": {"status_code": 200},
  "remote_address": "10.0.1.15"
}

Fields are optional — the analyzer works with whatever is available.
"""

import argparse
import json
import sys
import textwrap
from collections import defaultdict
from datetime import datetime


def load_logs(path):
    """Load audit log entries from file. Supports JSON lines and JSON array."""
    entries = []
    try:
        with open(path, "r") as f:
            content = f.read().strip()
    except FileNotFoundError:
        print(f"ERROR: Log file not found: {path}", file=sys.stderr)
        sys.exit(1)

    if not content:
        return entries

    # Try JSON array first
    if content.startswith("["):
        try:
            entries = json.loads(content)
            return entries
        except json.JSONDecodeError:
            pass

    # Try JSON lines
    for i, line in enumerate(content.split("\n"), 1):
        line = line.strip()
        if not line:
            continue
        try:
            entries.append(json.loads(line))
        except json.JSONDecodeError:
            print(f"WARNING: Skipping malformed line {i}", file=sys.stderr)

    return entries


def extract_fields(entry):
    """Extract normalized fields from a log entry."""
    timestamp_raw = entry.get("timestamp", entry.get("time", ""))
    ts = None
    if timestamp_raw:
        for fmt in ("%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S.%fZ", "%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%d %H:%M:%S"):
            try:
                ts = datetime.strptime(timestamp_raw.replace("+00:00", "Z").rstrip("Z") + "Z", fmt.rstrip("Z") + "Z") if "Z" not in fmt else datetime.strptime(timestamp_raw, fmt)
                break
            except (ValueError, TypeError):
                continue
        if ts is None:
            # Fallback: try basic parse
            try:
                ts = datetime.fromisoformat(timestamp_raw.replace("Z", "+00:00").replace("+00:00", ""))
            except (ValueError, TypeError):
                pass

    auth = entry.get("auth", {})
    request = entry.get("request", {})
    response = entry.get("response", {})

    return {
        "timestamp": ts,
        "hour": ts.hour if ts else None,
        "identity": auth.get("display_name", auth.get("entity_id", "unknown")),
        "path": request.get("path", entry.get("path", "unknown")),
        "operation": request.get("operation", entry.get("operation", "unknown")),
        "status_code": response.get("status_code", entry.get("status_code")),
        "remote_address": entry.get("remote_address", entry.get("source_address", "unknown")),
        "entry_type": entry.get("type", "unknown"),
    }


def analyze(entries, threshold):
    """Run anomaly detection across all log entries."""
    parsed = [extract_fields(e) for e in entries]

    # Counters
    access_by_identity = defaultdict(int)
    access_by_path = defaultdict(int)
    access_by_ip = defaultdict(set)        # identity -> set of IPs
    ip_to_identities = defaultdict(set)    # IP -> set of identities
    failed_by_source = defaultdict(int)
    off_hours_access = []
    path_by_identity = defaultdict(set)    # identity -> set of paths
    hourly_distribution = defaultdict(int)

    for p in parsed:
        identity = p["identity"]
        path = p["path"]
        ip = p["remote_address"]
        status = p["status_code"]
        hour = p["hour"]

        access_by_identity[identity] += 1
        access_by_path[path] += 1
        access_by_ip[identity].add(ip)
        ip_to_identities[ip].add(identity)
        path_by_identity[identity].add(path)

        if hour is not None:
            hourly_distribution[hour] += 1

        # Failed access (non-200 or 4xx/5xx)
        if status and (status >= 400 or status == 0):
            failed_by_source[f"{identity}@{ip}"] += 1

        # Off-hours: before 6 AM or after 10 PM
        if hour is not None and (hour < 6 or hour >= 22):
            off_hours_access.append(p)

    # Build anomalies
    anomalies = []

    # 1. Volume spikes — identities accessing secrets more than threshold * average
    if access_by_identity:
        avg_access = sum(access_by_identity.values()) / len(access_by_identity)
        spike_threshold = max(threshold * avg_access, threshold)
        for identity, count in access_by_identity.items():
            if count >= spike_threshold:
                anomalies.append({
                    "type": "volume_spike",
                    "severity": "HIGH",
                    "identity": identity,
                    "access_count": count,
                    "threshold": round(spike_threshold, 1),
                    "description": f"Identity '{identity}' made {count} accesses (threshold: {round(spike_threshold, 1)})",
                })

    # 2. Multi-IP access — single identity from many IPs
    for identity, ips in access_by_ip.items():
        if len(ips) >= threshold:
            anomalies.append({
                "type": "multi_ip_access",
                "severity": "MEDIUM",
                "identity": identity,
                "ip_count": len(ips),
                "ips": sorted(ips),
                "description": f"Identity '{identity}' accessed from {len(ips)} different IPs",
            })

    # 3. Failed access attempts
    for source, count in failed_by_source.items():
        if count >= threshold:
            anomalies.append({
                "type": "failed_access",
                "severity": "HIGH",
                "source": source,
                "failure_count": count,
                "description": f"Source '{source}' had {count} failed access attempts",
            })

    # 4. Off-hours access
    if off_hours_access:
        off_hours_identities = defaultdict(int)
        for p in off_hours_access:
            off_hours_identities[p["identity"]] += 1

        for identity, count in off_hours_identities.items():
            if count >= max(threshold, 2):
                anomalies.append({
                    "type": "off_hours_access",
                    "severity": "MEDIUM",
                    "identity": identity,
                    "access_count": count,
                    "description": f"Identity '{identity}' made {count} accesses outside business hours (before 6 AM / after 10 PM)",
                })

    # 5. Broad path access — single identity touching many paths
    for identity, paths in path_by_identity.items():
        if len(paths) >= threshold * 2:
            anomalies.append({
                "type": "broad_access",
                "severity": "MEDIUM",
                "identity": identity,
                "path_count": len(paths),
                "paths": sorted(paths)[:10],
                "description": f"Identity '{identity}' accessed {len(paths)} distinct secret paths",
            })

    # Sort anomalies by severity
    severity_order = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}
    anomalies.sort(key=lambda x: severity_order.get(x["severity"], 4))

    # Summary stats
    summary = {
        "total_entries": len(entries),
        "parsed_entries": len(parsed),
        "unique_identities": len(access_by_identity),
        "unique_paths": len(access_by_path),
        "unique_source_ips": len(ip_to_identities),
        "total_failures": sum(failed_by_source.values()),
        "off_hours_events": len(off_hours_access),
        "anomalies_found": len(anomalies),
    }

    # Top accessed paths
    top_paths = sorted(access_by_path.items(), key=lambda x: -x[1])[:10]

    return {
        "summary": summary,
        "anomalies": anomalies,
        "top_accessed_paths": [{"path": p, "count": c} for p, c in top_paths],
        "hourly_distribution": dict(sorted(hourly_distribution.items())),
    }


def print_human(result, threshold):
    """Print human-readable analysis report."""
    summary = result["summary"]
    anomalies = result["anomalies"]

    print("=== Audit Log Analysis Report ===")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"Anomaly threshold: {threshold}")
    print()

    print("--- Summary ---")
    print(f"  Total log entries:     {summary['total_entries']}")
    print(f"  Unique identities:     {summary['unique_identities']}")
    print(f"  Unique secret paths:   {summary['unique_paths']}")
    print(f"  Unique source IPs:     {summary['unique_source_ips']}")
    print(f"  Total failures:        {summary['total_failures']}")
    print(f"  Off-hours events:      {summary['off_hours_events']}")
    print(f"  Anomalies detected:    {summary['anomalies_found']}")
    print()

    if anomalies:
        print("--- Anomalies ---")
        for i, a in enumerate(anomalies, 1):
            print(f"  [{a['severity']}] {a['type']}: {a['description']}")
        print()
    else:
        print("--- No anomalies detected ---")
        print()

    if result["top_accessed_paths"]:
        print("--- Top Accessed Paths ---")
        for item in result["top_accessed_paths"]:
            print(f"  {item['count']:5d}  {item['path']}")
        print()

    if result["hourly_distribution"]:
        print("--- Hourly Distribution ---")
        max_count = max(result["hourly_distribution"].values()) if result["hourly_distribution"] else 1
        for hour in range(24):
            count = result["hourly_distribution"].get(hour, 0)
            bar_len = int((count / max_count) * 40) if max_count > 0 else 0
            marker = " *" if (hour < 6 or hour >= 22) else ""
            print(f"  {hour:02d}:00  {'#' * bar_len:40s}  {count}{marker}")
        print("  (* = off-hours)")


# Embedded synthetic audit log — exercises volume-spike + off-hours + failed-access
# detectors so --sample produces a non-trivial report without a real log file.
SAMPLE_ENTRIES = [
    {"timestamp": "2026-03-20T03:14:00Z", "type": "request",
     "auth": {"display_name": "approle-payment-svc"},
     "request": {"path": "secret/data/production/payment/api-keys", "operation": "read"},
     "response": {"status_code": 200}, "remote_address": "10.0.1.15"},
    {"timestamp": "2026-03-20T03:15:00Z", "type": "request",
     "auth": {"display_name": "approle-payment-svc"},
     "request": {"path": "secret/data/production/payment/db", "operation": "read"},
     "response": {"status_code": 200}, "remote_address": "10.0.1.99"},
    {"timestamp": "2026-03-20T03:16:00Z", "type": "request",
     "auth": {"display_name": "approle-payment-svc"},
     "request": {"path": "secret/data/production/payment/jwt", "operation": "read"},
     "response": {"status_code": 403}, "remote_address": "203.0.113.7"},
    {"timestamp": "2026-03-20T03:17:00Z", "type": "request",
     "auth": {"display_name": "approle-payment-svc"},
     "request": {"path": "secret/data/production/payment/jwt", "operation": "read"},
     "response": {"status_code": 403}, "remote_address": "203.0.113.7"},
    {"timestamp": "2026-03-20T14:00:00Z", "type": "request",
     "auth": {"display_name": "ci-runner"},
     "request": {"path": "secret/data/ci/tokens", "operation": "read"},
     "response": {"status_code": 200}, "remote_address": "10.0.2.20"},
]


def main():
    parser = argparse.ArgumentParser(
        description="Analyze Vault/cloud secret manager audit logs for anomalies.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            The analyzer detects:
              - Volume spikes (identity accessing secrets above threshold * average)
              - Multi-IP access (single identity from many source IPs)
              - Failed access attempts (repeated auth/access failures)
              - Off-hours access (before 6 AM or after 10 PM)
              - Broad path access (single identity accessing many distinct paths)

            Log format: JSON lines or JSON array. Each entry should include
            timestamp, auth info, request path/operation, response status,
            and remote address. Missing fields are handled gracefully.

            Examples:
              %(prog)s --log-file vault-audit.log --threshold 5
              %(prog)s --log-file audit.json --threshold 3 --json
        """),
    )
    parser.add_argument("--log-file", help="Path to audit log file (JSON lines or JSON array)")
    parser.add_argument(
        "--threshold",
        type=int,
        default=5,
        help="Anomaly sensitivity threshold — lower = more sensitive (default: 5)",
    )
    parser.add_argument("--json", action="store_true", dest="json_output", help="Output as JSON")
    parser.add_argument("--sample", action="store_true",
                        help="Analyze an embedded synthetic audit log")

    args = parser.parse_args()

    if args.sample:
        entries = SAMPLE_ENTRIES
        log_file = "<embedded sample>"
        threshold = 2
    else:
        if not args.log_file:
            parser.error("--log-file is required (or use --sample)")
        entries = load_logs(args.log_file)
        log_file = args.log_file
        threshold = args.threshold

    if not entries:
        print("No log entries found in file.", file=sys.stderr)
        sys.exit(1)

    result = analyze(entries, threshold)
    result["log_file"] = log_file
    result["threshold"] = threshold
    result["analyzed_at"] = datetime.now().isoformat()

    if args.json_output:
        print(json.dumps(result, indent=2))
    else:
        print_human(result, threshold)


if __name__ == "__main__":
    main()
