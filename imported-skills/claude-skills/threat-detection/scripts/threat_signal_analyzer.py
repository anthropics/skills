#!/usr/bin/env python3
"""
threat_signal_analyzer.py — Threat Signal Analysis: Hunt, IOC Sweep, Anomaly Detection

Supports three analysis modes:
  hunt    — Score and prioritize a threat hunting hypothesis
  ioc     — Process IOC list and emit sweep targets with freshness check
  anomaly — Z-score behavioral anomaly detection against a baseline

Usage:
    python3 threat_signal_analyzer.py --mode hunt --hypothesis "APT using WMI for lateral movement" --json
    python3 threat_signal_analyzer.py --mode ioc --ioc-file iocs.json --json
    python3 threat_signal_analyzer.py --mode anomaly --events-file events.json --baseline-mean 45.0 --baseline-std 12.0 --json

Exit codes:
    0  No high-priority findings
    1  Medium-priority signals detected
    2  High-priority findings confirmed
"""

import argparse
import json
import re
import sys
from datetime import datetime, timezone

MITRE_PATTERN = r'T\d{4}(?:\.\d{3})?'

HUNT_DATA_SOURCES = {
    "initial_access": ["web_proxy_logs", "email_gateway_logs", "firewall_logs", "dns_logs"],
    "execution": ["edr_process_logs", "sysmon_event_1", "windows_event_4688", "auditd"],
    "persistence": ["windows_event_4698", "registry_logs", "cron_logs", "systemd_logs"],
    "privilege_escalation": ["windows_event_4672", "sudo_logs", "auditd", "edr_process_logs"],
    "defense_evasion": ["edr_process_logs", "windows_event_4663", "sysmon_event_11", "antivirus_logs"],
    "credential_access": ["windows_event_4625", "windows_event_4648", "lsass_access_events", "vault_audit_logs"],
    "discovery": ["windows_event_4688", "auditd", "network_flow_logs", "dns_logs"],
    "lateral_movement": ["windows_event_4624", "smb_logs", "winrm_logs", "network_flow_logs"],
    "collection": ["dlp_alerts", "file_access_logs", "clipboard_monitoring", "screen_capture_logs"],
    "command_and_control": ["dns_logs", "proxy_logs", "firewall_logs", "netflow_records"],
    "exfiltration": ["dlp_alerts", "firewall_logs", "proxy_logs", "dns_logs"],
}

IOC_SWEEP_TARGETS = {
    "ip": ["firewall_logs", "netflow_records", "proxy_logs", "threat_intel_platform"],
    "domain": ["dns_logs", "proxy_logs", "email_gateway_logs", "threat_intel_platform"],
    "hash": ["edr_hash_scanning", "antivirus_logs", "file_integrity_monitoring", "threat_intel_platform"],
    "url": ["proxy_logs", "email_gateway_logs", "browser_history_logs"],
    "email": ["email_gateway_logs", "dlp_alerts"],
    "user_agent": ["proxy_logs", "web_application_logs"],
}

IOC_MAX_AGE_DAYS = 30  # IOCs older than this are flagged as stale

HUNT_KEYWORDS = {
    "wmi": {"tactic": "lateral_movement", "mitre": "T1047", "data_source_key": "lateral_movement"},
    "powershell": {"tactic": "execution", "mitre": "T1059.001", "data_source_key": "execution"},
    "lolbin": {"tactic": "defense_evasion", "mitre": "T1218", "data_source_key": "defense_evasion"},
    "lolbas": {"tactic": "defense_evasion", "mitre": "T1218", "data_source_key": "defense_evasion"},
    "pass-the-hash": {"tactic": "lateral_movement", "mitre": "T1550.002", "data_source_key": "lateral_movement"},
    "pth": {"tactic": "lateral_movement", "mitre": "T1550.002", "data_source_key": "lateral_movement"},
    "credential dump": {"tactic": "credential_access", "mitre": "T1003", "data_source_key": "credential_access"},
    "mimikatz": {"tactic": "credential_access", "mitre": "T1003.001", "data_source_key": "credential_access"},
    "lateral": {"tactic": "lateral_movement", "mitre": "T1021", "data_source_key": "lateral_movement"},
    "persistence": {"tactic": "persistence", "mitre": "T1053", "data_source_key": "persistence"},
    "exfil": {"tactic": "exfiltration", "mitre": "T1041", "data_source_key": "exfiltration"},
    "beacon": {"tactic": "command_and_control", "mitre": "T1071", "data_source_key": "command_and_control"},
    "c2": {"tactic": "command_and_control", "mitre": "T1071", "data_source_key": "command_and_control"},
    "ransomware": {"tactic": "impact", "mitre": "T1486", "data_source_key": "execution"},
    "privilege": {"tactic": "privilege_escalation", "mitre": "T1068", "data_source_key": "privilege_escalation"},
    "injection": {"tactic": "defense_evasion", "mitre": "T1055", "data_source_key": "defense_evasion"},
    "apt": {"tactic": "initial_access", "mitre": "T1190", "data_source_key": "initial_access"},
    "supply chain": {"tactic": "initial_access", "mitre": "T1195", "data_source_key": "initial_access"},
    "phishing": {"tactic": "initial_access", "mitre": "T1566", "data_source_key": "initial_access"},
    "scheduled task": {"tactic": "persistence", "mitre": "T1053", "data_source_key": "persistence"},
}

ANOMALY_TIME_HOURS_SUSPICIOUS = list(range(0, 6)) + list(range(22, 24))


# ---------------------------------------------------------------------------
# Hunt mode
# ---------------------------------------------------------------------------

def hunt_mode(args):
    """Score and prioritize a threat hunting hypothesis."""
    hypothesis = args.hypothesis or ""
    hypothesis_lower = hypothesis.lower()

    # Extract T-code references via regex
    matched_tcodes = list(set(re.findall(MITRE_PATTERN, hypothesis, re.IGNORECASE)))

    # Keyword matching — multi-word keywords must be checked before single-word
    matched_keywords = []
    seen_keywords = set()
    sorted_keywords = sorted(HUNT_KEYWORDS.keys(), key=lambda k: -len(k))
    for kw in sorted_keywords:
        if kw in hypothesis_lower and kw not in seen_keywords:
            matched_keywords.append(kw)
            seen_keywords.add(kw)

    # Build tactic set from matched keywords and any T-codes that map to known tactics
    tactics = set()
    for kw in matched_keywords:
        tactics.add(HUNT_KEYWORDS[kw]["tactic"])

    # T-codes that happen to be in our keyword map (by mitre field)
    for tcode in matched_tcodes:
        for kw_data in HUNT_KEYWORDS.values():
            if kw_data["mitre"].upper() == tcode.upper():
                tactics.add(kw_data["tactic"])
                break

    # Collect data sources for matched tactics (deduped, ordered)
    data_sources_set = []
    seen_sources = set()
    for tactic in tactics:
        for src in HUNT_DATA_SOURCES.get(tactic, []):
            if src not in seen_sources:
                seen_sources.add(src)
                data_sources_set.append(src)

    # Scoring
    actor_relevance = getattr(args, "actor_relevance", 1)
    control_gap = getattr(args, "control_gap", 1)
    data_availability = getattr(args, "data_availability", 2)

    base_score = len(matched_keywords) * 2 + len(matched_tcodes) * 3
    priority_score = base_score + actor_relevance * 3 + control_gap * 2 + data_availability

    pursue_threshold = 5
    pursue_recommendation = priority_score >= pursue_threshold

    # Data quality check required if no data sources identified or low data_availability
    data_quality_check_required = len(data_sources_set) == 0 or data_availability < 2

    result = {
        "mode": "hunt",
        "hypothesis": hypothesis,
        "matched_keywords": matched_keywords,
        "matched_tcodes": matched_tcodes,
        "tactics": sorted(tactics),
        "data_sources_required": data_sources_set,
        "priority_score": priority_score,
        "pursue_recommendation": pursue_recommendation,
        "data_quality_check_required": data_quality_check_required,
        "score_breakdown": {
            "base_score": base_score,
            "actor_relevance_contribution": actor_relevance * 3,
            "control_gap_contribution": control_gap * 2,
            "data_availability_contribution": data_availability,
            "pursue_threshold": pursue_threshold,
        },
    }
    return result


# ---------------------------------------------------------------------------
# IOC mode
# ---------------------------------------------------------------------------

def ioc_mode(args):
    """Process IOC list and emit sweep targets with freshness check."""
    ioc_file = getattr(args, "ioc_file", None)
    ioc_date_str = getattr(args, "ioc_date", None)

    if not ioc_file:
        return {
            "mode": "ioc",
            "error": "--ioc-file is required for ioc mode",
        }

    try:
        with open(ioc_file, "r", encoding="utf-8") as fh:
            ioc_data = json.load(fh)
    except FileNotFoundError:
        return {"mode": "ioc", "error": f"IOC file not found: {ioc_file}"}
    except json.JSONDecodeError as exc:
        return {"mode": "ioc", "error": f"Invalid JSON in IOC file: {exc}"}

    # Normalise: accept both plural and singular key names
    type_key_map = {
        "ip": ["ip", "ips"],
        "domain": ["domain", "domains"],
        "hash": ["hash", "hashes"],
        "url": ["url", "urls"],
        "email": ["email", "emails"],
        "user_agent": ["user_agent", "user_agents"],
    }

    ioc_counts = {}
    ioc_values = {}  # type -> list of values
    for ioc_type, candidate_keys in type_key_map.items():
        for ck in candidate_keys:
            if ck in ioc_data:
                vals = ioc_data[ck]
                if isinstance(vals, list) and vals:
                    ioc_counts[ioc_type] = len(vals)
                    ioc_values[ioc_type] = vals
                break

    # Freshness check
    freshness_warning = False
    ioc_age_days = None
    if ioc_date_str:
        try:
            ioc_date = datetime.strptime(ioc_date_str, "%Y-%m-%d").replace(tzinfo=timezone.utc)
            now = datetime.now(tz=timezone.utc)
            ioc_age_days = (now - ioc_date).days
            if ioc_age_days > IOC_MAX_AGE_DAYS:
                freshness_warning = True
        except ValueError:
            pass  # invalid date format — skip freshness check

    # Build sweep plan
    sweep_plan = {}
    for ioc_type, count in ioc_counts.items():
        stale = freshness_warning  # applies to entire IOC batch
        sweep_plan[ioc_type] = {
            "count": count,
            "targets": IOC_SWEEP_TARGETS.get(ioc_type, []),
            "stale": stale,
        }

    # Coverage score: ratio of represented IOC types to total possible
    coverage_score = round(len(ioc_counts) / len(IOC_SWEEP_TARGETS), 4) if IOC_SWEEP_TARGETS else 0.0

    # Recommended action
    if freshness_warning:
        recommended_action = (
            "IOCs are stale (>{} days old). Re-validate against current threat intel feeds "
            "before sweeping. Prioritise re-enrichment in threat intel platform.".format(IOC_MAX_AGE_DAYS)
        )
    elif not ioc_counts:
        recommended_action = "No valid IOC types found in file. Verify JSON structure: expected keys ip, domain, hash, url, email."
    elif coverage_score < 0.5:
        recommended_action = (
            "Partial IOC coverage ({:.0%}). Supplement with additional IOC types for broader detection fidelity. "
            "Begin sweep in parallel.".format(coverage_score)
        )
    else:
        recommended_action = (
            "IOC set covers {:.0%} of sweep targets. Initiate concurrent sweep across all listed log sources. "
            "Escalate any matches immediately.".format(coverage_score)
        )

    result = {
        "mode": "ioc",
        "ioc_counts": ioc_counts,
        "sweep_plan": sweep_plan,
        "coverage_score": coverage_score,
        "freshness_warning": freshness_warning,
        "ioc_age_days": ioc_age_days,
        "recommended_action": recommended_action,
    }
    return result


# ---------------------------------------------------------------------------
# Anomaly mode
# ---------------------------------------------------------------------------

def anomaly_mode(args):
    """Z-score behavioral anomaly detection against a provided baseline."""
    events_file = getattr(args, "events_file", None)
    baseline_mean = getattr(args, "baseline_mean", None)
    baseline_std = getattr(args, "baseline_std", None)

    if not events_file:
        return {"mode": "anomaly", "error": "--events-file is required for anomaly mode"}
    if baseline_mean is None or baseline_std is None:
        return {"mode": "anomaly", "error": "--baseline-mean and --baseline-std are required for anomaly mode"}
    if baseline_std <= 0:
        return {"mode": "anomaly", "error": "--baseline-std must be greater than 0"}

    try:
        with open(events_file, "r", encoding="utf-8") as fh:
            events = json.load(fh)
    except FileNotFoundError:
        return {"mode": "anomaly", "error": f"Events file not found: {events_file}"}
    except json.JSONDecodeError as exc:
        return {"mode": "anomaly", "error": f"Invalid JSON in events file: {exc}"}

    if not isinstance(events, list):
        return {"mode": "anomaly", "error": "Events file must contain a JSON array of event objects"}

    anomaly_events = []
    soft_flag_count = 0
    hard_flag_count = 0
    time_anomaly_count = 0
    entity_counts = {}  # entity -> anomaly count

    for idx, event in enumerate(events):
        if not isinstance(event, dict):
            continue

        volume = event.get("volume")
        timestamp_str = event.get("timestamp", "")
        entity = event.get("entity", f"unknown_{idx}")
        action = event.get("action", "")

        # Z-score calculation
        z_score = None
        soft_flag = False
        hard_flag = False
        if volume is not None:
            try:
                volume = float(volume)
                z_score = (volume - baseline_mean) / baseline_std
                if z_score >= 3.0:
                    hard_flag = True
                    hard_flag_count += 1
                    entity_counts[entity] = entity_counts.get(entity, 0) + 1
                elif z_score >= 2.0:
                    soft_flag = True
                    soft_flag_count += 1
                    entity_counts[entity] = entity_counts.get(entity, 0) + 1
            except (TypeError, ValueError):
                pass

        # Time anomaly check
        time_anomaly = False
        event_hour = None
        if timestamp_str:
            for fmt in ("%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S%z"):
                try:
                    dt = datetime.strptime(timestamp_str, fmt)
                    event_hour = dt.hour
                    break
                except ValueError:
                    continue
            # Try with timezone offset via fromisoformat (Python 3.7+)
            if event_hour is None:
                try:
                    dt = datetime.fromisoformat(timestamp_str.replace("Z", "+00:00"))
                    event_hour = dt.hour
                except ValueError:
                    pass

        if event_hour is not None and event_hour in ANOMALY_TIME_HOURS_SUSPICIOUS:
            time_anomaly = True
            time_anomaly_count += 1

        if soft_flag or hard_flag or time_anomaly:
            anomaly_events.append({
                "event_index": idx,
                "entity": entity,
                "action": action,
                "timestamp": timestamp_str,
                "volume": volume,
                "z_score": round(z_score, 4) if z_score is not None else None,
                "soft_flag": soft_flag,
                "hard_flag": hard_flag,
                "time_anomaly": time_anomaly,
                "event_hour": event_hour,
            })

    total_events = len(events)
    risk_score = round(hard_flag_count / total_events, 4) if total_events > 0 else 0.0

    # Top anomalous entities
    top_entities = sorted(entity_counts.items(), key=lambda x: -x[1])[:5]

    # Recommended action
    if hard_flag_count > 0:
        recommended_action = (
            "{} hard anomalies detected (z >= 3.0). Initiate threat hunt and review affected entities: {}. "
            "Escalate to incident response if entity is high-value.".format(
                hard_flag_count,
                ", ".join(e for e, _ in top_entities[:3]) if top_entities else "unknown"
            )
        )
    elif soft_flag_count > 0:
        recommended_action = (
            "{} soft anomalies detected (z >= 2.0). Investigate {} for unusual activity patterns. "
            "Cross-correlate with other log sources.".format(
                soft_flag_count,
                ", ".join(e for e, _ in top_entities[:3]) if top_entities else "unknown"
            )
        )
    elif time_anomaly_count > 0:
        recommended_action = (
            "No volume anomalies, but {} events occurred during suspicious hours (22:00-06:00). "
            "Verify whether this activity is expected for the affected entities.".format(time_anomaly_count)
        )
    else:
        recommended_action = "No anomalies detected. Baseline appears stable for the provided event set."

    result = {
        "mode": "anomaly",
        "total_events": total_events,
        "baseline_mean": baseline_mean,
        "baseline_std": baseline_std,
        "anomaly_events": anomaly_events,
        "risk_score": risk_score,
        "soft_flag_count": soft_flag_count,
        "hard_flag_count": hard_flag_count,
        "time_anomaly_count": time_anomaly_count,
        "top_anomalous_entities": [{"entity": e, "anomaly_count": c} for e, c in top_entities],
        "recommended_action": recommended_action,
    }
    return result


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description=(
            "Threat Signal Analyzer — Hunt hypothesis scoring, IOC sweep planning, "
            "and behavioral anomaly detection."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  python3 threat_signal_analyzer.py --mode hunt --hypothesis 'APT using WMI for lateral movement' --json\n"
            "  python3 threat_signal_analyzer.py --mode ioc --ioc-file iocs.json --ioc-date 2026-01-15 --json\n"
            "  python3 threat_signal_analyzer.py --mode anomaly --events-file events.json "
            "--baseline-mean 45.0 --baseline-std 12.0 --json\n"
            "\nExit codes:\n"
            "  0  No high-priority findings\n"
            "  1  Medium-priority signals detected\n"
            "  2  High-priority findings confirmed"
        ),
    )
    parser.add_argument(
        "--mode",
        choices=["hunt", "ioc", "anomaly"],
        required=True,
        help="Analysis mode: hunt | ioc | anomaly",
    )
    # Hunt args
    parser.add_argument("--hypothesis", type=str, help="[hunt] Free-text threat hypothesis")
    parser.add_argument("--actor-relevance", type=int, choices=[0, 1, 2, 3], default=1,
                        dest="actor_relevance",
                        help="[hunt] Actor relevance score 0-3 (default: 1)")
    parser.add_argument("--control-gap", type=int, choices=[0, 1, 2, 3], default=1,
                        dest="control_gap",
                        help="[hunt] Security control gap score 0-3 (default: 1)")
    parser.add_argument("--data-availability", type=int, choices=[0, 1, 2, 3], default=2,
                        dest="data_availability",
                        help="[hunt] Data availability score 0-3 (default: 2)")
    # IOC args
    parser.add_argument("--ioc-file", type=str, dest="ioc_file",
                        help="[ioc] Path to JSON file with IOC lists (keys: ips, domains, hashes, urls, emails)")
    parser.add_argument("--ioc-date", type=str, dest="ioc_date",
                        help="[ioc] Date IOCs were collected (YYYY-MM-DD) for freshness check")
    # Anomaly args
    parser.add_argument("--events-file", type=str, dest="events_file",
                        help="[anomaly] Path to JSON array of events with {timestamp, entity, action, volume}")
    parser.add_argument("--baseline-mean", type=float, dest="baseline_mean",
                        help="[anomaly] Baseline mean for volume z-score calculation")
    parser.add_argument("--baseline-std", type=float, dest="baseline_std",
                        help="[anomaly] Baseline standard deviation for z-score calculation")
    # Output
    parser.add_argument("--json", action="store_true", dest="output_json",
                        help="Output results as JSON")

    args = parser.parse_args()

    if args.mode == "hunt":
        if not args.hypothesis:
            parser.error("--hypothesis is required for hunt mode")
        result = hunt_mode(args)
        priority_score = result.get("priority_score", 0)
        if args.output_json:
            print(json.dumps(result, indent=2))
        else:
            print("\n=== THREAT HUNT ANALYSIS ===")
            print(f"Hypothesis      : {result['hypothesis']}")
            print(f"Matched Keywords: {', '.join(result['matched_keywords']) or 'None'}")
            print(f"Matched T-Codes : {', '.join(result['matched_tcodes']) or 'None'}")
            print(f"Tactics         : {', '.join(result['tactics']) or 'None'}")
            print(f"Priority Score  : {priority_score} (threshold: {result['score_breakdown']['pursue_threshold']})")
            print(f"Pursue?         : {'YES' if result['pursue_recommendation'] else 'NO'}")
            print(f"Data Sources    : {', '.join(result['data_sources_required']) or 'None identified'}")
            print(f"Quality Check   : {'Required' if result['data_quality_check_required'] else 'Not required'}")
        # Exit codes: >= 8 = high, 5-7 = medium, < 5 = low
        if priority_score >= 8:
            sys.exit(2)
        elif priority_score >= 5:
            sys.exit(1)
        sys.exit(0)

    elif args.mode == "ioc":
        if not args.ioc_file:
            parser.error("--ioc-file is required for ioc mode")
        result = ioc_mode(args)
        if "error" in result:
            if args.output_json:
                print(json.dumps(result, indent=2))
            else:
                print(f"ERROR: {result['error']}", file=sys.stderr)
            sys.exit(1)
        if args.output_json:
            print(json.dumps(result, indent=2))
        else:
            print("\n=== IOC SWEEP PLAN ===")
            print(f"IOC Counts      : {result['ioc_counts']}")
            print(f"Coverage Score  : {result['coverage_score']:.2%}")
            print(f"Freshness Warn  : {'YES — IOCs may be stale' if result['freshness_warning'] else 'No'}")
            if result.get("ioc_age_days") is not None:
                print(f"IOC Age (days)  : {result['ioc_age_days']}")
            print(f"\nAction: {result['recommended_action']}")
            print("\nSweep Plan:")
            for ioc_type, plan in result["sweep_plan"].items():
                stale_tag = " [STALE]" if plan["stale"] else ""
                print(f"  {ioc_type:<12} {plan['count']} IOC(s){stale_tag} -> {', '.join(plan['targets'])}")
        # Exit codes based on staleness and coverage
        if result["freshness_warning"]:
            sys.exit(1)
        if result["coverage_score"] >= 0.5 and not result["freshness_warning"]:
            sys.exit(0)
        sys.exit(1)

    elif args.mode == "anomaly":
        if not args.events_file:
            parser.error("--events-file is required for anomaly mode")
        if args.baseline_mean is None or args.baseline_std is None:
            parser.error("--baseline-mean and --baseline-std are required for anomaly mode")
        result = anomaly_mode(args)
        if "error" in result:
            if args.output_json:
                print(json.dumps(result, indent=2))
            else:
                print(f"ERROR: {result['error']}", file=sys.stderr)
            sys.exit(1)
        if args.output_json:
            print(json.dumps(result, indent=2))
        else:
            print("\n=== ANOMALY DETECTION REPORT ===")
            print(f"Total Events    : {result['total_events']}")
            print(f"Baseline Mean   : {result['baseline_mean']}")
            print(f"Baseline Std    : {result['baseline_std']}")
            print(f"Hard Flags      : {result['hard_flag_count']} (z >= 3.0)")
            print(f"Soft Flags      : {result['soft_flag_count']} (z >= 2.0)")
            print(f"Time Anomalies  : {result['time_anomaly_count']}")
            print(f"Risk Score      : {result['risk_score']:.4f}")
            if result["top_anomalous_entities"]:
                print("\nTop Anomalous Entities:")
                for entry in result["top_anomalous_entities"]:
                    print(f"  {entry['entity']}: {entry['anomaly_count']} anomaly(s)")
            print(f"\nAction: {result['recommended_action']}")
            if result["anomaly_events"]:
                print("\nFlagged Events (first 10):")
                for ev in result["anomaly_events"][:10]:
                    flags = []
                    if ev["hard_flag"]:
                        flags.append("HARD")
                    if ev["soft_flag"]:
                        flags.append("SOFT")
                    if ev["time_anomaly"]:
                        flags.append("TIME")
                    print(
                        f"  [{', '.join(flags)}] entity={ev['entity']} "
                        f"volume={ev['volume']} z={ev['z_score']} ts={ev['timestamp']}"
                    )
        # Exit codes
        hard_flags = result.get("hard_flag_count", 0)
        soft_flags = result.get("soft_flag_count", 0)
        time_anomalies = result.get("time_anomaly_count", 0)
        if hard_flags > 0:
            sys.exit(2)
        elif soft_flags > 0 or time_anomalies > 0:
            sys.exit(1)
        sys.exit(0)


if __name__ == "__main__":
    main()
