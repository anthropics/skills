#!/usr/bin/env python3
"""
incident_triage.py — Incident Classification, Triage, and Escalation

Classifies security events into 14 incident types, applies false-positive
filters, scores severity (SEV1-SEV4), determines escalation path, and
performs forensic pre-analysis for confirmed incidents.

Usage:
    echo '{"event_type": "ransomware", "raw_payload": {...}}' | python3 incident_triage.py
    python3 incident_triage.py --input event.json --json
    python3 incident_triage.py --classify --false-positive-check --input event.json --json

Exit codes:
    0  SEV3/SEV4 or clean — standard handling
    1  SEV2 — elevated response required
    2  SEV1 — critical incident declared
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Constants — Forensic Pre-Analysis Base (reused from pre_analysis.py logic)
# ---------------------------------------------------------------------------

DWELL_CRITICAL = 720    # hours (30 days)
DWELL_HIGH = 168        # hours (7 days)
DWELL_MEDIUM = 24       # hours (1 day)

EVIDENCE_SOURCES = [
    "siem_logs",
    "edr_telemetry",
    "network_pcap",
    "dns_logs",
    "proxy_logs",
    "cloud_trail",
    "authentication_logs",
    "endpoint_filesystem",
    "memory_dump",
    "email_headers",
]

CHAIN_OF_CUSTODY_STEPS = [
    "Identify and preserve volatile evidence (RAM, network connections)",
    "Hash all collected artifacts (SHA-256) before analysis",
    "Document collection timestamp and analyst identity",
    "Transfer artifacts to isolated forensic workstation",
    "Maintain write-blockers for disk images",
    "Log every access to evidence with timestamps",
    "Store originals in secure, access-controlled evidence vault",
    "Maintain dual-custody chain for legal proceedings",
]


# ---------------------------------------------------------------------------
# Constants — Incident Taxonomy and Escalation
# ---------------------------------------------------------------------------

INCIDENT_TAXONOMY: Dict[str, Dict[str, Any]] = {
    "ransomware": {
        "default_severity": "sev1",
        "mitre": "T1486",
        "response_sla_minutes": 15,
    },
    "data_exfiltration": {
        "default_severity": "sev1",
        "mitre": "T1048",
        "response_sla_minutes": 15,
    },
    "apt_intrusion": {
        "default_severity": "sev1",
        "mitre": "T1190",
        "response_sla_minutes": 15,
    },
    "supply_chain_compromise": {
        "default_severity": "sev1",
        "mitre": "T1195",
        "response_sla_minutes": 15,
    },
    "credential_compromise": {
        "default_severity": "sev2",
        "mitre": "T1078",
        "response_sla_minutes": 60,
    },
    "lateral_movement": {
        "default_severity": "sev2",
        "mitre": "T1021",
        "response_sla_minutes": 60,
    },
    "privilege_escalation": {
        "default_severity": "sev2",
        "mitre": "T1068",
        "response_sla_minutes": 60,
    },
    "malware_detected": {
        "default_severity": "sev2",
        "mitre": "T1204",
        "response_sla_minutes": 60,
    },
    "phishing": {
        "default_severity": "sev3",
        "mitre": "T1566",
        "response_sla_minutes": 240,
    },
    "unauthorized_access": {
        "default_severity": "sev3",
        "mitre": "T1078",
        "response_sla_minutes": 240,
    },
    "policy_violation": {
        "default_severity": "sev4",
        "mitre": "T1530",
        "response_sla_minutes": 1440,
    },
    "vulnerability_discovered": {
        "default_severity": "sev4",
        "mitre": "T1190",
        "response_sla_minutes": 1440,
    },
    "dos_attack": {
        "default_severity": "sev3",
        "mitre": "T1498",
        "response_sla_minutes": 240,
    },
    "insider_threat": {
        "default_severity": "sev2",
        "mitre": "T1078.002",
        "response_sla_minutes": 60,
    },
}

FALSE_POSITIVE_INDICATORS = [
    {
        "name": "ci_cd_automation",
        "description": "CI/CD pipeline service account activity",
        "patterns": [
            "jenkins", "github-actions", "gitlab-ci", "terraform",
            "ansible", "circleci", "codepipeline",
        ],
    },
    {
        "name": "test_environment",
        "description": "Activity in test/dev/staging environment",
        "patterns": [
            "test", "dev", "staging", "sandbox", "qa", "nonprod", "non-prod",
        ],
    },
    {
        "name": "scheduled_scanner",
        "description": "Known security scanner or automated tool",
        "patterns": [
            "nessus", "qualys", "rapid7", "tenable", "crowdstrike",
            "defender", "sentinel",
        ],
    },
    {
        "name": "scheduled_batch_job",
        "description": "Recurring batch process with expected behavior",
        "patterns": [
            "backup", "sync", "batch", "cron", "scheduled", "nightly", "weekly",
        ],
    },
    {
        "name": "whitelisted_identity",
        "description": "Identity in approved exception list",
        "patterns": [
            "svc-", "sa-", "system@", "automation@", "monitor@", "health-check",
        ],
    },
]

ESCALATION_ROUTING: Dict[str, Dict[str, Any]] = {
    "sev1": {
        "escalate_to": "CISO + CEO + Board Chair (if data at risk)",
        "bridge_call": True,
        "war_room": True,
    },
    "sev2": {
        "escalate_to": "SOC Lead + CISO",
        "bridge_call": True,
        "war_room": False,
    },
    "sev3": {
        "escalate_to": "SOC Lead + Security Manager",
        "bridge_call": False,
        "war_room": False,
    },
    "sev4": {
        "escalate_to": "L3 Analyst queue",
        "bridge_call": False,
        "war_room": False,
    },
}

SEV_ESCALATION_TRIGGERS = [
    {"indicator": "ransomware_note_found", "escalate_to": "sev1"},
    {"indicator": "active_exfiltration_confirmed", "escalate_to": "sev1"},
    {"indicator": "siem_disabled", "escalate_to": "sev1"},
    {"indicator": "domain_controller_access", "escalate_to": "sev1"},
    {"indicator": "second_system_compromised", "escalate_to": "sev1"},
]


# ---------------------------------------------------------------------------
# Forensic Pre-Analysis Functions (base pre_analysis.py logic)
# ---------------------------------------------------------------------------

def parse_forensic_fields(fact: dict) -> dict:
    """
    Parse and normalise forensic-relevant fields from the raw event.

    Returns a dict with keys: source_ip, destination_ip, user_account,
    hostname, process_name, dwell_hours, iocs, raw_payload.
    """
    raw = fact.get("raw_payload", {}) if isinstance(fact.get("raw_payload"), dict) else {}

    def _pick(*keys: str, default: Any = None) -> Any:
        """Return first non-None value found across fact and raw_payload."""
        for k in keys:
            v = fact.get(k) or raw.get(k)
            if v is not None:
                return v
        return default

    source_ip = _pick("source_ip", "src_ip", "sourceIp", default="unknown")
    destination_ip = _pick("destination_ip", "dst_ip", "dest_ip", "destinationIp", default="unknown")
    user_account = _pick("user", "user_account", "username", "actor", "identity", default="unknown")
    hostname = _pick("hostname", "host", "device", "computer_name", default="unknown")
    process_name = _pick("process", "process_name", "executable", "image", default="unknown")

    # Dwell time: accept hours directly or compute from timestamps
    dwell_hours: float = 0.0
    raw_dwell = _pick("dwell_hours", "dwell_time_hours", "dwell")
    if raw_dwell is not None:
        try:
            dwell_hours = float(raw_dwell)
        except (TypeError, ValueError):
            dwell_hours = 0.0
    else:
        first_seen = _pick("first_seen", "first_observed", "initial_access_time")
        last_seen = _pick("last_seen", "last_observed", "detection_time")
        if first_seen and last_seen:
            try:
                fmt = "%Y-%m-%dT%H:%M:%SZ"
                dt_first = datetime.strptime(str(first_seen), fmt)
                dt_last = datetime.strptime(str(last_seen), fmt)
                dwell_hours = max(0.0, (dt_last - dt_first).total_seconds() / 3600.0)
            except (ValueError, TypeError):
                dwell_hours = 0.0

    iocs: List[str] = []
    raw_iocs = _pick("iocs", "indicators", "indicators_of_compromise")
    if isinstance(raw_iocs, list):
        iocs = [str(i) for i in raw_iocs]
    elif isinstance(raw_iocs, str):
        iocs = [raw_iocs]

    return {
        "source_ip": source_ip,
        "destination_ip": destination_ip,
        "user_account": user_account,
        "hostname": hostname,
        "process_name": process_name,
        "dwell_hours": dwell_hours,
        "iocs": iocs,
        "raw_payload": raw,
    }


def assess_dwell_severity(dwell_hours: float) -> str:
    """
    Map dwell time (hours) to a severity label.

    Returns 'critical', 'high', 'medium', or 'low'.
    """
    if dwell_hours >= DWELL_CRITICAL:
        return "critical"
    if dwell_hours >= DWELL_HIGH:
        return "high"
    if dwell_hours >= DWELL_MEDIUM:
        return "medium"
    return "low"


def build_ioc_summary(fields: dict) -> dict:
    """
    Build a structured IOC summary from parsed forensic fields.

    Returns a dict suitable for embedding in the triage output.
    """
    iocs = fields.get("iocs", [])
    dwell_hours = fields.get("dwell_hours", 0.0)
    dwell_severity = assess_dwell_severity(dwell_hours)

    # Classify IOCs by rough heuristic
    ip_iocs = [i for i in iocs if _looks_like_ip(i)]
    hash_iocs = [i for i in iocs if _looks_like_hash(i)]
    domain_iocs = [i for i in iocs if not _looks_like_ip(i) and not _looks_like_hash(i)]

    return {
        "total_ioc_count": len(iocs),
        "ip_indicators": ip_iocs,
        "hash_indicators": hash_iocs,
        "domain_url_indicators": domain_iocs,
        "dwell_hours": round(dwell_hours, 2),
        "dwell_severity": dwell_severity,
        "evidence_sources_applicable": [
            src for src in EVIDENCE_SOURCES
            if _source_applicable(src, fields)
        ],
        "chain_of_custody_steps": CHAIN_OF_CUSTODY_STEPS,
    }


def _looks_like_ip(value: str) -> bool:
    """Heuristic: does the string look like an IPv4 address?"""
    import re
    return bool(re.match(r"^\d{1,3}(\.\d{1,3}){3}$", value.strip()))


def _looks_like_hash(value: str) -> bool:
    """Heuristic: does the string look like a hex hash (MD5/SHA1/SHA256)?"""
    import re
    return bool(re.match(r"^[0-9a-fA-F]{32,64}$", value.strip()))


def _source_applicable(source: str, fields: dict) -> bool:
    """Decide if an evidence source is relevant given parsed fields."""
    mapping = {
        "network_pcap": fields.get("source_ip") not in (None, "unknown"),
        "edr_telemetry": fields.get("hostname") not in (None, "unknown"),
        "authentication_logs": fields.get("user_account") not in (None, "unknown"),
        "dns_logs": fields.get("destination_ip") not in (None, "unknown"),
        "endpoint_filesystem": fields.get("process_name") not in (None, "unknown"),
        "memory_dump": fields.get("process_name") not in (None, "unknown"),
    }
    return mapping.get(source, True)


# ---------------------------------------------------------------------------
# New Classification and Escalation Functions
# ---------------------------------------------------------------------------

def classify_incident(fact: dict) -> Tuple[str, float]:
    """
    Classify incident type from event fields.

    Performs keyword matching against INCIDENT_TAXONOMY keys and the
    flattened string representation of raw_payload content.

    Returns:
        (incident_type, confidence) where confidence is 0.0–1.0.
        Returns ("unknown", 0.0) when no match is found.
    """
    # Build a single searchable string from the fact
    searchable = _flatten_to_string(fact).lower()

    scores: Dict[str, int] = {}

    for incident_type in INCIDENT_TAXONOMY:
        # The incident type slug itself is a keyword
        slug_words = incident_type.replace("_", " ").split()
        score = 0
        for word in slug_words:
            if word in searchable:
                score += 2  # direct slug match carries more weight

        # Additional keyword synonyms per type
        synonyms = _get_synonyms(incident_type)
        for syn in synonyms:
            if syn in searchable:
                score += 1

        if score > 0:
            scores[incident_type] = score

    if not scores:
        # Last resort: check explicit event_type field
        event_type = str(fact.get("event_type", "")).lower().replace(" ", "_").replace("-", "_")
        if event_type in INCIDENT_TAXONOMY:
            return event_type, 0.6
        return "unknown", 0.0

    best_type = max(scores, key=lambda k: scores[k])
    max_score = scores[best_type]

    # Normalise confidence: cap at 1.0, scale by how much the best
    # outscores alternatives
    total_score = sum(scores.values()) or 1
    raw_confidence = max_score / total_score
    # Boost if event_type field matches
    event_type = str(fact.get("event_type", "")).lower().replace(" ", "_").replace("-", "_")
    if event_type == best_type:
        raw_confidence = min(1.0, raw_confidence + 0.25)

    confidence = round(min(1.0, raw_confidence + 0.1 * min(max_score, 5)), 2)
    return best_type, confidence


def _flatten_to_string(obj: Any, depth: int = 0) -> str:
    """Recursively flatten any JSON-like object into a single string."""
    if depth > 6:
        return ""
    if isinstance(obj, dict):
        parts = []
        for k, v in obj.items():
            parts.append(str(k))
            parts.append(_flatten_to_string(v, depth + 1))
        return " ".join(parts)
    if isinstance(obj, list):
        return " ".join(_flatten_to_string(i, depth + 1) for i in obj)
    return str(obj)


def _get_synonyms(incident_type: str) -> List[str]:
    """Return additional keyword synonyms for an incident type."""
    synonyms_map: Dict[str, List[str]] = {
        "ransomware": ["encrypt", "ransom", "locked", "decrypt", "wiper", "crypto"],
        "data_exfiltration": ["exfil", "upload", "transfer", "leak", "dump", "steal", "exfiltrate"],
        "apt_intrusion": ["apt", "nation-state", "targeted", "backdoor", "persistence", "c2", "c&c"],
        "supply_chain_compromise": ["supply chain", "dependency", "package", "solarwinds", "xz", "npm"],
        "credential_compromise": ["credential", "password", "brute force", "spray", "stuffing", "stolen"],
        "lateral_movement": ["lateral", "pivot", "pass-the-hash", "wmi", "psexec", "rdp movement"],
        "priv_escalation": ["privesc", "su_exec", "priv_change", "elevated_session", "priv_grant", "priv_abuse"],
        "malware_detected": ["malware", "trojan", "virus", "worm", "keylogger", "spyware", "rat"],
        "phishing": ["phish", "spear", "bec", "email", "lure", "credential harvest"],
        "unauthorized_access": ["unauthorized", "unauthenticated", "brute", "login failed", "access denied"],
        "policy_violation": ["policy", "dlp", "data loss", "violation", "compliance"],
        "vulnerability_discovered": ["vulnerability", "cve", "exploit", "patch", "zero-day", "rce"],
        "dos_attack": ["dos", "ddos", "flood", "amplification", "bandwidth", "exhaustion"],
        "insider_threat": ["insider", "employee", "contractor", "abuse", "privilege misuse"],
    }
    return synonyms_map.get(incident_type, [])


def check_false_positives(fact: dict) -> List[str]:
    """
    Check fact fields against FALSE_POSITIVE_INDICATORS pattern lists.

    Returns a list of triggered false positive indicator names.
    """
    searchable = _flatten_to_string(fact).lower()
    triggered: List[str] = []

    for indicator in FALSE_POSITIVE_INDICATORS:
        for pattern in indicator["patterns"]:
            if pattern.lower() in searchable:
                triggered.append(indicator["name"])
                break  # one match per indicator is enough

    return triggered


def get_escalation_path(incident_type: str, severity: str) -> dict:
    """
    Return escalation routing for a given incident type and severity level.

    Falls back to sev4 routing if severity is not recognised.
    """
    sev_key = severity.lower()
    routing = ESCALATION_ROUTING.get(sev_key, ESCALATION_ROUTING["sev4"]).copy()

    # Augment with taxonomy SLA if available
    taxonomy = INCIDENT_TAXONOMY.get(incident_type, {})
    routing["incident_type"] = incident_type
    routing["severity"] = sev_key
    routing["response_sla_minutes"] = taxonomy.get("response_sla_minutes", 1440)
    routing["mitre_technique"] = taxonomy.get("mitre", "N/A")

    return routing


def check_sev_escalation_triggers(fact: dict) -> Optional[str]:
    """
    Scan fact fields for any SEV escalation trigger indicators.

    Returns the escalation target (e.g. 'sev1') if a trigger fires,
    or None if no triggers are present.
    """
    searchable = _flatten_to_string(fact).lower()
    # Also inspect a flat list of explicit indicator flags
    explicit_indicators: List[str] = []
    if isinstance(fact.get("indicators"), list):
        explicit_indicators = [str(i).lower() for i in fact["indicators"]]
    if isinstance(fact.get("escalation_triggers"), list):
        explicit_indicators += [str(i).lower() for i in fact["escalation_triggers"]]

    for trigger in SEV_ESCALATION_TRIGGERS:
        indicator_key = trigger["indicator"].replace("_", " ")
        indicator_raw = trigger["indicator"].lower()

        if (
            indicator_key in searchable
            or indicator_raw in searchable
            or indicator_raw in explicit_indicators
        ):
            return trigger["escalate_to"]

    return None


# ---------------------------------------------------------------------------
# Severity Normalisation Helpers
# ---------------------------------------------------------------------------

_SEV_ORDER = {"sev1": 1, "sev2": 2, "sev3": 3, "sev4": 4}


def _sev_to_int(sev: str) -> int:
    return _SEV_ORDER.get(sev.lower(), 4)


def _int_to_sev(n: int) -> str:
    return {1: "sev1", 2: "sev2", 3: "sev3", 4: "sev4"}.get(n, "sev4")


def _escalate_sev(current: str, target: str) -> str:
    """Return the higher severity (lower SEV number)."""
    return _int_to_sev(min(_sev_to_int(current), _sev_to_int(target)))


# ---------------------------------------------------------------------------
# Text Report
# ---------------------------------------------------------------------------

def _print_text_report(result: dict) -> None:
    """Print a human-readable triage report to stdout."""
    sep = "=" * 70
    print(sep)
    print("  INCIDENT TRIAGE REPORT")
    print(sep)
    print(f"  Timestamp     : {result.get('timestamp_utc', 'N/A')}")
    print(f"  Incident Type : {result.get('incident_type', 'unknown').upper()}")
    print(f"  Severity      : {result.get('severity', 'N/A').upper()}")
    print(f"  Confidence    : {result.get('classification_confidence', 0.0):.0%}")
    print(sep)

    fp = result.get("false_positive_indicators", [])
    if fp:
        print(f"\n  [!] FALSE POSITIVE FLAGS: {', '.join(fp)}")
        print("      Review before escalating.")

    esc_trigger = result.get("escalation_trigger_fired")
    if esc_trigger:
        print(f"\n  [!] ESCALATION TRIGGER FIRED -> {esc_trigger.upper()}")

    path = result.get("escalation_path", {})
    print(f"\n  Escalate To   : {path.get('escalate_to', 'N/A')}")
    print(f"  Response SLA  : {path.get('response_sla_minutes', 'N/A')} minutes")
    print(f"  Bridge Call   : {'YES' if path.get('bridge_call') else 'no'}")
    print(f"  War Room      : {'YES' if path.get('war_room') else 'no'}")
    print(f"  MITRE         : {path.get('mitre_technique', 'N/A')}")

    forensics = result.get("forensic_analysis", {})
    if forensics:
        print(f"\n  Forensic Fields:")
        print(f"    Source IP     : {forensics.get('source_ip', 'N/A')}")
        print(f"    User Account  : {forensics.get('user_account', 'N/A')}")
        print(f"    Hostname      : {forensics.get('hostname', 'N/A')}")
        print(f"    Process       : {forensics.get('process_name', 'N/A')}")
        print(f"    Dwell (hrs)   : {forensics.get('dwell_hours', 0.0)}")
        print(f"    Dwell Severity: {forensics.get('dwell_severity', 'N/A')}")

    ioc_summary = result.get("ioc_summary", {})
    if ioc_summary:
        print(f"\n  IOC Summary:")
        print(f"    Total IOCs    : {ioc_summary.get('total_ioc_count', 0)}")
        if ioc_summary.get("ip_indicators"):
            print(f"    IPs           : {', '.join(ioc_summary['ip_indicators'])}")
        if ioc_summary.get("hash_indicators"):
            print(f"    Hashes        : {len(ioc_summary['hash_indicators'])} hash(es)")
        print(f"    Evidence Srcs : {', '.join(ioc_summary.get('evidence_sources_applicable', []))}")

    print(f"\n  Recommended Action: {result.get('recommended_action', 'N/A')}")
    print(sep)


# ---------------------------------------------------------------------------
# Main Entry Point
# ---------------------------------------------------------------------------

# Embedded synthetic security event for --sample (no file/stdin needed).
SAMPLE_EVENT = {
    "event_type": "ransomware",
    "source_ip": "203.0.113.50",
    "destination_ip": "10.0.4.21",
    "user_account": "svc-backup",
    "hostname": "fileserver-02",
    "process_name": "encryptor.exe",
    "first_seen": "2026-06-10T01:30:00Z",
    "detected_at": "2026-06-10T09:30:00Z",
}


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Incident Classification, Triage, and Escalation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  echo '{"event_type": "ransomware"}' | %(prog)s --json
  %(prog)s --input event.json --classify --false-positive-check --json
  %(prog)s --input event.json --severity sev1 --json

Exit codes:
  0  SEV3/SEV4 or no confirmed incident
  1  SEV2 — elevated response required
  2  SEV1 — critical incident declared
        """,
    )

    parser.add_argument(
        "--input", "-i",
        metavar="FILE",
        help="JSON file path containing the security event (default: stdin)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON",
    )
    parser.add_argument(
        "--classify",
        action="store_true",
        help="Run incident classification against INCIDENT_TAXONOMY",
    )
    parser.add_argument(
        "--false-positive-check",
        action="store_true",
        dest="false_positive_check",
        help="Run false positive filter checks",
    )
    parser.add_argument(
        "--severity",
        choices=["sev1", "sev2", "sev3", "sev4"],
        help="Explicit severity override (skips taxonomy-derived severity)",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Triage an embedded synthetic ransomware event (no file/stdin needed; "
             "note: exits 2 — the SEV1 exit-code signal is intentional)",
    )

    args = parser.parse_args()

    # --- Load input ---
    try:
        if args.sample:
            if args.input:
                print("Warning: --sample specified; ignoring --input", file=sys.stderr)
            raw_event = SAMPLE_EVENT
        elif args.input:
            with open(args.input, "r", encoding="utf-8") as fh:
                raw_event = json.load(fh)
        else:
            raw_event = json.load(sys.stdin)
    except json.JSONDecodeError as exc:
        msg = {"error": f"Invalid JSON input: {exc}"}
        if args.json:
            print(json.dumps(msg, indent=2))
        else:
            print(f"Error: {msg['error']}", file=sys.stderr)
        sys.exit(1)
    except FileNotFoundError as exc:
        msg = {"error": str(exc)}
        if args.json:
            print(json.dumps(msg, indent=2))
        else:
            print(f"Error: {msg['error']}", file=sys.stderr)
        sys.exit(1)

    # --- Forensic pre-analysis (base logic) ---
    fields = parse_forensic_fields(raw_event)
    ioc_summary = build_ioc_summary(fields)

    forensic_analysis = {
        "source_ip": fields["source_ip"],
        "destination_ip": fields["destination_ip"],
        "user_account": fields["user_account"],
        "hostname": fields["hostname"],
        "process_name": fields["process_name"],
        "dwell_hours": fields["dwell_hours"],
        "dwell_severity": assess_dwell_severity(fields["dwell_hours"]),
    }

    # --- Classification ---
    incident_type = "unknown"
    confidence = 0.0

    if args.classify or not args.severity:
        incident_type, confidence = classify_incident(raw_event)

    # Override with explicit event_type if classify not run
    if not args.classify:
        et = str(raw_event.get("event_type", "")).lower().replace(" ", "_").replace("-", "_")
        if et in INCIDENT_TAXONOMY:
            incident_type = et
            confidence = 0.75

    # --- Determine base severity ---
    if args.severity:
        severity = args.severity.lower()
    else:
        taxonomy_entry = INCIDENT_TAXONOMY.get(incident_type, {})
        severity = taxonomy_entry.get("default_severity", "sev4")

        # Factor in dwell severity
        dwell_sev_map = {"critical": "sev1", "high": "sev2", "medium": "sev3", "low": "sev4"}
        dwell_derived = dwell_sev_map.get(forensic_analysis["dwell_severity"], "sev4")
        severity = _escalate_sev(severity, dwell_derived)

    # --- Escalation trigger check ---
    escalation_trigger_fired: Optional[str] = None
    trigger_result = check_sev_escalation_triggers(raw_event)
    if trigger_result:
        escalation_trigger_fired = trigger_result
        severity = _escalate_sev(severity, trigger_result)

    # --- False positive check ---
    fp_indicators: List[str] = []
    if args.false_positive_check:
        fp_indicators = check_false_positives(raw_event)

    # --- Escalation path ---
    escalation_path = get_escalation_path(incident_type, severity)

    # --- Recommended action ---
    if fp_indicators:
        recommended_action = (
            f"Verify false positive flags before escalating: {', '.join(fp_indicators)}. "
            "Confirm with asset owner and close or reclassify."
        )
    elif severity == "sev1":
        recommended_action = (
            "IMMEDIATE: Declare SEV1, open war room, page CISO and CEO. "
            "Isolate affected systems, preserve evidence, activate IR playbook."
        )
    elif severity == "sev2":
        recommended_action = (
            "URGENT: Page SOC Lead and CISO. Open bridge call. "
            "Contain impacted accounts/hosts and begin forensic collection."
        )
    elif severity == "sev3":
        recommended_action = (
            "Notify SOC Lead and Security Manager. "
            "Investigate during business hours and document findings."
        )
    else:
        recommended_action = (
            "Queue for L3 Analyst review. "
            "Document and track per standard operating procedure."
        )

    # --- Assemble output ---
    result: Dict[str, Any] = {
        "incident_type": incident_type,
        "classification_confidence": confidence,
        "severity": severity,
        "false_positive_indicators": fp_indicators,
        "escalation_trigger_fired": escalation_trigger_fired,
        "escalation_path": escalation_path,
        "forensic_analysis": forensic_analysis,
        "ioc_summary": ioc_summary,
        "recommended_action": recommended_action,
        "taxonomy": INCIDENT_TAXONOMY.get(incident_type, {}),
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }

    # --- Output ---
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        _print_text_report(result)

    # --- Exit code ---
    if severity == "sev1":
        sys.exit(2)
    elif severity == "sev2":
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
