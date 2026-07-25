---
name: "threat-detection"
description: "Use when hunting for threats in an environment, analyzing IOCs, or detecting behavioral anomalies in telemetry. Covers hypothesis-driven threat hunting, IOC sweep generation, z-score anomaly detection, and MITRE ATT&CK-mapped signal prioritization."
---

# Threat Detection

Threat detection skill for proactive discovery of attacker activity through hypothesis-driven hunting, IOC analysis, and behavioral anomaly detection. This is NOT incident response (see incident-response) or red team operations (see red-team) — this is about finding threats that have evaded automated controls.

---

## Table of Contents

- [Overview](#overview)
- [Threat Signal Analyzer](#threat-signal-analyzer)
- [Threat Hunting Methodology](#threat-hunting-methodology)
- [IOC Analysis](#ioc-analysis)
- [Anomaly Detection](#anomaly-detection)
- [MITRE ATT&CK Signal Prioritization](#mitre-attck-signal-prioritization)
- [Deception and Honeypot Integration](#deception-and-honeypot-integration)
- [Workflows](#workflows)
- [Anti-Patterns](#anti-patterns)
- [Cross-References](#cross-references)

---

## Overview

### What This Skill Does

This skill provides the methodology and tooling for **proactive threat detection** — finding attacker activity through structured hunting hypotheses, IOC analysis, and statistical anomaly detection before alerts fire.

### Distinction from Other Security Skills

| Skill | Focus | Approach |
|-------|-------|----------|
| **threat-detection** (this) | Finding hidden threats | Proactive — hunt before alerts |
| incident-response | Active incidents | Reactive — contain and investigate declared incidents |
| red-team | Offensive simulation | Offensive — test defenses from attacker perspective |
| cloud-security | Cloud misconfigurations | Posture — IAM, S3, network exposure |

### Prerequisites

Read access to SIEM/EDR telemetry, endpoint logs, and network flow data. IOC feeds require freshness within 30 days to avoid false positives. Hunting hypotheses must be scoped to the environment before execution.

---

## Threat Signal Analyzer

The `threat_signal_analyzer.py` tool supports three modes: `hunt` (hypothesis scoring), `ioc` (sweep generation), and `anomaly` (statistical detection).

```bash
# Hunt mode: score a hypothesis against MITRE ATT&CK coverage
python3 scripts/threat_signal_analyzer.py --mode hunt \
  --hypothesis "Lateral movement via PtH using compromised service account" \
  --actor-relevance 3 --control-gap 2 --data-availability 2 --json

# IOC mode: generate sweep targets from an IOC feed file
python3 scripts/threat_signal_analyzer.py --mode ioc \
  --ioc-file iocs.json --json

# Anomaly mode: detect statistical outliers in telemetry events
python3 scripts/threat_signal_analyzer.py --mode anomaly \
  --events-file telemetry.json \
  --baseline-mean 100 --baseline-std 25 --json

# List all supported MITRE ATT&CK techniques
python3 scripts/threat_signal_analyzer.py --list-techniques
```

### IOC file format

```json
{
  "ips": ["1.2.3.4", "5.6.7.8"],
  "domains": ["malicious.example.com"],
  "hashes": ["abc123def456..."]
}
```

### Telemetry events file format

```json
[
  {"timestamp": "2024-01-15T14:32:00Z", "entity": "host-01", "action": "dns_query", "volume": 450},
  {"timestamp": "2024-01-15T14:33:00Z", "entity": "host-02", "action": "dns_query", "volume": 95}
]
```

### Exit codes

| Code | Meaning |
|------|---------|
| 0 | No high-priority findings |
| 1 | Medium-priority signals detected |
| 2 | High-priority confirmed findings |

---

## Threat Hunting Methodology

Structured threat hunting follows a five-step loop: hypothesis → data source identification → query execution → finding triage → feedback to detection engineering.

### Hypothesis Scoring

| Factor | Weight | Description |
|--------|--------|-------------|
| Actor relevance | ×3 | How closely does this TTP match known threat actors in your sector? |
| Control gap | ×2 | How many of your existing controls would miss this behavior? |
| Data availability | ×1 | Do you have the telemetry data needed to test this hypothesis? |

Priority score = (actor_relevance × 3) + (control_gap × 2) + (data_availability × 1)

### High-Value Hunt Hypotheses by Tactic

| Hypothesis | MITRE ID | Data Sources | Priority Signal |
|-----------|----------|--------------|-----------------|
| WMI lateral movement via remote execution | T1047 | WMI logs, EDR process telemetry | WMI process spawned from WINRM, unusual parent-child chain |
| LOLBin execution for defense evasion | T1218 | Process creation, command-line args | certutil.exe, regsvr32.exe, mshta.exe with network activity |
| Beaconing C2 via jitter-heavy intervals | T1071.001 | Proxy logs, DNS logs | Regular interval outbound connections ±10% jitter |
| Pass-the-Hash lateral movement | T1550.002 | Windows security event 4624 type 3 | NTLM auth from unexpected source host to admin share |
| LSASS memory access | T1003.001 | EDR memory access events | OpenProcess on lsass.exe from non-system process |
| Kerberoasting | T1558.003 | Windows event 4769 | High volume TGS requests for service accounts |
| Scheduled task persistence | T1053.005 | Sysmon Event 1/11, Windows 4698 | Scheduled task created in non-standard directory |

---

## IOC Analysis

IOC analysis determines whether indicators are fresh, maps them to required sweep targets, and filters stale data that generates false positives.

### IOC Types and Sweep Priority

| IOC Type | Staleness Threshold | Sweep Target | MITRE Coverage |
|---------|--------------------|--------------|----|
| IP addresses | 30 days | Firewall logs, NetFlow, proxy logs | T1071, T1105 |
| Domains | 30 days | DNS resolver logs, proxy logs | T1568, T1583 |
| File hashes | 90 days | EDR file creation, AV scan logs | T1105, T1027 |
| URLs | 14 days | Proxy access logs, browser history | T1566.002 |
| Mutex names | 180 days | EDR runtime artifacts | T1055 |

### IOC Staleness Handling

IOCs older than their threshold are flagged as `stale` and excluded from sweep target generation. Running sweeps against stale IOCs inflates false positive rates and reduces SOC credibility. Refresh IOC feeds from threat intelligence platforms (MISP, OpenCTI, commercial TI) before every hunt cycle.

---

## Anomaly Detection

Statistical anomaly detection identifies behavior that deviates from established baselines without relying on known-bad signatures.

### Z-Score Thresholds

| Z-Score | Classification | Response |
|---------|---------------|----------|
| < 2.0 | Normal | No action required |
| 2.0–2.9 | Soft anomaly | Log and monitor — increase sampling |
| ≥ 3.0 | Hard anomaly | Escalate to hunt analyst — investigate entity |

### Baseline Requirements

Effective anomaly detection requires at least 14 days of historical telemetry to establish a valid baseline. Baselines must be recomputed after:
- Security incidents (post-incident behavior change)
- Major infrastructure changes (cloud migrations, new SaaS deployments)
- Seasonal usage pattern changes (end of quarter, holiday periods)

### High-Value Anomaly Targets

| Entity Type | Metric | Anomaly Indicator |
|-------------|--------|--------------------|
| DNS resolver | Queries per hour per host | Beaconing, tunneling, DGA |
| Endpoint | Unique process executions per day | Malware installation, LOLBin abuse |
| Service account | Auth events per hour | Credential stuffing, lateral movement |
| Email gateway | Attachment types per hour | Phishing campaign spike |
| Cloud IAM | API calls per identity per hour | Credential compromise, exfiltration |

---

## MITRE ATT&CK Signal Prioritization

Each hunting hypothesis maps to one or more ATT&CK techniques. Techniques with multiple confirmed signals in your environment are higher priority.

### Tactic Coverage Matrix

| Tactic | Key Techniques | Primary Data Source |
|--------|---------------|--------------------|-|
| Initial Access | T1190, T1566, T1078 | Web access logs, email gateway, auth logs |
| Execution | T1059, T1047, T1218 | Process creation, command-line, script execution |
| Persistence | T1053, T1543, T1098 | Scheduled tasks, services, account changes |
| Defense Evasion | T1027, T1562, T1070 | Process hollowing, log clearing, encoding |
| Credential Access | T1003, T1558, T1110 | LSASS, Kerberos, auth failures |
| Lateral Movement | T1550, T1021, T1534 | NTLM auth, remote services, internal spearphish |
| Collection | T1074, T1560, T1114 | Staging directories, archive creation, email access |
| Exfiltration | T1048, T1041, T1567 | Unusual outbound volume, DNS tunneling, cloud storage |
| Command & Control | T1071, T1572, T1568 | Beaconing, protocol tunneling, DNS C2 |

---

## Deception and Honeypot Integration

Deception assets generate high-fidelity alerts — any interaction with a honeypot is an unambiguous signal requiring investigation.

### Deception Asset Types and Placement

| Asset Type | Placement | Signal | ATT&CK Technique |
|-----------|-----------|--------|-----------------|
| Honeypot credentials in password vault | Vault secrets store | Credential access attempt | T1555 |
| Honey tokens (fake AWS access keys) | Git repos, S3 objects | Reconnaissance or exfiltration | T1552.004 |
| Honey files (named: passwords.xlsx) | File shares, endpoints | Collection staging | T1074 |
| Honey accounts (dormant AD users) | Active Directory | Lateral movement pivot | T1078.002 |
| Honeypot network services | DMZ, flat network segments | Network scanning, service exploitation | T1046, T1190 |

Honeypot alerts bypass the standard scoring pipeline — any hit is an automatic SEV2 until proven otherwise.

---

## Workflows

### Workflow 1: Quick Hunt (30 Minutes)

For responding to a new threat intelligence report or CVE alert:

```bash
# 1. Score hypothesis against environment context
python3 scripts/threat_signal_analyzer.py --mode hunt \
  --hypothesis "Exploitation of CVE-YYYY-NNNNN in Apache" \
  --actor-relevance 2 --control-gap 3 --data-availability 2 --json

# 2. Build IOC sweep list from threat intel
echo '{"ips": ["1.2.3.4"], "domains": ["malicious.tld"], "hashes": []}' > iocs.json
python3 scripts/threat_signal_analyzer.py --mode ioc --ioc-file iocs.json --json

# 3. Check for anomalies in web server telemetry from last 24h
python3 scripts/threat_signal_analyzer.py --mode anomaly \
  --events-file web_events_24h.json --baseline-mean 80 --baseline-std 20 --json
```

**Decision**: If hunt priority ≥ 7 or any IOC sweep hits, escalate to full hunt.

### Workflow 2: Full Threat Hunt (Multi-Day)

**Day 1 — Hypothesis Generation:**
1. Review threat intelligence feeds for sector-relevant TTPs
2. Map last 30 days of security alerts to ATT&CK tactics to identify gaps
3. Score top 5 hypotheses with threat_signal_analyzer.py hunt mode
4. Prioritize by score — start with highest

**Day 2 — Data Collection and Query Execution:**
1. Pull relevant telemetry from SIEM (date range: last 14 days)
2. Run anomaly detection across entity baselines
3. Execute IOC sweeps for all feeds fresh within 30 days
4. Review hunt playbooks in `references/hunt-playbooks.md`

**Day 3 — Triage and Reporting:**
1. Triage all anomaly findings — confirm or dismiss
2. Escalate confirmed activity to incident-response
3. Document new detection rules from hunt findings
4. Submit false-positive IOCs back to TI provider

### Workflow 3: Continuous Monitoring (Automated)

Configure recurring anomaly detection against key entity baselines on a 6-hour cadence:

```bash
# Run as cron job every 6 hours — auto-escalate on exit code 2
python3 scripts/threat_signal_analyzer.py --mode anomaly \
  --events-file /var/log/telemetry/events_6h.json \
  --baseline-mean "${BASELINE_MEAN}" \
  --baseline-std "${BASELINE_STD}" \
  --json > /var/log/threat-detection/$(date +%Y%m%d_%H%M%S).json

# Alert on exit code 2 (hard anomaly)
if [ $? -eq 2 ]; then
  send_alert "Hard anomaly detected — threat_signal_analyzer"
fi
```

---

## Anti-Patterns

1. **Hunting without a hypothesis** — Running broad queries across all telemetry without a focused question generates noise, not signal. Every hunt must start with a testable hypothesis scoped to one or two ATT&CK techniques.
2. **Using stale IOCs** — IOCs older than 30 days generate false positives that train analysts to ignore alerts. Always check IOC freshness before sweeping; exclude stale indicators from automated sweeps.
3. **Skipping baseline establishment** — Anomaly detection without a valid baseline produces alerts on normal high-volume days. Require 14+ days of baseline data before enabling statistical alerting on any entity type.
4. **Hunting only known techniques** — Hunting exclusively against documented ATT&CK techniques misses novel adversary behavior. Regularly include open-ended anomaly analysis that can surface unknown TTPs.
5. **Not closing the feedback loop to detection engineering** — Hunt findings that confirm malicious behavior must produce new detection rules. Hunting that doesn't improve detection coverage has no lasting value.
6. **Treating every anomaly as a confirmed threat** — High z-scores indicate deviation from baseline, not confirmed malice. All anomalies require human triage to confirm or dismiss before escalation.
7. **Ignoring honeypot alerts** — Any interaction with a deception asset is a high-fidelity signal. Treating honeypot alerts as noise invalidates the entire deception investment.

---

## Cross-References

| Skill | Relationship |
|-------|-------------|
| [incident-response](../incident-response/SKILL.md) | Confirmed threats from hunting escalate to incident-response for triage and containment |
| [red-team](../red-team/SKILL.md) | Red team exercises generate realistic TTPs that inform hunt hypothesis prioritization |
| [cloud-security](../cloud-security/SKILL.md) | Cloud posture findings (open S3, IAM wildcards) create hunting targets for data exfiltration TTPs |
| [security-pen-testing](../security-pen-testing/SKILL.md) | Pen test findings identify attack surfaces that threat hunting should monitor post-remediation |
