# Attack Path Methodology

Reference documentation for attack path graph construction, choke point scoring, and effort-vs-impact analysis used in red team engagement planning.

---

## Attack Path Graph Model

An attack path is a directed graph where:
- **Nodes** are ATT&CK techniques or system states (initial access, crown jewel reached)
- **Edges** represent prerequisite relationships between techniques
- **Weight** on each edge is the effort score for the destination technique

The goal is to find all paths from the starting node (access level) to each crown jewel node, and to identify which nodes have the highest betweenness centrality (choke points).

### Node Types

| Node Type | Description | Example |
|-----------|-------------|---------|
| Starting state | Attacker's initial access level | external, internal, credentialed |
| Technique node | A MITRE ATT&CK technique | T1566.001, T1003.001, T1550.002 |
| Tactic state | Intermediate state achieved after completing a tactic | initial_access_achieved, persistence_established |
| Crown jewel node | Target asset — defines engagement success | Domain Controller, S3 Data Lake |

---

## Effort Score Formula

Each technique is scored by how hard it is to execute in the environment without triggering detection:

```
effort_score = detection_risk × (prerequisite_count + 1)
```

Where:
- `detection_risk` is 0.0–1.0 (0 = trivial to execute, 1 = will be detected with high probability)
- `prerequisite_count` is the number of earlier techniques that must succeed before this one can be executed

A path's total effort score is the sum of effort scores for all techniques in the path.

### Technique Effort Score Reference

| Technique | Detection Risk | Prerequisites | Effort Score | Tactic |
|-----------|---------------|---------------|-------------|--------|
| T1566.001 Spearphishing Link | 0.40 | 0 | 0.40 | initial_access |
| T1190 Exploit Public-Facing Application | 0.55 | 0 | 0.55 | initial_access |
| T1078 Valid Accounts | 0.35 | 0 | 0.35 | initial_access |
| T1059.001 PowerShell | 0.70 | 1 | 1.40 | execution |
| T1047 WMI Execution | 0.60 | 1 | 1.20 | execution |
| T1053.005 Scheduled Task | 0.50 | 1 | 1.00 | persistence |
| T1543.003 Windows Service | 0.55 | 1 | 1.10 | persistence |
| T1003.001 LSASS Dump | 0.80 | 1 | 1.60 | credential_access |
| T1558.003 Kerberoasting | 0.65 | 1 | 1.30 | credential_access |
| T1110 Brute Force | 0.75 | 0 | 0.75 | credential_access |
| T1021.006 WinRM | 0.65 | 2 | 1.95 | lateral_movement |
| T1550.002 Pass-the-Hash | 0.60 | 2 | 1.80 | lateral_movement |
| T1078.002 Domain Account | 0.40 | 2 | 1.20 | lateral_movement |
| T1074.001 Local Data Staging | 0.45 | 3 | 1.80 | collection |
| T1048.003 Exfil via HTTP | 0.55 | 3 | 2.20 | exfiltration |
| T1486 Ransomware | 0.90 | 3 | 3.60 | impact |

---

## Choke Point Identification

A choke point is a technique node that:
1. Lies on multiple paths to crown jewel assets, AND
2. Has no alternative technique that achieves the same prerequisite state

### Choke Point Score

```
choke_point_score = (paths_through_node / total_paths_to_all_crown_jewels) × detection_risk
```

Techniques with a high choke point score have high defensive leverage — a detection rule for that technique covers the most attack paths.

### Common Choke Points by Environment

**Active Directory Domain:**
- T1003 (Credential Access) — required for Pass-the-Hash and most lateral movement
- T1558 (Kerberos Tickets) — Kerberoasting provides service account credentials for privilege escalation

**AWS Cloud:**
- iam:PassRole — required for most cloud privilege escalation paths
- T1078.004 (Valid Cloud Accounts) — credential compromise required for all cloud attack paths

**Hybrid Environment:**
- T1078.002 (Domain Accounts) — once domain credentials are obtained, both on-prem and cloud paths open
- T1021.001 (Remote Desktop Protocol) — primary lateral movement mechanism in Windows environments

---

## Effort-vs-Impact Matrix

Plot each path on two dimensions to prioritize red team focus:

| Quadrant | Effort | Impact | Priority |
|----------|--------|--------|----------|
| High Priority | Low | High | Test first — easiest path to critical asset |
| Medium Priority | Low | Low | Test after high priority |
| Medium Priority | High | High | Test — complex but high-value if successful |
| Low Priority | High | Low | Test last — costly and low-value |

**Effort** is the path's total effort score (lower = easier).
**Impact** is the crown jewel value (defined in RoE — Domain Controller = highest, individual workstation = lowest).

---

## Access Level Constraints

Not all techniques are available from all starting positions. The engagement planner enforces access level hierarchy:

| Access Level | Available Techniques | Blocked Techniques |
|-------------|---------------------|-------------------|
| external | Techniques requiring only internet access: T1190, T1566, T1110, T1078 (via credential stuffing) | Any technique requiring internal_network or local_admin |
| internal | All external + internal recon, lateral movement prep | Techniques requiring local_admin or domain_admin |
| credentialed | All techniques — full kill-chain available | None (assumes valid credentials = highest starting position) |

### Scope Violation Detection

The engagement planner flags scope violations when a technique requires a prerequisite that is not reachable from the specified access level. Example: `T1550.002 Pass-the-Hash` requires `credential_access` as a prerequisite. If the plan specifies `access-level external`, the technique will generate a scope violation because credential access is not reachable from external without first completing initial access and execution phases.

---

## OPSEC Risk Registry

| Tactic | Risk Description | Detection Likelihood | Mitigation in Engagement |
|--------|-----------------|--------------------|-----------------------------|
| credential_access | LSASS memory access logged by EDR | High | Use DCSync or Kerberoasting instead of direct LSASS dump |
| execution | PowerShell ScriptBlock logging enabled in most orgs | High | Use alternate execution (compiled binaries, COM objects) |
| lateral_movement | NTLM Event 4624 type 3 correlates source/destination | Medium | Use Kerberos; avoid NTLM over the wire where possible |
| persistence | Scheduled task creation generates Event 4698 | Medium | Use less-monitored persistence (COM hijacking, DLL side-load) within scope |
| exfiltration | Large outbound transfers trigger DLP | Medium | Use slow exfil (<100KB/min); leverage allowed cloud storage |
| collection | Staging directory access triggers file integrity monitoring | Low-Medium | Stage in user-writable directories not covered by FIM |
