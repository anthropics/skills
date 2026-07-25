---
name: "red-team"
description: "Use when planning or executing authorized red team engagements, attack path analysis, or offensive security simulations. Covers MITRE ATT&CK kill-chain planning, technique scoring, choke point identification, OPSEC risk assessment, and crown jewel targeting."
---

# Red Team

Red team engagement planning and attack path analysis skill for authorized offensive security simulations. This is NOT vulnerability scanning (see security-pen-testing) or incident response (see incident-response) — this is about structured adversary simulation to test detection, response, and control effectiveness.

---

## Table of Contents

- [Overview](#overview)
- [Engagement Planner Tool](#engagement-planner-tool)
- [Kill-Chain Phase Methodology](#kill-chain-phase-methodology)
- [Technique Scoring and Prioritization](#technique-scoring-and-prioritization)
- [Choke Point Analysis](#choke-point-analysis)
- [OPSEC Risk Assessment](#opsec-risk-assessment)
- [Crown Jewel Targeting](#crown-jewel-targeting)
- [Attack Path Methodology](#attack-path-methodology)
- [Workflows](#workflows)
- [Anti-Patterns](#anti-patterns)
- [Cross-References](#cross-references)

---

## Overview

### What This Skill Does

This skill provides the methodology and tooling for **red team engagement planning** — building structured attack plans from MITRE ATT&CK technique selection, access level, and crown jewel targets. It scores techniques by effort and detection risk, assembles kill-chain phases, identifies choke points, and flags OPSEC risks.

### Distinction from Other Security Skills

| Skill | Focus | Approach |
|-------|-------|----------|
| **red-team** (this) | Adversary simulation | Offensive — structured attack planning and execution |
| security-pen-testing | Vulnerability discovery | Offensive — systematic exploitation of specific weaknesses |
| threat-detection | Finding attacker activity | Proactive — detect TTPs in telemetry |
| incident-response | Active incident management | Reactive — contain and investigate confirmed incidents |

### Authorization Requirement

**All red team activities described here require written authorization.** This includes a signed Rules of Engagement (RoE) document, defined scope, and explicit executive approval. The `engagement_planner.py` tool will not generate output without the `--authorized` flag. Unauthorized use of these techniques is illegal under the CFAA, Computer Misuse Act, and equivalent laws worldwide.

---

## Engagement Planner Tool

The `engagement_planner.py` tool builds a scored, kill-chain-ordered attack plan from technique selection, access level, and crown jewel targets.

```bash
# Basic engagement plan — external access, specific techniques
python3 scripts/engagement_planner.py \
  --techniques T1059,T1078,T1003 \
  --access-level external \
  --authorized --json

# Internal network access with crown jewel targeting
python3 scripts/engagement_planner.py \
  --techniques T1059,T1078,T1021,T1550,T1003 \
  --access-level internal \
  --crown-jewels "Database,Active Directory,Payment Systems" \
  --authorized --json

# Credentialed (assumed breach) scenario with scale
python3 scripts/engagement_planner.py \
  --techniques T1059,T1078,T1021,T1550,T1003,T1486,T1048 \
  --access-level credentialed \
  --crown-jewels "Domain Controller,S3 Data Lake" \
  --target-count 50 \
  --authorized --json

# List all 29 supported MITRE ATT&CK techniques
python3 scripts/engagement_planner.py --list-techniques
```

### Access Level Definitions

| Level | Starting Position | Techniques Available |
|-------|------------------|----------------------|
| external | No internal access — internet only | External-facing techniques only (T1190, T1566, etc.) |
| internal | Network foothold — no credentials | Internal recon + lateral movement prep |
| credentialed | Valid credentials obtained | Full kill chain including priv-esc, lateral movement, impact |

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Engagement plan generated successfully |
| 1 | Missing authorization or invalid technique |
| 2 | Scope violation — technique outside access-level constraints |

---

## Kill-Chain Phase Methodology

The engagement planner organizes techniques into eight kill-chain phases and orders the execution plan accordingly.

### Kill-Chain Phase Order

| Phase | Order | MITRE Tactic | Examples |
|-------|-------|--------------|----------|
| Reconnaissance | 1 | TA0043 | T1595, T1596, T1598 |
| Resource Development | 2 | TA0042 | T1583, T1588 |
| Initial Access | 3 | TA0001 | T1190, T1566, T1078 |
| Execution | 4 | TA0002 | T1059, T1047, T1204 |
| Persistence | 5 | TA0003 | T1053, T1543, T1136 |
| Privilege Escalation | 6 | TA0004 | T1055, T1548, T1134 |
| Credential Access | 7 | TA0006 | T1003, T1110, T1558 |
| Lateral Movement | 8 | TA0008 | T1021, T1550, T1534 |
| Collection | 9 | TA0009 | T1074, T1560, T1114 |
| Exfiltration | 10 | TA0010 | T1048, T1041, T1567 |
| Impact | 11 | TA0040 | T1486, T1491, T1498 |

### Phase Execution Principles

Each phase must be completed before advancing to the next unless the engagement scope specifies assumed breach (skip to a later phase). Do not skip persistence before attempting lateral movement — persistence ensures operational continuity if a single foothold is detected and removed.

---

## Technique Scoring and Prioritization

Techniques are scored by effort (how hard to execute without detection) and prioritized in the engagement plan.

### Effort Score Formula

```
effort_score = detection_risk × (len(prerequisites) + 1)
```

Lower effort score = easier to execute without triggering detection.

### Technique Scoring Reference

| Technique | Detection Risk | Prerequisites | Effort Score | MITRE ID |
|-----------|---------------|---------------|-------------|---------|
| PowerShell execution | 0.7 | initial_access | 1.4 | T1059.001 |
| Scheduled task persistence | 0.5 | execution | 1.0 | T1053.005 |
| Pass-the-Hash | 0.6 | credential_access, internal_network | 1.8 | T1550.002 |
| LSASS credential dump | 0.8 | local_admin | 1.6 | T1003.001 |
| Spearphishing link | 0.4 | none | 0.4 | T1566.001 |
| Ransomware deployment | 0.9 | persistence, lateral_movement | 2.7 | T1486 |

---

## Choke Point Analysis

Choke points are techniques required by multiple paths to crown jewel assets. Detecting a choke point technique detects all attack paths that pass through it.

### Choke Point Identification

The engagement planner identifies choke points by finding techniques in `credential_access` and `privilege_escalation` tactics that serve as prerequisites for multiple subsequent techniques targeting crown jewels.

Prioritize detection rule development and monitoring density around choke point techniques — hardening a choke point has multiplied defensive value.

### Common Choke Points by Environment

| Environment Type | Common Choke Points | Detection Priority |
|-----------------|--------------------|--------------------|
| Active Directory domain | T1003 (credential dump), T1558 (Kerberoasting) | Highest |
| AWS environment | T1078.004 (cloud account), iam:PassRole chains | Highest |
| Hybrid cloud | T1550.002 (PtH), T1021.006 (WinRM) | High |
| Containerized apps | T1610 (deploy container), T1611 (container escape) | High |

Full methodology: `references/attack-path-methodology.md`

---

## OPSEC Risk Assessment

OPSEC risk items identify actions that are likely to trigger detection or leave persistent artifacts.

### OPSEC Risk Categories

| Tactic | Primary OPSEC Risk | Mitigation |
|--------|------------------|------------|
| Credential Access | LSASS memory access triggers EDR | Use LSASS-less techniques (DCSync, Kerberoasting) where possible |
| Execution | PowerShell command-line logging | Use AMSI bypass or alternative execution methods in scope |
| Lateral Movement | NTLM lateral movement generates event 4624 type 3 | Use Kerberos where possible; avoid NTLM over the network |
| Persistence | Scheduled tasks generate event 4698 | Use less-monitored persistence mechanisms within scope |
| Exfiltration | Large outbound transfers trigger DLP | Stage data and use slow exfil if stealth is required |

### OPSEC Checklist Before Each Phase

1. Is the technique in scope per RoE?
2. Will it generate logs that blue team monitors actively?
3. Is there a less-detectable alternative that achieves the same objective?
4. If detected, will it reveal the full operation or only the current foothold?
5. Are cleanup artifacts defined for post-exercise removal?

---

## Crown Jewel Targeting

Crown jewel assets are the high-value targets that define the success criteria of a red team engagement.

### Crown Jewel Classification

| Crown Jewel Type | Target Indicators | Attack Paths |
|-----------------|------------------|--------------|
| Domain Controller | AD DS, NTDS.dit, SYSVOL | Kerberoasting → DCSync → Golden Ticket |
| Database servers | Production SQL, NoSQL, data warehouse | Lateral movement → DBA account → data staging |
| Payment systems | PCI-scoped network, card data vault | Network pivot → service account → exfiltration |
| Source code repositories | Internal Git, build systems | VPN → internal git → code signing keys |
| Cloud management plane | AWS management console, IAM admin | Phishing → credential → AssumeRole chain |

Crown jewel definition is agreed upon in the RoE — engagement success is measured by whether red team reaches defined crown jewels, not by the number of vulnerabilities found.

---

## Attack Path Methodology

Attack path analysis identifies all viable routes from the starting access level to each crown jewel.

### Path Scoring

Each path is scored by:
- **Total effort score** (sum of per-technique effort scores)
- **Choke point count** (how many choke points the path passes through)
- **Detection probability** (product of per-technique detection risks)

Lower effort + fewer choke points = path of least resistance for the attacker.

### Attack Path Graph Construction

```
external
  └─ T1566.001 (spearphishing) → initial_access
       └─ T1059.001 (PowerShell) → execution
            └─ T1003.001 (LSASS dump) → credential_access [CHOKE POINT]
                 └─ T1550.002 (Pass-the-Hash) → lateral_movement
                      └─ T1078.002 (domain account) → privilege_escalation
                           └─ Crown Jewel: Domain Controller
```

For the full scoring algorithm, choke point weighting, and effort-vs-impact matrix, see `references/attack-path-methodology.md`.

---

## Workflows

### Workflow 1: Quick Engagement Scoping (30 Minutes)

For scoping a focused red team exercise against a specific target:

```bash
# 1. Generate initial technique list from kill-chain coverage gaps
python3 scripts/engagement_planner.py --list-techniques

# 2. Build plan for external assumed-no-access scenario
python3 scripts/engagement_planner.py \
  --techniques T1566,T1190,T1059,T1003,T1021 \
  --access-level external \
  --crown-jewels "Database Server" \
  --authorized --json

# 3. Review choke_points and opsec_risks in output
# 4. Present kill-chain phases to stakeholders for scope approval
```

**Decision**: If choke_points are already covered by detection rules, focus on gaps. If not, those are the highest-value exercise targets.

### Workflow 2: Full Red Team Engagement (Multi-Week)

**Week 1 — Planning:**
1. Define crown jewels and success criteria with stakeholders
2. Sign RoE with defined scope, timeline, and out-of-scope exclusions
3. Build engagement plan with engagement_planner.py
4. Review OPSEC risks for each phase

**Week 2 — Execution (External Phase):**
1. Reconnaissance and target profiling
2. Initial access attempts (phishing, exploit public-facing)
3. Document each technique executed with timestamps
4. Log all detection events to validate blue team coverage

**Week 3 — Execution (Internal Phase):**
1. Establish persistence if initial access obtained
2. Execute credential access techniques (choke points)
3. Lateral movement toward crown jewels
4. Document when and how crown jewels were reached

**Week 4 — Reporting:**
1. Compile findings — techniques executed, detection rates, crown jewels reached
2. Map findings to detection gaps
3. Produce remediation recommendations prioritized by choke point impact
4. Deliver read-out to security leadership

### Workflow 3: Assumed Breach Tabletop

Simulate a compromised credential scenario for rapid detection testing:

```bash
# Assumed breach — credentialed access starting position
python3 scripts/engagement_planner.py \
  --techniques T1059,T1078,T1021,T1550,T1003,T1048 \
  --access-level credentialed \
  --crown-jewels "Active Directory,S3 Data Bucket" \
  --target-count 20 \
  --authorized --json | jq '.phases, .choke_points, .opsec_risks'

# Run across multiple access levels to compare path options
for level in external internal credentialed; do
  echo "=== ${level} ==="
  python3 scripts/engagement_planner.py \
    --techniques T1059,T1078,T1003,T1021 \
    --access-level "${level}" \
    --authorized --json | jq '.total_effort_score, .phases | keys'
done
```

---

## Anti-Patterns

1. **Operating without written authorization** — Unauthorized red team activity against any system you don't own or have explicit permission to test is a criminal offense. The `--authorized` flag must reflect a real signed RoE, not just running the tool to bypass the check. Authorization must predate execution.
2. **Skipping kill-chain phase ordering** — Jumping directly to lateral movement without establishing persistence means a single detection wipes out the entire foothold. Follow the kill-chain phase order — each phase builds the foundation for the next.
3. **Not defining crown jewels before starting** — Engagements without defined success criteria drift into open-ended vulnerability hunting. Crown jewels and success conditions must be agreed upon in the RoE before the first technique is executed.
4. **Ignoring OPSEC risks in the plan** — Red team exercises test blue team detection. Deliberately avoiding all detectable techniques produces an unrealistic engagement that doesn't validate detection coverage. Use OPSEC risks to understand detection exposure, not to avoid it entirely.
5. **Failing to document executed techniques in real time** — Retroactive documentation of what was executed is unreliable. Log each technique, timestamp, and outcome as it happens. Post-engagement reporting must be based on contemporaneous records.
6. **Not cleaning up artifacts post-exercise** — Persistence mechanisms, new accounts, modified configurations, and staged data must be removed after engagement completion. Leaving red team artifacts creates permanent security risks and can be confused with real attacker activity.
7. **Treating path of least resistance as the only path** — Attackers adapt. Test multiple attack paths including higher-effort routes that may evade detection. Validating that the easiest path is detected is necessary but not sufficient.

---

## Cross-References

| Skill | Relationship |
|-------|-------------|
| [threat-detection](../threat-detection/SKILL.md) | Red team technique execution generates realistic TTPs that validate threat hunting hypotheses |
| [incident-response](../incident-response/SKILL.md) | Red team activity should trigger incident response procedures — detection and response quality is a primary success metric |
| [cloud-security](../cloud-security/SKILL.md) | Cloud posture findings (IAM misconfigs, S3 exposure) become red team attack path targets |
| [security-pen-testing](../security-pen-testing/SKILL.md) | Pen testing focuses on specific vulnerability exploitation; red team focuses on end-to-end kill-chain simulation to crown jewels |
