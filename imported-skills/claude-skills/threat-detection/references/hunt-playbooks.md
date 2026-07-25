# Threat Hunt Playbooks

> **Defensive documentation — not malware.** This file lists detection queries
> and indicators-of-attack for blue-team threat hunting. It cites legitimate
> Windows binaries (`certutil.exe`, `regsvr32.exe`, `mshta.exe`, `msiexec.exe`,
> `rundll32.exe`) and the LOLBin command-line patterns associated with their
> abuse. No executable code is shipped here.
>
> Some endpoint AV/EDR products (Bitdefender, Defender, etc.) heuristically
> flag plain-text documents that contain these strings. If your scanner
> quarantines this file, allow-list the path
> `engineering-team/skills/threat-detection/references/hunt-playbooks.md`
> or exclude the `claude-skills` checkout. The strings appear inside markdown
> code spans / tables; they cannot execute from a `.md` file. Tracking issue:
> [#533](https://github.com/alirezarezvani/claude-skills/issues/533).

Reference playbooks for common high-value hunt hypotheses. Each playbook defines the hypothesis, required data sources, query approach, and confirmation criteria.

---

## Playbook 1: WMI-Based Lateral Movement

**Hypothesis:** An attacker is using Windows Management Instrumentation (WMI) for remote code execution as part of lateral movement.

**MITRE Technique:** T1047 — Windows Management Instrumentation

**Data Sources Required:**
- WMI activity logs (Microsoft-Windows-WMI-Activity/Operational)
- Sysmon Event ID 1 (Process Create) and Event ID 20 (WmiEvent)
- EDR process telemetry

**Query Approach:**
1. Search for WMI processes (`WmiPrvSE.exe`, `scrcons.exe`) spawning child processes other than `WmiApSrv.exe`
2. Filter for WMI events where `ActiveScriptEventConsumer` or `CommandLineEventConsumer` is created
3. Cross-reference source host with authentication logs for lateral movement source identification

**Confirmation Criteria:**
- WMI child process execution on a host where the triggering identity is not the local admin or system
- WMI execution targeting multiple hosts within a short time window (>3 hosts in 10 minutes = high confidence)

**False Positive Sources:**
- SCCM/Configuration Manager uses WMI heavily for inventory — whitelist SCCM service accounts
- Monitoring agents (SolarWinds, Nagios) use WMI for performance data — whitelist monitoring identities

---

## Playbook 2: Living-off-the-Land Binary (LOLBin) Execution

**Hypothesis:** An attacker is using legitimate Windows binaries (`certutil.exe`, `regsvr32.exe`, `mshta.exe`, `msiexec.exe`) for payload delivery or execution, bypassing application allowlisting.

**MITRE Technique:** T1218 — System Binary Proxy Execution

**Data Sources Required:**
- Process creation logs with full command-line (Sysmon Event ID 1)
- Network connection logs (Sysmon Event ID 3)
- DNS query logs

**High-Value LOLBin Indicators:**

| Binary | Suspicious Indicators | Common Abuse |
|--------|----------------------|--------------|
| certutil.exe | `-decode` or `-urlcache -split -f http://` | Base64 decode, remote file download |
| regsvr32.exe | `/s /u /i:http://` or `scrobj.dll` | Remote scriptlet execution (Squiblydoo) |
| mshta.exe | Any URL as argument | Remote HTA execution |
| msiexec.exe | `/quiet /i http://` | Remote MSI execution |
| wscript.exe | Executing from temp/download directories | VBScript malware execution |
| cscript.exe | Executing from temp/download directories | JScript/VBScript malware |
| rundll32.exe | Calling exports from temp-directory DLLs | DLL side-loading |

**Query Approach:**
1. Search for listed LOLBins with network-connectivity-indicating arguments (URLs, IP addresses)
2. Identify LOLBin executions where the parent process is unusual (Office apps, browsers, scripting engines)
3. Flag executions from non-standard paths (temp directories, user AppData)

**Confirmation Criteria:**
- LOLBin making outbound network connection (Sysmon Event ID 3 within 30 seconds of Event ID 1)
- LOLBin executing from a temp or user-writable directory
- LOLBin spawned from Office application or browser process

---

## Playbook 3: C2 Beaconing Detection

**Hypothesis:** A compromised host is communicating with a command-and-control server on a regular interval, indicating active malware or attacker control.

**MITRE Technique:** T1071.001 — Application Layer Protocol: Web Protocols

**Data Sources Required:**
- Proxy or web gateway logs (URL, user-agent, bytes transferred, connection duration)
- NetFlow or firewall session logs
- DNS resolver logs

**Beaconing Indicators:**

| Indicator | Threshold | Notes |
|----------|-----------|-------|
| Regular connection interval | ±10% jitter from mean | Calculate standard deviation of inter-connection times |
| Low data volume per connection | <1 KB per session | C2 check-in packets are typically small |
| Consistent user-agent string | Same UA across all requests | Hardcoded user agents in malware |
| Domain generation algorithm (DGA) | High entropy domain names | Compare against entropy baseline for org |
| Long-lived connections with low data transfer | >1 hour session, <10 KB total | HTTP long-polling C2 |

**Query Approach:**
1. Group outbound connections by source host + destination IP/domain
2. Calculate standard deviation of connection intervals per group
3. Flag groups where standard deviation is <10% of mean interval (regular beaconing)
4. Cross-reference destination IPs/domains against threat intel feeds

**Confirmation Criteria:**
- Connection regularity (coefficient of variation <0.10) from a non-browser process
- Destination domain resolves to IP with no PTR record or recently registered domain
- Connection volume inconsistent with claimed user-agent (browser UA but non-browser process)

---

## Playbook 4: Pass-the-Hash Lateral Movement

**Hypothesis:** An attacker is using stolen NTLM hashes for lateral movement without cracking the underlying password.

**MITRE Technique:** T1550.002 — Use Alternate Authentication Material: Pass the Hash

**Data Sources Required:**
- Windows Security Event Logs (Event ID 4624 — Logon)
- Domain controller authentication logs
- EDR telemetry for LSASS memory access (pre-harvest detection)

**Pass-the-Hash Indicators:**

| Event | Field | Suspicious Value |
|-------|-------|-----------------|
| Event 4624 | Logon Type | 3 (Network) |
| Event 4624 | Authentication Package | NTLM |
| Event 4624 | Key Length | 0 (NTLMv2) |
| Event 4624 | Source Network Address | Different from last successful logon of same account |

**Query Approach:**
1. Filter Event 4624 for LogonType=3 with NTLM authentication
2. Group by account name — flag accounts with authentication events from multiple source IPs within a 1-hour window
3. Correlate source hosts: the harvesting host (LSASS access) and the destination hosts (lateral movement targets) should form a pattern
4. Look for service account authentication to interactive desktop sessions (a service account logging on Type 2/10 is anomalous)

**Confirmation Criteria:**
- Same account authenticating to 3+ hosts via NTLM within 30 minutes
- Source hosts are workstations, not servers (server-to-server NTLM is more common legitimately)
- Account's normal authentication pattern is Kerberos — NTLM is anomalous for this identity
