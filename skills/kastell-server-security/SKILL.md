---
name: kastell-server-security
description: "Server security auditing and hardening using Kastell MCP tools. Run 413-check security audits across 29 categories (SSH, Firewall, Docker, TLS, HTTP Headers, etc.), analyze results by security domain, apply production hardening, and manage fleet-wide security posture. Requires kastell plugin installed. Triggers: 'server audit', 'security audit', 'harden server', 'server security', 'audit score'."
---

# Server Security Audit & Hardening

Analyze and improve server security posture using Kastell's 13 MCP tools. Covers the full lifecycle: audit → analyze → harden → verify.

## Prerequisites

Install the kastell plugin:

```
claude plugins add kastell
```

Requires at least one registered server (`kastell add` or `server_manage` MCP tool).

## Workflow

### 1. Audit

Run a comprehensive security scan (413 checks, 29 categories):

```
Use server_audit tool with server: "<name>" and format: "summary"
```

For compliance-filtered results:

```
Use server_audit tool with framework: "cis-level1" (or pci-dss, hipaa)
```

### 2. Analyze by Security Domain

Map audit findings to 5 security domains:

| Domain | Categories | Focus |
|--------|-----------|-------|
| Perimeter | Network, Firewall, DNS | External attack surface |
| Authentication | SSH, Auth, Crypto, Accounts | Identity controls |
| Runtime | Docker, Services, Boot, Scheduling | Service exposure |
| Internals | Filesystem, Logging, Kernel, Memory | System hardening |
| Compliance | Updates, TLS, HTTP Headers, Secrets, etc. | Hygiene |

### 3. Harden

Apply production hardening (19 steps: SSH, fail2ban, UFW, sysctl, auditd, AIDE, Docker):

```
Use server_lock tool with server: "<name>" and dryRun: true
```

Review the dry-run output, then apply with `production: true`.

### 4. Verify

Re-run audit to confirm score improvement:

```
Use server_audit tool with server: "<name>" and format: "score"
```

## Available MCP Tools

| Tool | Purpose |
|------|---------|
| `server_audit` | 413-check security scan with CIS/PCI-DSS/HIPAA mapping |
| `server_lock` | 19-step production hardening |
| `server_secure` | Granular SSH, firewall, domain/SSL management |
| `server_doctor` | Proactive health analysis (disk, swap, stale packages) |
| `server_fleet` | Fleet-wide security dashboard |
| `server_info` | Server status and health checks |
| `server_logs` | Log retrieval and system metrics |
| `server_guard` | Autonomous security monitoring daemon |
| `server_evidence` | Forensic evidence collection with SHA256 checksums |
| `server_backup` | Backup/restore and cloud snapshots |
| `server_provision` | New server provisioning (Hetzner, DigitalOcean, Vultr, Linode) |
| `server_manage` | Server registration and lifecycle |
| `server_maintain` | Updates, restarts, maintenance cycles |

## Quick Wins

After an audit, prioritize fixes by severity:

1. **Critical** (3x weight): Exploitable vulnerabilities — fix immediately
2. **Warning** (2x weight): Security risks — fix in next maintenance window
3. **Info** (1x weight): Best practices — address when convenient

Use `server_audit` with `explain: true` to get per-check remediation guidance.
