# Emergency Procedures Reference

## Secret Leak Response Playbook

### Severity Classification

| Severity | Definition | Response Time | Example |
|----------|-----------|---------------|---------|
| **P0 — Critical** | Production credentials exposed publicly | Immediate (15 min) | Database password in public GitHub repo |
| **P1 — High** | Internal credentials exposed beyond intended scope | 1 hour | API key in build logs accessible to wider org |
| **P2 — Medium** | Non-production credentials exposed | 4 hours | Staging DB password in internal wiki |
| **P3 — Low** | Expired or limited-scope credential exposed | 24 hours | Rotated API key found in old commit history |

### P0/P1 Response Procedure

**Phase 1: Contain (0-15 minutes)**

1. **Identify the leaked secret**
   - What credential was exposed? (type, scope, permissions)
   - Where was it exposed? (repo, log, error page, third-party service)
   - When was it first exposed? (commit timestamp, log timestamp)
   - Is the exposure still active? (repo public? log accessible?)

2. **Revoke immediately**
   - Database password: `ALTER ROLE app_user WITH PASSWORD 'new_password';`
   - API key: Regenerate via provider console/API
   - Vault token: `vault token revoke <token>`
   - AWS access key: `aws iam delete-access-key --access-key-id <key>`
   - Cloud service account: Delete and recreate key
   - TLS certificate: Revoke via CA, generate new certificate

3. **Remove exposure**
   - Public repo: Remove file, force-push to remove from history, request GitHub cache purge
   - Build logs: Delete log artifacts, rotate CI/CD secrets
   - Error page: Deploy fix to suppress secret in error output
   - Third-party: Contact vendor for log purge if applicable

4. **Deploy new credentials**
   - Update secret store with rotated credential
   - Restart affected services to pick up new credential
   - Verify services are healthy with new credential

**Phase 2: Assess (15-60 minutes)**

5. **Audit blast radius**
   - Query Vault/cloud SM audit logs for the compromised credential
   - Check for unauthorized usage during the exposure window
   - Review network logs for suspicious connections from unknown IPs
   - Check if the compromised credential grants access to other secrets (privilege escalation)

6. **Notify stakeholders**
   - Security team (always)
   - Service owners for affected systems
   - Compliance team if regulated data was potentially accessed
   - Legal if customer data may have been compromised
   - Executive leadership for P0 incidents

**Phase 3: Recover (1-24 hours)**

7. **Rotate adjacent credentials**
   - If the leaked credential could access other secrets, rotate those too
   - If a Vault token leaked, check what policies it had — rotate everything accessible

8. **Harden against recurrence**
   - Add pre-commit hook to detect secrets (e.g., `gitleaks`, `detect-secrets`)
   - Review CI/CD pipeline for secret masking
   - Audit who has access to the source of the leak

**Phase 4: Post-Mortem (24-72 hours)**

9. **Document incident**
   - Timeline of events
   - Root cause analysis
   - Impact assessment
   - Remediation actions taken
   - Preventive measures added

### Response Communication Template

```
SECURITY INCIDENT — SECRET EXPOSURE
Severity: P0/P1
Time detected: YYYY-MM-DD HH:MM UTC
Secret type: [database password / API key / token / certificate]
Exposure vector: [public repo / build log / error output / other]
Status: [CONTAINED / INVESTIGATING / RESOLVED]

Immediate actions taken:
- [ ] Credential revoked at source
- [ ] Exposure removed
- [ ] New credential deployed
- [ ] Services verified healthy
- [ ] Audit log review in progress

Blast radius assessment: [PENDING / COMPLETE — no unauthorized access / COMPLETE — unauthorized access detected]

Next update: [time]
Incident commander: [name]
```

## Vault Seal/Unseal Procedures

### Understanding Seal Status

Vault uses a **seal** mechanism to protect the encryption key hierarchy. When sealed, Vault cannot decrypt any data or serve any requests.

```
Sealed State:
  Vault process running → YES
  API responding → YES (503 Sealed)
  Serving secrets → NO
  All active leases → FROZEN (not revoked)
  Audit logging → NO

Unsealed State:
  Vault process running → YES
  API responding → YES (200 OK)
  Serving secrets → YES
  Active leases → RESUMING
  Audit logging → YES
```

### When to Seal Vault (Emergency Only)

Seal Vault when:
- Active intrusion on Vault infrastructure is confirmed
- Vault server compromise is suspected (unauthorized root access)
- Encryption key material may have been extracted
- Regulatory/legal hold requires immediate data access prevention

**Do NOT seal for:**
- Routine maintenance (use graceful shutdown instead)
- Single-node issues in HA cluster (let standby take over)
- Suspected secret leak (revoke the secret, don't seal Vault)

### Seal Procedure

```bash
# Seal a single node
vault operator seal

# Seal all nodes (HA cluster)
# Seal each node individually — leader last
vault operator seal -address=https://vault-standby-1:8200
vault operator seal -address=https://vault-standby-2:8200
vault operator seal -address=https://vault-leader:8200
```

**Impact of sealing:**
- All active client connections dropped immediately
- All token and lease timers paused
- Applications lose secret access — prepare for cascading failures
- Monitoring will fire alerts for sealed state

### Unseal Procedure (Shamir Keys)

Requires a quorum of key holders (e.g., 3 of 5).

```bash
# Each key holder provides their unseal key
vault operator unseal <key-1>
vault operator unseal <key-2>
vault operator unseal <key-3>
# Vault unseals after reaching threshold
```

**Operational checklist after unseal:**
1. Verify health: `vault status` shows `Sealed: false`
2. Check audit devices: `vault audit list` — confirm all enabled
3. Check auth methods: `vault auth list`
4. Verify HA status: `vault operator raft list-peers`
5. Check lease count: monitor `vault.expire.num_leases`
6. Verify applications reconnecting (check application logs)

### Unseal Procedure (Auto-Unseal)

If using cloud KMS auto-unseal, Vault unseals automatically on restart:

```bash
# Restart Vault service
systemctl restart vault

# Verify unseal (should happen within seconds)
vault status
```

**If auto-unseal fails:**
- Check cloud KMS key permissions (IAM role may have been modified)
- Check network connectivity to cloud KMS endpoint
- Check KMS key status (not disabled, not scheduled for deletion)
- Check Vault logs: `journalctl -u vault -f`

## Mass Credential Rotation Procedure

When a broad compromise requires rotating many credentials simultaneously.

### Pre-Rotation Checklist

- [ ] Identify all credentials in scope
- [ ] Map credential dependencies (which services use which credentials)
- [ ] Determine rotation order (databases before applications)
- [ ] Prepare rollback plan for each credential
- [ ] Notify all service owners
- [ ] Schedule maintenance window if zero-downtime not possible
- [ ] Stage new credentials in secret store (but don't activate yet)

### Rotation Order

1. **Infrastructure credentials** — Database root passwords, cloud IAM admin keys
2. **Service credentials** — Application database users, API keys
3. **Integration credentials** — Third-party API keys, webhook secrets
4. **Human credentials** — Force password reset, revoke SSO sessions

### Rollback Plan

For each credential, document:
- Previous value (store in sealed emergency envelope or HSM)
- How to revert (specific command or API call)
- Verification step (how to confirm old credential works)
- Maximum time to rollback (SLA)

## Vault Recovery Procedures

### Lost Unseal Keys

If unseal keys are lost and auto-unseal is not configured:

1. **If Vault is currently unsealed:** Enable auto-unseal immediately, then reseal/unseal with KMS
2. **If Vault is sealed:** Data is irrecoverable without keys. Restore from Raft snapshot backup
3. **Prevention:** Store unseal keys in separate, secure locations (HSMs, safety deposit boxes). Use auto-unseal for production.

### Raft Cluster Recovery

**Single node failure (cluster still has quorum):**
```bash
# Remove failed peer
vault operator raft remove-peer <failed-node-id>

# Add replacement node
# (new node joins via retry_join in config)
```

**Loss of quorum (majority of nodes failed):**
```bash
# On a surviving node with recent data
vault operator raft join -leader-ca-cert=@ca.crt https://surviving-node:8200

# If no node survives, restore from snapshot
vault operator raft snapshot restore /backups/latest.snap
```

### Root Token Recovery

If root token is lost (it should be revoked after initial setup):

```bash
# Generate new root token (requires unseal key quorum)
vault operator generate-root -init
# Each key holder provides their key
vault operator generate-root -nonce=<nonce> <unseal-key>
# After quorum, decode the encoded token
vault operator generate-root -decode=<encoded-token> -otp=<otp>
```

**Best practice:** Generate a root token only when needed, complete the task, then revoke it:
```bash
vault token revoke <root-token>
```

## Incident Severity Escalation Matrix

| Signal | Escalation |
|--------|-----------|
| Single secret exposed in internal log | P2 — Rotate secret, add log masking |
| Secret in public repository (no evidence of use) | P1 — Immediate rotation, history scrub |
| Secret in public repository (evidence of unauthorized use) | P0 — Full incident response, legal notification |
| Vault node compromised | P0 — Seal cluster, rotate all accessible secrets |
| Cloud KMS key compromised | P0 — Create new key, re-encrypt all secrets, rotate all credentials |
| Audit log gap detected | P1 — Investigate cause, assume worst case for gap period |
| Multiple failed auth attempts from unknown source | P2 — Block source, investigate, rotate targeted credentials |
