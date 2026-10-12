---
name: hardening
description: "Complete security hardening of a Linux server based on CIS Benchmarks, NIST 800-123, and ANSSI BP-028. Smart service discovery to avoid disruption. 4 hardening levels (minimal/standard/enhanced/paranoid). Installs open-source security tools, hardens SSH/kernel/firewall/systemd/permissions, runs all scans, generates a compliance report."
user-invocable: true
disable-model-invocation: true
allowed-tools: Bash, Read, Write, Edit, Grep, Glob, Agent, TaskCreate, TaskUpdate
argument-hint: "[minimal|standard|enhanced|paranoid|scan-only|report]"
effort: max
---

# Linux Server Security Hardening Skill
## Based on CIS Benchmarks, NIST SP 800-123, ANSSI BP-028 v2.0 & DevSec Hardening Framework

You are performing a **security hardening** of a Linux server. You MUST be systematic, intelligent, and non-disruptive. Follow ALL phases in order.

---

## Hardening Levels (inspired by ANSSI BP-028)

| Level | Argument | Description | Use Case |
|-------|----------|-------------|----------|
| **Minimal** | `minimal` | Essential security baseline. Quick, low risk. | Dev servers, temporary VMs |
| **Standard** | `standard` or empty | Full hardening with all tools. Balanced. | Production servers, web apps |
| **Enhanced** | `enhanced` | Aggressive hardening + systemd sandboxing + advanced kernel params. | Exposed servers, compliance (PCI-DSS, HIPAA) |
| **Paranoid** | `paranoid` | Maximum lockdown. Kernel lockdown, restricted /proc, seccomp everywhere. May break some apps. | High-security, sensitive data, military-grade |

Special modes:
- **scan-only**: Run all security scans and generate report (no changes)
- **report**: Status report of current security posture (no changes)

`$ARGUMENTS` determines the level. Default is `standard` if empty.

---

## PHASE 0: Smart Reconnaissance & Service Discovery (ALL LEVELS)

**This is the most critical phase. NEVER skip it.**

Before making ANY changes, perform a complete system audit:

### 0.1 System Information
```bash
cat /etc/os-release
uname -a
whoami
hostname -f
df -h
free -h
nproc
uptime
```

### 0.2 Running Services & Applications Discovery
```bash
# All running services
systemctl list-units --type=service --state=running

# All listening ports with process names
ss -tlnp

# All established connections
ss -tnp state established

# Docker containers if Docker is present
docker ps 2>/dev/null

# Web server detection
which nginx apache2 httpd caddy 2>/dev/null
nginx -v 2>&1; apache2 -v 2>&1; httpd -v 2>&1

# Database detection
which mysql psql mongod redis-server redis-cli elasticsearch 2>/dev/null
systemctl is-active mysql postgresql mongod redis redis-server elasticsearch 2>/dev/null

# Mail server detection
which postfix sendmail dovecot 2>/dev/null
systemctl is-active postfix sendmail dovecot 2>/dev/null

# Application frameworks
which node python3 java php ruby go 2>/dev/null

# Cron jobs (user's scheduled tasks)
crontab -l 2>/dev/null; ls /etc/cron.d/ 2>/dev/null

# Desktop vs Server detection
if [ -n "$XDG_CURRENT_DESKTOP" ] || [ -n "$DESKTOP_SESSION" ] || systemctl is-active display-manager &>/dev/null; then
  echo "DESKTOP ENVIRONMENT DETECTED"
else
  echo "SERVER MODE"
fi

# Browser detection (impacts /dev/shm noexec)
which firefox chromium chrome brave 2>/dev/null
```

### 0.3 Current Security Posture
```bash
# Current firewall
iptables -L -n 2>/dev/null; ufw status 2>/dev/null

# SSH config
sshd -T 2>/dev/null | grep -E "permitrootlogin|passwordauth|x11forwarding|maxauthtries"

# SSH audit (if ssh-audit is available or install it)
ssh-audit localhost 2>/dev/null | head -20

# Existing security tools
which fail2ban-client lynis rkhunter clamdscan auditctl aide 2>/dev/null

# AppArmor / SELinux status
aa-status 2>/dev/null; getenforce 2>/dev/null

# Sudo configuration audit
grep -r "NOPASSWD" /etc/sudoers /etc/sudoers.d/ 2>/dev/null

# Users with shell access
grep -v '/nologin\|/false' /etc/passwd | grep -v '^#'

# Pending security updates
apt list --upgradable 2>/dev/null | grep -i security | head -10

# NTP sync status
timedatectl status 2>/dev/null | grep -E "synchronized|NTP"
```

### 0.4 Service Impact Analysis

**CRITICAL: Present findings to the user BEFORE proceeding.**

Generate a service impact table:

```
## Services detectes sur cette machine

| Service | Port | Process | Impact potentiel du hardening |
|---------|------|---------|-------------------------------|
| SSH     | 22   | sshd    | Config modifiee, acces preserve |
| Nginx   | 80   | nginx   | Headers ajoutes, TLS durci |
| Docker  | -    | dockerd | ip_forward preserve |
| ...     | ...  | ...     | ... |

## Services qui DOIVENT rester accessibles:
- [list]

## Services a desactiver potentiellement:
- [list — ASK USER before disabling]
```

**ASK the user**: "Voici les services detectes. Y a-t-il des services que je ne dois PAS toucher ou des ports supplementaires a ouvrir dans le firewall?"

Wait for user response before proceeding to Phase 1. If the user says to continue without changes, proceed.

---

## PHASE 1: System Update (ALL LEVELS)

```bash
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq
apt-get upgrade -y -qq
```

---

## PHASE 2: Install Security Tools (ALL LEVELS)

### Minimal level:
```bash
apt-get install -y -qq fail2ban ufw unattended-upgrades apt-listchanges \
  libpam-pwquality needrestart debsums
```

### Standard level (adds to minimal):
```bash
apt-get install -y -qq \
  auditd audispd-plugins rkhunter chkrootkit lynis \
  clamav clamav-daemon clamav-freshclam aide \
  apparmor apparmor-utils apparmor-profiles apparmor-profiles-extra \
  libpam-tmpdir acct sysstat net-tools arpwatch logwatch \
  psad firejail openssh-server nmap nikto john \
  tcpdump wireshark-common tshark htop iotop iftop \
  secure-delete gnupg2 certbot \
  apt-transport-https ca-certificates curl software-properties-common
```

Also install from pip if available (STANDARD+):
```bash
pip3 install ssh-audit testssl.sh 2>/dev/null || true
# Or from apt if packaged
apt-get install -y -qq ssh-audit 2>/dev/null || true
```

### Enhanced level (adds to standard):
```bash
apt-get install -y -qq openscap-scanner scap-security-guide \
  osquery 2>/dev/null || true
# Docker Bench for Security (if Docker detected)
if command -v docker &>/dev/null; then
  docker run --rm --net host --pid host --userns host --cap-add audit_control \
    -v /etc:/etc:ro -v /var/lib:/var/lib:ro -v /var/run/docker.sock:/var/run/docker.sock:ro \
    docker/docker-bench-security 2>/dev/null || true
fi
```

### Paranoid level (adds to enhanced):
```bash
apt-get install -y -qq \
  libseccomp-dev seccomp bpftool 2>/dev/null || true
```

If any package fails, log it and continue. Never abort for a missing package.

---

## PHASE 3: SSH Hardening (ALL LEVELS)

1. **Backup**: `cp /etc/ssh/sshd_config /etc/ssh/sshd_config.backup.$(date +%Y%m%d)`
2. **Create** `/etc/ssh/sshd_config.d/hardening.conf` from `${CLAUDE_SKILL_DIR}/templates/sshd_hardening.conf`

### Level-specific adjustments:

**Minimal**: Only set `PasswordAuthentication no`, `PermitRootLogin prohibit-password`, `MaxAuthTries 4`

**Standard**: Full template (Protocol 2, key-only, strong ciphers, disable forwarding, logging VERBOSE)

**Enhanced**: Add `AllowUsers` or `AllowGroups` restriction (ask user), enable 2FA recommendation

**Paranoid**: Set `PermitRootLogin no` (require non-root user + sudo), `MaxSessions 2`, `LoginGraceTime 20`

3. **Create** warning banners in `/etc/issue.net` and `/etc/issue`
4. **Validate**: `sshd -t` — MUST pass before reload
5. **Reload**: `systemctl reload ssh`

**CRITICAL**: NEVER lock out the current SSH session.

---

## PHASE 4: Kernel Hardening via sysctl (STANDARD+)

Create `/etc/sysctl.d/99-security-hardening.conf` from `${CLAUDE_SKILL_DIR}/templates/sysctl_hardening.conf`

### Level-specific additions:

**Enhanced** — add:
```
# Enhanced: restrict ASLR entropy
vm.mmap_rnd_bits = 32
vm.mmap_rnd_compat_bits = 16
# Disable SACK (CVE-2019-11477)
net.ipv4.tcp_sack = 0
# Disable kexec
kernel.kexec_load_disabled = 1
# Restrict TTY line discipline
dev.tty.ldisc_autoload = 0
# Restrict userfaultfd
vm.unprivileged_userfaultfd = 0
```

**Paranoid** — add:
```
# Paranoid: full ICMP block
net.ipv4.icmp_echo_ignore_all = 1
# Disable all printk
kernel.printk = 3 3 3 3
```

**IMPORTANT**: If Docker is running, do NOT disable `net.ipv4.ip_forward`.

Apply: `sysctl --system`
Verify: `sysctl net.ipv4.tcp_syncookies net.ipv4.conf.all.rp_filter kernel.randomize_va_space kernel.dmesg_restrict`

---

## PHASE 5: Firewall (ALL LEVELS)

### Minimal:
```bash
ufw default deny incoming
ufw default allow outgoing
ufw limit ssh comment 'SSH rate-limited'
# Add rules for services detected in Phase 0
ufw --force enable
```

### Standard+:
```bash
ufw --force reset
ufw default deny incoming
ufw default allow outgoing
ufw limit ssh comment 'SSH rate-limited'
ufw logging medium
# Add rules for services detected in Phase 0 (HTTP, HTTPS, etc.)
ufw --force enable
```

### Paranoid:
- Default deny OUTGOING too, then whitelist: DNS (53), HTTP/S (80/443), NTP (123)
- Enable HIGH logging

**CRITICAL**: Always add rules for services detected in Phase 0 BEFORE enabling the firewall.

---

## PHASE 6: Fail2ban (ALL LEVELS)

### Minimal: SSH jail only
### Standard: Create `/etc/fail2ban/jail.local` from `${CLAUDE_SKILL_DIR}/templates/fail2ban_jail.conf`
### Enhanced/Paranoid: Add custom filters for detected applications (PostgreSQL, MySQL, phpMyAdmin, WordPress, etc.)

Progressive ban policy (all levels):
- `bantime.increment = true`
- `bantime.factor = 2`
- `bantime.maxtime = 604800` (7 days)
- Recidive jail for repeat offenders

```bash
systemctl enable fail2ban && systemctl restart fail2ban
fail2ban-client status
```

---

## PHASE 7: Auditd Rules (STANDARD+)

Create `/etc/audit/rules.d/hardening.rules` from `${CLAUDE_SKILL_DIR}/templates/audit_rules.conf`

### Enhanced/Paranoid additions:
- Monitor all privileged command executions:
  `find / -xdev -type f \( -perm -4000 -o -perm -2000 \) | while read f; do echo "-a always,exit -F path=$f -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged"; done`
- Monitor `/etc/` entirely: `-w /etc/ -p wa -k etc_changes`
- Immutable rules: `-e 2` (requires reboot to modify)

```bash
augenrules --load
auditctl -l | wc -l
```

---

## PHASE 8: Configure Security Tools (STANDARD+)

### ClamAV
```bash
systemctl stop clamav-freshclam
freshclam
systemctl enable clamav-freshclam && systemctl start clamav-freshclam
systemctl enable clamav-daemon && systemctl start clamav-daemon
```

### AIDE (run in background — slow)
```bash
aideinit &
# Later: cp /var/lib/aide/aide.db.new /var/lib/aide/aide.db
```

### rkhunter
```bash
rkhunter --update && rkhunter --propupd
```
Create `/etc/rkhunter.conf.local` with appropriate ALLOW_SSH settings.

### PSAD
Configure hostname and auto-IDS in `/etc/psad/psad.conf`.

### Process accounting & sysstat
```bash
systemctl enable acct && systemctl start acct
systemctl enable sysstat && systemctl start sysstat
```

### Logwatch
Configure `/etc/logwatch/conf/logwatch.conf` with `Detail = High`.

### NTP Time Synchronization (ALL LEVELS)
Accurate time is critical for logs, TLS certificates, TOTP 2FA, and Kerberos.
```bash
timedatectl set-ntp true
systemctl enable systemd-timesyncd
systemctl start systemd-timesyncd
timedatectl status
```

### Shared Memory Hardening (STANDARD+)
Secure `/dev/shm` to prevent shared memory attacks:
```bash
# Check if browsers are installed (JIT needs exec on /dev/shm)
if command -v firefox &>/dev/null || command -v chromium &>/dev/null || command -v google-chrome &>/dev/null; then
  # Desktop with browsers: apply nosuid,nodev only (preserve JIT)
  echo "tmpfs /dev/shm tmpfs defaults,nosuid,nodev 0 0" >> /etc/fstab
else
  # Server: full lockdown with noexec
  echo "tmpfs /dev/shm tmpfs defaults,nosuid,nodev,noexec 0 0" >> /etc/fstab
fi
mount -o remount /dev/shm
```

### Sudo Hardening (STANDARD+)
```bash
# Audit dangerous NOPASSWD entries
grep -r "NOPASSWD" /etc/sudoers /etc/sudoers.d/ 2>/dev/null
# Add secure defaults
echo 'Defaults use_pty' >> /etc/sudoers.d/hardening
echo 'Defaults logfile="/var/log/sudo.log"' >> /etc/sudoers.d/hardening
echo 'Defaults !visiblepw' >> /etc/sudoers.d/hardening
echo 'Defaults timestamp_timeout=5' >> /etc/sudoers.d/hardening
chmod 440 /etc/sudoers.d/hardening
visudo -c  # ALWAYS validate
```

### Remove Dangerous Packages (STANDARD+)
```bash
# Remove insecure legacy services if present
apt-get purge -y -qq telnet rsh-client rsh-server xinetd 2>/dev/null || true
```

---

## PHASE 9: File & Permission Hardening (ALL LEVELS)

### 9.1 Critical file permissions (ALL)
```bash
chmod 600 /etc/shadow /etc/gshadow
chmod 644 /etc/passwd /etc/group
chmod 600 /etc/ssh/sshd_config
chmod 700 /etc/ssh/sshd_config.d
chmod 600 /etc/crontab
chmod 700 /etc/cron.d /etc/cron.daily /etc/cron.weekly /etc/cron.monthly /etc/cron.hourly
chmod 600 /boot/grub/grub.cfg 2>/dev/null
chmod 700 /root
```

### 9.2 Restrict cron/at (STANDARD+)
```bash
echo "root" > /etc/cron.allow
echo "root" > /etc/at.allow
chmod 600 /etc/cron.allow /etc/at.allow
```

### 9.3 Disable core dumps (STANDARD+)
```bash
echo "* hard core 0" >> /etc/security/limits.d/hardening.conf
echo "* soft core 0" >> /etc/security/limits.d/hardening.conf
```
Systemd: create `/etc/systemd/coredump.conf.d/disable.conf`:
```
[Coredump]
Storage=none
ProcessSizeMax=0
```

### 9.4 Password policy (ALL)
`/etc/security/pwquality.conf`:
- **Minimal**: minlen=12, minclass=2
- **Standard**: minlen=14, minclass=3, dcredit=-1, ucredit=-1, ocredit=-1, lcredit=-1
- **Enhanced/Paranoid**: minlen=16, minclass=4, maxrepeat=2, dictcheck=1, enforcing=1

### 9.5 login.defs (STANDARD+)
```
PASS_MAX_DAYS   90
PASS_MIN_DAYS   7
PASS_WARN_AGE   14
UMASK           027
LOGIN_RETRIES   3
LOGIN_TIMEOUT   60
SHA_CRYPT_MIN_ROUNDS  10000
```

### 9.6 Disable unnecessary kernel modules (STANDARD+)
Create `/etc/modprobe.d/hardening.conf` from `${CLAUDE_SKILL_DIR}/templates/modprobe_hardening.conf`

### 9.7 Automatic security updates (ALL)
Configure unattended-upgrades for security-only patches.

### 9.8 Restrict /proc visibility (PARANOID)
Add to `/etc/fstab`: `proc /proc proc defaults,hidepid=2,gid=adm 0 0`

### 9.9 UMASK hardening (ENHANCED+)
Set `umask 0077` in `/etc/profile` and `/etc/bash.bashrc`

### 9.10 Restrict compiler access (ENHANCED+)
```bash
chmod 700 /usr/bin/gcc* /usr/bin/g++* /usr/bin/cc* /usr/bin/make 2>/dev/null
```

---

## PHASE 10: Systemd Service Hardening (ENHANCED+)

For each running service detected in Phase 0, analyze and harden using systemd security directives.

### 10.1 Audit current exposure
```bash
for svc in $(systemctl list-units --type=service --state=running --no-legend | awk '{print $1}'); do
  echo "=== $svc ==="
  systemd-analyze security "$svc" 2>/dev/null | tail -1
done
```

### 10.2 Create override files for exposed services
For services with exposure > 5.0, create `/etc/systemd/system/<service>.d/hardening.conf`:

```ini
[Service]
# Filesystem isolation
ProtectSystem=strict
ProtectHome=true
PrivateTmp=yes
PrivateDevices=yes
ProtectKernelModules=yes
ProtectKernelTunables=yes
ProtectControlGroups=yes
ProtectKernelLogs=yes
ProtectHostname=yes
ProtectClock=yes

# Privilege restriction
NoNewPrivileges=yes
RestrictSUIDSGID=yes
LockPersonality=yes

# Memory protection
MemoryDenyWriteExecute=yes

# Namespace restriction
RestrictNamespaces=yes
RestrictRealtime=yes

# Capability restriction (adapt per service)
CapabilityBoundingSet=~CAP_SYS_ADMIN CAP_SYS_PTRACE CAP_NET_ADMIN

# Network restriction (if no network needed)
# PrivateNetwork=yes
# IPAddressDeny=any

# Syscall filtering
SystemCallArchitectures=native
```

**IMPORTANT**: Test each service after hardening. Roll back if the service fails.

```bash
systemctl daemon-reload
systemctl restart <service>
systemctl status <service>  # Verify it's running
```

---

## PHASE 11: Web Server Hardening (if detected)

### 11.1 Nginx
1. `server_tokens off;`
2. Remove TLSv1/1.1, keep only TLSv1.2+
3. Strong ciphers (ECDHE + CHACHA20/AES-GCM only)
4. Security headers from `${CLAUDE_SKILL_DIR}/templates/nginx_security_headers.conf`
5. Test with `nginx -t` and reload
6. If domain exists, offer Let's Encrypt setup

### 11.2 Apache (if detected)
1. `ServerTokens Prod` and `ServerSignature Off`
2. Disable directory listing: `Options -Indexes`
3. Same headers and TLS config as Nginx
4. Disable unnecessary modules: `a2dismod status info`

### 11.3 Application-specific (if detected)
- **PHP**: `expose_php = Off`, `display_errors = Off`, `session.cookie_secure = 1`, `session.cookie_httponly = 1`
- **Node.js**: Recommend helmet.js, check for outdated npm packages
- **Database**: Ensure not listening on 0.0.0.0, require authentication

---

## PHASE 12: Advanced Hardening (PARANOID only)

### 12.1 Boot security
- GRUB password: `grub-mkpasswd-pbkdf2` and configure in `/etc/grub.d/40_custom`
- Kernel boot parameters: add `slab_nomerge init_on_alloc=1 init_on_free=1 page_alloc.shuffle=1 pti=on randomize_kstack_offset=on vsyscall=none debugfs=off lockdown=confidentiality module.sig_enforce=1`

### 12.2 Mount hardening
Add `noexec,nosuid,nodev` to `/tmp`, `/var/tmp`, `/dev/shm` in `/etc/fstab`

### 12.3 USB protection
```bash
echo "install usb-storage /bin/false" >> /etc/modprobe.d/hardening.conf
```

### 12.4 Restrict /boot and kernel info
```bash
chmod 700 /boot
chmod 700 /usr/src 2>/dev/null
rm -f /boot/System.map-* 2>/dev/null
```

### 12.5 PAM advanced hardening
- Add `pam_faildelay.so delay=4000000` for 4-second login delay
- Increase shadow hashing rounds: `SHA_CRYPT_MIN_ROUNDS 65536` in login.defs

### 12.6 Kernel lockdown
If `lockdown=confidentiality` is not already in boot params, recommend it.

---

## PHASE 13: Automated Scans (STANDARD+)

Create `/etc/cron.d/security-scans` with scanning schedule:
- ClamAV: weekly (Sunday 2 AM)
- rkhunter: daily (3 AM)
- chkrootkit: weekly (Monday 3:30 AM)
- Lynis: monthly (1st, 4 AM)
- AIDE: daily (5 AM)
- Security updates check: daily (6 AM)
- Logwatch: daily (7 AM)

Create log directories: `/var/log/aide`, `/var/log/logwatch`, `/var/log/clamav`

---

## PHASE 14: Run ALL Security Scans (ALL LEVELS)

Run in parallel:
1. **Lynis**: `lynis audit system --cronjob`
2. **rkhunter**: `rkhunter --check --skip-keypress --report-warnings-only`
3. **chkrootkit**: `chkrootkit`
4. **ClamAV**: `clamscan -r /etc /usr/bin /usr/sbin /usr/local/bin /root /home /tmp --infected --quiet`
5. **Nmap**: `nmap -sV -sS -O --top-ports 1000 localhost`
6. **Nikto**: `nikto -h http://localhost -C all -nointeractive` (if web server)
7. **debsums**: `debsums -s`
8. **John the Ripper**: Quick password audit
9. **systemd-analyze security**: All services exposure (ENHANCED+)
10. **SUID/SGID/World-writable/Unowned file audit**
11. **Network audit**: listening ports + established connections

Wait for ALL scans to complete.

---

## PHASE 15: Generate Comprehensive Security Report

Generate a structured report:

```markdown
# RAPPORT DE SECURITE - [HOSTNAME]
**Date**: [DATE] | **OS**: [OS] | **Kernel**: [KERNEL]
**Niveau de hardening**: [LEVEL] | **Reference**: CIS Benchmark + NIST 800-123 + ANSSI BP-028

## Score Global
| Metrique | Valeur |
|----------|--------|
| Lynis Hardening Index | XX/100 |
| Services securises (systemd) | X/Y |
| Regles audit actives | XX |
| Jails fail2ban | XX |

## 1. LYNIS - Audit Global
## 2. CLAMAV - Antivirus
## 3. RKHUNTER + CHKROOTKIT - Rootkits
## 4. NMAP - Ports ouverts
## 5. NIKTO - Vulnerabilites web
## 6. DEBSUMS - Integrite paquets
## 7. JOHN - Audit mots de passe
## 8. SYSTEMD - Exposition services (ENHANCED+)
## 9. Audit reseau (ports, connexions)
## 10. Audit fichiers (SUID, world-writable, unowned)

## CONFORMITE
| Standard | Couverture estimee |
|----------|-------------------|
| CIS Benchmark L1 | XX% |
| NIST 800-123 | XX% |
| ANSSI BP-028 [level] | XX% |

## ACTIONS RECOMMANDEES (prioritisees)
1. [CRITIQUE] ...
2. [IMPORTANT] ...
3. [RECOMMANDE] ...
```

---

## PHASE 16: Post-Hardening Health Verification (ALL LEVELS)

After ALL hardening is complete, verify nothing is broken:

```bash
echo "=== HEALTH CHECK ==="

# 1. SSH still accessible
echo -n "SSH: "; systemctl is-active ssh && echo "OK" || echo "BROKEN"

# 2. Web server (if was running before)
echo -n "Nginx: "; systemctl is-active nginx 2>/dev/null && echo "OK" || echo "N/A"
echo -n "Apache: "; systemctl is-active apache2 2>/dev/null && echo "OK" || echo "N/A"

# 3. Docker (if was running before)
echo -n "Docker: "; docker ps &>/dev/null && echo "OK" || echo "N/A"

# 4. DNS resolution
echo -n "DNS: "; host google.com &>/dev/null && echo "OK" || echo "BROKEN"

# 5. Firewall active
echo -n "Firewall: "; ufw status | grep -q "active" && echo "OK" || echo "BROKEN"

# 6. Fail2ban running
echo -n "Fail2ban: "; fail2ban-client status &>/dev/null && echo "OK" || echo "BROKEN"

# 7. Auditd running
echo -n "Auditd: "; systemctl is-active auditd && echo "OK" || echo "N/A"

# 8. All services from Phase 0 still running
# (compare against the list captured in Phase 0)
```

If ANY critical service is broken, investigate and fix immediately. Report status to user.

---

## Troubleshooting

### Common Issues and Fixes

| Problem | Cause | Fix |
|---------|-------|-----|
| SSH connection refused | SSH config error | `sshd -t` then fix config, `systemctl restart ssh` |
| Website down after hardening | UFW blocking port | `ufw allow 80/tcp && ufw allow 443/tcp` |
| Docker containers can't reach internet | ip_forward disabled | `sysctl net.ipv4.ip_forward=1` |
| Browser crashes (desktop) | /dev/shm noexec | Remount without noexec: `mount -o remount,exec /dev/shm` |
| Database unreachable | Firewall blocking localhost | `ufw allow from 127.0.0.1` |
| Service won't start after systemd hardening | Too restrictive sandboxing | Remove override: `rm /etc/systemd/system/<svc>.d/hardening.conf && systemctl daemon-reload` |
| Can't install packages | Audit rules immutable | Reboot to clear immutable audit rules, or `auditctl -e 0` |
| Fail2ban not banning | Wrong log path in jail | Check `fail2ban-client status <jail>` and fix logpath |
| NTP not syncing | Firewall blocking UDP 123 | `ufw allow out 123/udp` |

### Emergency Recovery
If you're locked out or something is critically broken:
1. Access via console (not SSH) if available
2. Boot into recovery/single-user mode
3. Restore backups from `/etc/*.backup.*` files
4. Disable UFW: `ufw disable`
5. Restart SSH: `systemctl restart ssh`

---

## Quick Reference

### Files Modified by This Skill

| File | Purpose | Backed Up |
|------|---------|-----------|
| `/etc/ssh/sshd_config.d/hardening.conf` | SSH hardening | Yes |
| `/etc/sysctl.d/99-security-hardening.conf` | Kernel params | New file |
| `/etc/fail2ban/jail.local` | Fail2ban jails | New file |
| `/etc/audit/rules.d/hardening.rules` | Audit rules | New file |
| `/etc/modprobe.d/hardening.conf` | Disabled modules | New file |
| `/etc/security/pwquality.conf` | Password policy | Yes |
| `/etc/security/limits.d/hardening.conf` | Core dumps | New file |
| `/etc/login.defs` | Login policy | Yes |
| `/etc/issue.net`, `/etc/issue` | Warning banners | Yes |
| `/etc/nginx/conf.d/security-headers.conf` | Web headers | New file |
| `/etc/apt/apt.conf.d/50unattended-upgrades` | Auto-updates | Yes |
| `/etc/cron.d/security-scans` | Scan schedule | New file |
| `/etc/sudoers.d/hardening` | Sudo policy | New file |

### Services Enabled by This Skill

| Service | Purpose |
|---------|---------|
| `fail2ban` | Brute-force protection |
| `auditd` | System audit logging |
| `clamav-daemon` | Antivirus |
| `clamav-freshclam` | Virus DB updates |
| `psad` | Port scan detection |
| `acct` | Process accounting |
| `sysstat` | System statistics |
| `ufw` | Firewall |
| `apparmor` | Mandatory access control |

---

## Safety Rules (NON-NEGOTIABLE)

1. **ALWAYS** run Phase 0 (reconnaissance) FIRST — understand before acting
2. **ALWAYS** ask the user about detected services before Phase 5 (firewall)
3. **NEVER** lock out SSH access
4. **NEVER** disable a service without asking the user
5. **ALWAYS** backup configs before modifying: `cp file file.backup.$(date +%Y%m%d)`
6. **ALWAYS** validate configs before reloading: `sshd -t`, `nginx -t`, `visudo -c`, etc.
7. **ALWAYS** test services after systemd hardening — roll back if broken
8. If Docker is running: preserve `ip_forward`, don't break Docker networking
9. If a database is running: don't block its port on localhost
10. If browsers are detected (desktop): don't add `noexec` to `/dev/shm`
11. Use `DEBIAN_FRONTEND=noninteractive` for all apt commands
12. Run long scans (AIDE, ClamAV) in background
13. Use TaskCreate/TaskUpdate to track progress
14. Report to the user at each phase completion
15. If any phase fails, log the error and continue to the next phase — never abort entirely
16. **ALWAYS** run Phase 16 (health verification) after hardening to confirm nothing is broken
