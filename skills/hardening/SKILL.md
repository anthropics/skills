---
name: hardening
description: "Automated Linux server security hardening based on CIS Benchmarks, NIST SP 800-123, and ANSSI BP-028. Use when the user wants to harden, secure, or audit a Linux server. Smart service discovery to avoid disruption. 4 levels: minimal, standard, enhanced, paranoid. Installs 35+ open-source security tools, hardens SSH/kernel/firewall/systemd/permissions, runs all scans, and generates a compliance report."
user-invocable: true
disable-model-invocation: true
allowed-tools: Bash, Read, Write, Edit, Grep, Glob, Agent, TaskCreate, TaskUpdate
argument-hint: "[minimal|standard|enhanced|paranoid|scan-only|report]"
---

# Linux Server Security Hardening

Automated, non-disruptive Linux server hardening based on industry standards.

## Arguments

- `minimal` — Essential baseline (firewall, SSH, passwords). ~5 min. Low risk.
- `standard` (default) — Full hardening with 35+ tools. ~15 min. Balanced.
- `enhanced` — Aggressive: systemd sandboxing, advanced kernel params. ~25 min.
- `paranoid` — Maximum lockdown: kernel lockdown, restricted /proc, GRUB password. ~35 min.
- `scan-only` — Run all security scans, generate report. No changes.
- `report` — Status report of current security posture. No changes.

---

## Phase 0: Smart Reconnaissance (ALL LEVELS)

**NEVER skip this phase.** Before making ANY changes:

```bash
# System info
cat /etc/os-release && uname -a && hostname -f && df -h && free -h

# Running services and ports
systemctl list-units --type=service --state=running
ss -tlnp
docker ps 2>/dev/null

# Detect web servers, databases, mail, applications
which nginx apache2 mysql psql mongod redis-server postfix node python3 java php 2>/dev/null

# Desktop vs Server (impacts /dev/shm hardening)
[ -n "$XDG_CURRENT_DESKTOP" ] || systemctl is-active display-manager &>/dev/null && echo "DESKTOP" || echo "SERVER"

# Current security posture
ufw status 2>/dev/null; iptables -L -n 2>/dev/null
sshd -T 2>/dev/null | grep -E "permitrootlogin|passwordauth|x11forwarding"
which fail2ban-client lynis rkhunter clamdscan auditctl 2>/dev/null
aa-status 2>/dev/null
```

**Present findings and ASK the user** before proceeding:
- List detected services and their ports
- Ask: "Any services I should NOT touch? Any extra ports to allow?"
- Wait for response before Phase 1

---

## Phase 1: System Update (ALL)

```bash
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq && apt-get upgrade -y -qq
```

---

## Phase 2: Install Security Tools

**Minimal:**
```bash
apt-get install -y -qq fail2ban ufw unattended-upgrades libpam-pwquality needrestart debsums
```

**Standard** (adds to minimal):
```bash
apt-get install -y -qq auditd audispd-plugins rkhunter chkrootkit lynis \
  clamav clamav-daemon clamav-freshclam aide \
  apparmor apparmor-utils apparmor-profiles apparmor-profiles-extra \
  libpam-tmpdir acct sysstat net-tools arpwatch logwatch psad firejail \
  nmap nikto john tcpdump tshark htop certbot gnupg2 \
  apt-transport-https ca-certificates curl
```

**Enhanced** (adds): `openscap-scanner scap-security-guide`
**Paranoid** (adds): `libseccomp-dev seccomp bpftool`

Skip any package that fails — never abort.

---

## Phase 3: SSH Hardening (ALL)

1. Backup: `cp /etc/ssh/sshd_config /etc/ssh/sshd_config.backup.$(date +%Y%m%d)`
2. Create `/etc/ssh/sshd_config.d/hardening.conf`:

```
Protocol 2
PermitRootLogin prohibit-password
MaxAuthTries 3
MaxSessions 3
LoginGraceTime 30
PasswordAuthentication no
PermitEmptyPasswords no
KbdInteractiveAuthentication no
KerberosAuthentication no
GSSAPIAuthentication no
HostbasedAuthentication no
X11Forwarding no
AllowTcpForwarding no
AllowAgentForwarding no
PermitTunnel no
StrictModes yes
IgnoreRhosts yes
UseDNS no
PermitUserEnvironment no
DebianBanner no
SyslogFacility AUTH
LogLevel VERBOSE
ClientAliveInterval 300
ClientAliveCountMax 2
KexAlgorithms sntrup761x25519-sha512@openssh.com,curve25519-sha256@libssh.org,diffie-hellman-group16-sha512,diffie-hellman-group18-sha512
Ciphers chacha20-poly1305@openssh.com,aes256-gcm@openssh.com,aes128-gcm@openssh.com
MACs hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com
Banner /etc/issue.net
```

**Paranoid**: Set `PermitRootLogin no`, `MaxSessions 2`, `LoginGraceTime 20`

3. Create warning banner in `/etc/issue.net`
4. **Validate**: `sshd -t` — MUST pass
5. **Reload**: `systemctl reload ssh`

**NEVER lock out the current SSH session.**

---

## Phase 4: Kernel Hardening (STANDARD+)

Create `/etc/sysctl.d/99-security-hardening.conf`:

```
# Network
net.ipv4.conf.all.accept_source_route = 0
net.ipv4.conf.default.accept_source_route = 0
net.ipv4.conf.all.accept_redirects = 0
net.ipv4.conf.default.accept_redirects = 0
net.ipv4.conf.all.send_redirects = 0
net.ipv4.conf.default.send_redirects = 0
net.ipv4.conf.all.secure_redirects = 0
net.ipv4.tcp_syncookies = 1
net.ipv4.tcp_max_syn_backlog = 2048
net.ipv4.tcp_rfc1337 = 1
net.ipv4.conf.all.log_martians = 1
net.ipv4.icmp_echo_ignore_broadcasts = 1
net.ipv4.icmp_ignore_bogus_error_responses = 1
net.ipv4.conf.all.rp_filter = 1
net.ipv4.conf.default.rp_filter = 1
net.ipv4.tcp_timestamps = 0
net.ipv6.conf.all.accept_redirects = 0
net.ipv6.conf.all.accept_ra = 0
net.ipv6.conf.all.accept_source_route = 0
# Kernel
kernel.dmesg_restrict = 1
kernel.kptr_restrict = 2
kernel.randomize_va_space = 2
kernel.yama.ptrace_scope = 2
kernel.sysrq = 0
kernel.perf_event_paranoid = 3
kernel.unprivileged_bpf_disabled = 1
net.core.bpf_jit_harden = 2
# Filesystem
fs.suid_dumpable = 0
fs.protected_symlinks = 1
fs.protected_hardlinks = 1
fs.protected_fifos = 2
fs.protected_regular = 2
vm.swappiness = 10
vm.mmap_min_addr = 65536
```

**Enhanced** adds: `vm.mmap_rnd_bits=32`, `net.ipv4.tcp_sack=0`, `kernel.kexec_load_disabled=1`, `dev.tty.ldisc_autoload=0`
**Paranoid** adds: `net.ipv4.icmp_echo_ignore_all=1`, `kernel.printk=3 3 3 3`
**Docker running**: Do NOT disable `net.ipv4.ip_forward`

Apply: `sysctl --system`

---

## Phase 5: Firewall (ALL)

```bash
ufw --force reset
ufw default deny incoming
ufw default allow outgoing
ufw limit ssh comment 'SSH rate-limited'
ufw logging medium
# Add rules for services from Phase 0 BEFORE enabling
ufw --force enable
```

**Paranoid**: Default deny outgoing too, whitelist DNS/HTTP/S/NTP.

---

## Phase 6: Fail2ban (ALL)

Create `/etc/fail2ban/jail.local` with SSH jail (all levels) + Nginx jails (if detected) + recidive jail.
Progressive banning: `bantime.increment=true`, `bantime.factor=2`, `bantime.maxtime=604800`.

---

## Phase 7: Auditd (STANDARD+)

Create `/etc/audit/rules.d/hardening.rules` monitoring: passwd/shadow/group, sudoers, SSH config, cron, login/logout, kernel modules, mounts, time changes, privileged commands. Set `-e 2` (immutable).

---

## Phase 8: Security Tools Config (STANDARD+)

- **ClamAV**: `freshclam`, enable daemon + freshclam services
- **AIDE**: `aideinit` (background), copy DB when done
- **rkhunter**: `rkhunter --update && --propupd`
- **PSAD**: Configure hostname, enable auto-IDS
- **NTP**: `timedatectl set-ntp true`
- **Shared memory**: Add `nosuid,nodev` (+ `noexec` if server mode) to `/dev/shm` in fstab
- **Sudo**: Add `use_pty`, logging, `timestamp_timeout=5` to `/etc/sudoers.d/hardening`
- **Remove dangerous packages**: `telnet rsh-client rsh-server xinetd`

---

## Phase 9: File & Permission Hardening (ALL)

```bash
chmod 600 /etc/shadow /etc/gshadow /etc/ssh/sshd_config /etc/crontab
chmod 644 /etc/passwd /etc/group
chmod 700 /etc/ssh/sshd_config.d /etc/cron.d /etc/cron.daily /etc/cron.weekly /root
echo "root" > /etc/cron.allow && echo "root" > /etc/at.allow
```

- Core dumps: `* hard core 0` in limits.d + systemd coredump `Storage=none`
- Password policy: minlen 14, minclass 3, complexity enforced (pwquality.conf)
- login.defs: PASS_MAX_DAYS 90, UMASK 027, SHA_CRYPT_MIN_ROUNDS 10000
- Disable kernel modules: dccp, sctp, rds, tipc, cramfs, freevxfs, jffs2, hfs, hfsplus, udf
- Auto security updates: Configure unattended-upgrades

**Enhanced+**: UMASK 0077, restrict compiler access
**Paranoid**: hidepid=2 on /proc

---

## Phase 10: Systemd Sandboxing (ENHANCED+)

For each service with `systemd-analyze security` exposure > 5.0, create override with: `ProtectSystem=strict`, `ProtectHome=true`, `PrivateTmp=yes`, `PrivateDevices=yes`, `NoNewPrivileges=yes`, `ProtectKernelModules/Tunables/Logs=yes`, `MemoryDenyWriteExecute=yes`, `RestrictNamespaces=yes`, `SystemCallArchitectures=native`.

**Test each service after hardening. Roll back if broken.**

---

## Phase 11: Web Server Hardening (if detected)

- Nginx: `server_tokens off`, TLSv1.2+ only, strong ciphers, security headers (X-Frame-Options, X-Content-Type-Options, HSTS, CSP, Referrer-Policy)
- Apache: `ServerTokens Prod`, `ServerSignature Off`, `Options -Indexes`
- PHP: `expose_php=Off`, `display_errors=Off`, secure session cookies

---

## Phase 12: Advanced Hardening (PARANOID)

- GRUB password with PBKDF2
- Boot params: `slab_nomerge init_on_alloc=1 init_on_free=1 pti=on vsyscall=none debugfs=off lockdown=confidentiality`
- Mount /tmp, /var/tmp, /dev/shm with `noexec,nosuid,nodev`
- USB storage disabled via modprobe

---

## Phase 13: Automated Scans (STANDARD+)

Create cron jobs: ClamAV weekly, rkhunter daily, chkrootkit weekly, Lynis monthly, AIDE daily, security updates daily, Logwatch daily.

---

## Phase 14: Run All Security Scans (ALL)

Run in parallel: Lynis, rkhunter, chkrootkit, ClamAV, Nmap (localhost), Nikto (if web server), debsums, John the Ripper (password audit), SUID/SGID/world-writable file audit, network audit.

---

## Phase 15: Compliance Report (ALL)

Generate structured report with: Lynis score, scan results, open ports, vulnerabilities found, compliance estimation (CIS/NIST/ANSSI), and prioritized action items.

---

## Phase 16: Health Verification (ALL)

Verify SSH, web server, Docker, DNS, firewall, fail2ban, auditd all still working. Report any issues.

---

## Safety Rules

1. ALWAYS run Phase 0 first — understand before acting
2. ALWAYS ask user about services before enabling firewall
3. NEVER lock out SSH access
4. NEVER disable a service without asking
5. ALWAYS backup configs before modifying
6. ALWAYS validate before reloading (sshd -t, nginx -t, visudo -c)
7. ALWAYS test services after systemd hardening — roll back if broken
8. If Docker running: preserve ip_forward
9. If browsers detected (desktop): no noexec on /dev/shm
10. Use DEBIAN_FRONTEND=noninteractive for apt
11. Run long scans in background
12. If a phase fails, log and continue — never abort
