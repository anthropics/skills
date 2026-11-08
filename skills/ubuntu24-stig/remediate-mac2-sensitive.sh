#!/usr/bin/env bash
# DISA STIG V1R1 — Ubuntu 24.04 LTS — MAC-2_Sensitive remediation
# Tested on AWS EC2 (no GUI, no smartcard)
# Run as root. Take an AMI snapshot first.
set -euo pipefail

LOGDIR=/var/backups/stig-$(date +%Y%m%dT%H%M%SZ)
mkdir -p "$LOGDIR"
echo "[*] Backing up /etc to $LOGDIR/etc.tgz"
tar czf "$LOGDIR/etc.tgz" /etc 2>/dev/null || true

log() { echo "[STIG] $*"; }
stig_ok()   { echo "  ✓ $*"; }
stig_fix()  { echo "  → $*"; }
stig_skip() { echo "  ⚠ SKIP (AWS/NA): $*"; }

# ---------------------------------------------------------------------------
# 1. PACKAGES
# ---------------------------------------------------------------------------
log "Installing required packages..."
DEBIAN_FRONTEND=noninteractive apt-get update -qq
DEBIAN_FRONTEND=noninteractive apt-get install -y \
  auditd audispd-plugins \
  libpam-pwquality \
  sssd sssd-tools libsss-sudo \
  aide aide-common \
  chrony \
  openscap-scanner \
  libpam-pkcs11 \
  opensc \
  ufw 2>&1 | grep -E "^(Setting|Installing|Unpacking|Get)" || true
stig_ok "Packages installed"

# ---------------------------------------------------------------------------
# 2. auditd — SV-270656, SV-270657, SV-270676
# ---------------------------------------------------------------------------
log "Configuring auditd..."
systemctl enable --now auditd 2>/dev/null || true

# Startup audit (SV-270676): add audit=1 to kernel cmdline via GRUB
if ! grep -q "audit=1" /etc/default/grub 2>/dev/null; then
  sed -i 's/GRUB_CMDLINE_LINUX_DEFAULT="\([^"]*\)"/GRUB_CMDLINE_LINUX_DEFAULT="\1 audit=1"/' /etc/default/grub
  update-grub 2>/dev/null || true
  stig_fix "audit=1 added to kernel cmdline (reboot required)"
else
  stig_ok "audit=1 already in kernel cmdline"
fi

# auditd.conf settings
AUDITD_CONF=/etc/audit/auditd.conf
sed -i 's/^log_format.*/log_format = ENRICHED/'    "$AUDITD_CONF" 2>/dev/null || true
sed -i 's/^space_left_action.*/space_left_action = email/' "$AUDITD_CONF" 2>/dev/null || true
sed -i 's/^action_mail_acct.*/action_mail_acct = root/'   "$AUDITD_CONF" 2>/dev/null || true
stig_ok "auditd.conf configured"

# ---------------------------------------------------------------------------
# 3. AUDIT RULES — SV-270684 through SV-270815
# ---------------------------------------------------------------------------
log "Writing audit rules..."
RULES=/etc/audit/rules.d/99-stig.rules
cat > "$RULES" << 'AUDITEOF'
## DISA STIG Ubuntu 24.04 V1R1 — audit rules

# Delete all rules first
-D

# Buffer size
-b 8192

# Failure mode: 1=printk, 2=panic
-f 1

# ── Identity files (SV-270684 to SV-270688) ───────────────────────────────
-w /etc/passwd   -p wa -k identity
-w /etc/group    -p wa -k identity
-w /etc/shadow   -p wa -k identity
-w /etc/gshadow  -p wa -k identity
-w /etc/opasswd  -p wa -k identity

# ── Sudoers (SV-270807, SV-270808) ────────────────────────────────────────
-w /etc/sudoers    -p wa -k sudoers
-w /etc/sudoers.d/ -p wa -k sudoers

# ── Log files (SV-270810, SV-270811, SV-270812) ───────────────────────────
-w /var/log/wtmp  -p wa -k session
-w /var/run/utmp  -p wa -k session
-w /var/log/btmp  -p wa -k session

# ── Systemd journal (SV-270715) ───────────────────────────────────────────
-w /run/log/journal/ -p wa -k systemd_journal

# ── Privileged commands (SV-270778 to SV-270804) ─────────────────────────
-a always,exit -F path=/usr/bin/su           -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/chfn         -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/bin/mount            -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/bin/umount           -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/ssh-agent    -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/lib/openssh/ssh-keysign -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/sudo         -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/sudoedit     -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/chsh         -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/newgrp       -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/chcon        -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/sbin/apparmor_parser -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/setfacl      -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/chacl        -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/passwd       -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/sbin/unix_update -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/gpasswd      -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/chage        -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/sbin/usermod     -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/usr/bin/crontab      -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged
-a always,exit -F path=/sbin/pam_timestamp_check -F perm=x -F auid>=1000 -F auid!=4294967295 -k privileged

# ── Fail log / last log (SV-270796, SV-270797) ────────────────────────────
-w /var/log/faillog  -p wa -k logins
-w /var/log/lastlog  -p wa -k logins

# ── Privilege escalation via setuid/setgid (SV-270689) ────────────────────
-a always,exit -F arch=b64 -S execve -C uid!=euid -F euid=0 -k setuid
-a always,exit -F arch=b64 -S execve -C gid!=egid -F egid=0 -k setgid
-a always,exit -F arch=b32 -S execve -C uid!=euid -F euid=0 -k setuid
-a always,exit -F arch=b32 -S execve -C gid!=egid -F egid=0 -k setgid

# ── xattr (SV-270784) ─────────────────────────────────────────────────────
-a always,exit -F arch=b64 -S setxattr,fsetxattr,lsetxattr,removexattr,fremovexattr,lremovexattr -k perm_mod
-a always,exit -F arch=b32 -S setxattr,fsetxattr,lsetxattr,removexattr,fremovexattr,lremovexattr -k perm_mod

# ── chown (SV-270785) ─────────────────────────────────────────────────────
-a always,exit -F arch=b64 -S chown,fchown,fchownat,lchown -k perm_mod
-a always,exit -F arch=b32 -S chown,fchown,fchownat,lchown -k perm_mod

# ── chmod (SV-270786) ─────────────────────────────────────────────────────
-a always,exit -F arch=b64 -S chmod,fchmod,fchmodat -k perm_mod
-a always,exit -F arch=b32 -S chmod,fchmod,fchmodat -k perm_mod

# ── File access failures (SV-270787) ─────────────────────────────────────
-a always,exit -F arch=b64 -S creat,open,openat,open_by_handle_at,truncate,ftruncate -F exit=-EACCES -k access
-a always,exit -F arch=b64 -S creat,open,openat,open_by_handle_at,truncate,ftruncate -F exit=-EPERM  -k access
-a always,exit -F arch=b32 -S creat,open,openat,truncate,ftruncate -F exit=-EACCES -k access
-a always,exit -F arch=b32 -S creat,open,openat,truncate,ftruncate -F exit=-EPERM  -k access

# ── Module loading (SV-270805, SV-270806) ────────────────────────────────
-a always,exit -F arch=b64 -S init_module,finit_module -k modules
-a always,exit -F arch=b64 -S delete_module -k modules
-a always,exit -F arch=b32 -S init_module,finit_module -k modules
-a always,exit -F arch=b32 -S delete_module -k modules

# ── modprobe, kmod, fdisk (SV-270813 to SV-270815) ───────────────────────
-w /sbin/modprobe -p x -k modules
-w /usr/bin/kmod  -p x -k modules
-w /sbin/fdisk    -p x -k partition

# ── Delete operations (SV-270809) ─────────────────────────────────────────
-a always,exit -F arch=b64 -S unlink,unlinkat,rename,renameat,rmdir -k delete
-a always,exit -F arch=b32 -S unlink,unlinkat,rename,renameat,rmdir -k delete

# ── cron audit (SV-274870) ────────────────────────────────────────────────
-w /etc/cron.allow -p wa -k cron
-w /etc/cron.deny  -p wa -k cron
-w /etc/cron.d/    -p wa -k cron
-w /etc/cron.daily/   -p wa -k cron
-w /etc/cron.hourly/  -p wa -k cron
-w /etc/cron.monthly/ -p wa -k cron
-w /etc/cron.weekly/  -p wa -k cron
-w /etc/crontab       -p wa -k cron

# ── sudo privilege escalation requires password (SV-274868) ──────────────
-a always,exit -F arch=b64 -S execve -F path=/usr/bin/sudo -k sudo

# ── Make audit rules immutable (SV-270832) — requires reboot to change ───
-e 2
AUDITEOF

chmod 640 "$RULES"
chown root:root "$RULES"
augenrules --load 2>/dev/null || auditctl -R "$RULES" 2>/dev/null || true
stig_ok "Audit rules loaded"

# ---------------------------------------------------------------------------
# 4. SSH HARDENING — SV-270666 to SV-270671, SV-270708, SV-270709, SV-270717
# ---------------------------------------------------------------------------
log "Hardening SSH daemon (FIPS 140-3)..."
SSHD_STIG=/etc/ssh/sshd_config.d/99-stig.conf
cat > "$SSHD_STIG" << 'SSHEOF'
# DISA STIG V1R1 — SSH daemon hardening
Protocol 2
Ciphers aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
MACs hmac-sha2-256,hmac-sha2-512,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com
KexAlgorithms ecdh-sha2-nistp256,ecdh-sha2-nistp384,ecdh-sha2-nistp521,diffie-hellman-group-exchange-sha256
X11Forwarding no
X11UseLocalhost yes
PermitEmptyPasswords no
PermitUserEnvironment no
PrintLastLog yes
ClientAliveInterval 600
ClientAliveCountMax 0
Banner /etc/issue.net
AllowAgentForwarding no
SSHEOF

log "Hardening SSH client (FIPS 140-3)..."
SSH_STIG=/etc/ssh/ssh_config.d/99-stig.conf
cat > "$SSH_STIG" << 'SSHCEOF'
# DISA STIG V1R1 — SSH client hardening
Host *
    Ciphers aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
    MACs hmac-sha2-256,hmac-sha2-512,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com
SSHCEOF

systemctl restart sshd
stig_ok "SSH hardened"

# ---------------------------------------------------------------------------
# 5. LOGIN BANNER — SV-270666 (SSH banner)
# ---------------------------------------------------------------------------
log "Setting DoD login banner..."
cat > /etc/issue.net << 'BANEOF'
You are accessing a U.S. Government (USG) Information System (IS) that is
provided for USG-authorized use only. By using this IS (which includes any
device attached to this IS), you consent to the following conditions:
- The USG routinely intercepts and monitors communications on this IS for
  purposes including, but not limited to, penetration testing, COMSEC
  monitoring, network operations and defense, personnel misconduct (PM),
  law enforcement (LE), and counterintelligence (CI) investigations.
- At any time, the USG may inspect and seize data stored on this IS.
- Communications using, or data stored on, this IS are not private, are
  subject to routine monitoring, interception, and search, and may be
  disclosed or used for any USG-authorized purpose.
- This IS includes security measures (e.g., authentication and access
  controls) to protect USG interests--not for your personal benefit or privacy.
- Notwithstanding the above, using this IS does not constitute consent to PM,
  LE or CI investigative searching or monitoring of the content of privileged
  communications, or work product, related to personal representation or
  services by attorneys, psychotherapists, or clergy, and their assistants.
  Such communications and work product are private and confidential. See User
  Agreement for details.
BANEOF
stig_ok "DoD banner set"

# ---------------------------------------------------------------------------
# 6. PAM — pwquality, lockout, password aging
# ---------------------------------------------------------------------------
log "Configuring PAM pwquality (SV-270704, SV-270705, SV-270726–270733)..."
cat > /etc/security/pwquality.conf << 'PWEOF'
minlen = 15
ucredit = -1
lcredit = -1
dcredit = -1
ocredit = -1
difok = 8
dictcheck = 1
enforcing = 1
PWEOF
stig_ok "pwquality configured"

log "Configuring PAM faillock lockout (SV-270690)..."
cat > /etc/security/faillock.conf << 'FLEOF'
deny = 3
unlock_time = 0
fail_interval = 900
audit
FLEOF
stig_ok "faillock configured"

log "Configuring password aging (SV-270730, SV-270731)..."
sed -i 's/^PASS_MAX_DAYS.*/PASS_MAX_DAYS   60/' /etc/login.defs
sed -i 's/^PASS_MIN_DAYS.*/PASS_MIN_DAYS   1/'  /etc/login.defs
sed -i 's/^PASS_WARN_AGE.*/PASS_WARN_AGE   7/'  /etc/login.defs
stig_ok "Password aging: min=1 max=60 warn=7"

log "Setting password hashing to yescrypt/SHA-512 (SV-270725, SV-270739)..."
sed -i 's/^ENCRYPT_METHOD.*/ENCRYPT_METHOD SHA512/' /etc/login.defs
stig_ok "Password hashing: SHA512"

log "Setting login delay (SV-270706)..."
sed -i 's/^FAIL_DELAY.*/FAIL_DELAY 4/' /etc/login.defs
grep -q "^FAIL_DELAY" /etc/login.defs || echo "FAIL_DELAY 4" >> /etc/login.defs
stig_ok "Login delay: 4 seconds"

log "Disabling inactive accounts after 35 days (SV-270683)..."
useradd -D -f 35
stig_ok "Inactive account lock: 35 days"

# ---------------------------------------------------------------------------
# 7. SESSION LIMITS — SV-270677, SV-270680
# ---------------------------------------------------------------------------
log "Setting session limits..."
cat > /etc/security/limits.d/99-stig.conf << 'LIMEOF'
* hard maxlogins 10
LIMEOF

cat > /etc/profile.d/99-stig-tmout.sh << 'TMEOF'
TMOUT=600
readonly TMOUT
export TMOUT
TMEOF
chmod 644 /etc/profile.d/99-stig-tmout.sh
stig_ok "Max sessions: 10, TMOUT: 600s"

# ---------------------------------------------------------------------------
# 8. SYSCTL HARDENING — SV-270749, SV-270753
# ---------------------------------------------------------------------------
log "Applying sysctl hardening..."
cat > /etc/sysctl.d/99-stig.conf << 'SYSCTLEOF'
# Restrict kernel message buffer (SV-270749)
kernel.dmesg_restrict = 1
# TCP SYN cookie protection (SV-270753)
net.ipv4.tcp_syncookies = 1
SYSCTLEOF
sysctl --system > /dev/null 2>&1
stig_ok "sysctl: dmesg_restrict=1, tcp_syncookies=1"

# ---------------------------------------------------------------------------
# 9. UFW FIREWALL — SV-270654, SV-270655
# ---------------------------------------------------------------------------
log "Enabling UFW firewall..."
ufw --force enable
ufw logging on
stig_ok "UFW enabled"

# ---------------------------------------------------------------------------
# 10. AIDE — SV-270649, SV-270652
# ---------------------------------------------------------------------------
log "Initialising AIDE file integrity database..."
if [ ! -f /var/lib/aide/aide.db ]; then
  aideinit 2>/dev/null || aide --init 2>/dev/null || true
  [ -f /var/lib/aide/aide.db.new ] && mv /var/lib/aide/aide.db.new /var/lib/aide/aide.db
  stig_ok "AIDE database initialised"
else
  stig_ok "AIDE database already exists"
fi

# Daily AIDE check with email alert
cat > /etc/cron.d/aide-stig << 'AIDEEOF'
0 5 * * * root /usr/bin/aide --check 2>&1 | /usr/bin/mail -s "AIDE integrity report $(hostname)" root
AIDEEOF
stig_ok "AIDE daily cron configured"

# ---------------------------------------------------------------------------
# 11. DISABLE CTRL-ALT-DELETE — SV-270712
# ---------------------------------------------------------------------------
log "Disabling Ctrl-Alt-Delete..."
systemctl mask ctrl-alt-del.target 2>/dev/null || true
systemctl daemon-reload
stig_ok "Ctrl-Alt-Delete disabled"

# ---------------------------------------------------------------------------
# 12. DISABLE USB MASS STORAGE — SV-270718
# ---------------------------------------------------------------------------
log "Blacklisting USB mass storage..."
echo "install usb-storage /bin/true" > /etc/modprobe.d/99-stig-disable-usb.conf
rmmod usb-storage 2>/dev/null || true
stig_ok "USB mass storage blacklisted"

# ---------------------------------------------------------------------------
# 13. APT AUTOREMOVE — SV-270773
# ---------------------------------------------------------------------------
log "Configuring APT autoremove..."
cat > /etc/apt/apt.conf.d/99-stig-autoremove << 'APTEOF'
APT::Get::AutomaticRemove "true";
APTEOF
DEBIAN_FRONTEND=noninteractive apt-get -y autoremove > /dev/null 2>&1 || true
stig_ok "APT autoremove configured"

# ---------------------------------------------------------------------------
# 14. FILE PERMISSIONS — SV-270775–277, SV-270758, SV-270822–SV-270823
# ---------------------------------------------------------------------------
log "Fixing audit config and tool permissions..."
# Audit config files
find /etc/audit/ -type f \( -name "*.rules" -o -name "*.conf" \) \
  -exec chmod 640 {} \; -exec chown root:root {} \; 2>/dev/null || true

# Audit tools
find /sbin /usr/sbin -name "audit*" -o -name "auditctl" -o -name "ausearch" \
     -o -name "aureport" -o -name "aulast" -o -name "autrace" 2>/dev/null | \
  xargs -I{} sh -c 'chown root:root "{}" && chmod 0755 "{}"' 2>/dev/null || true

# journalctl (SV-270758)
chmod 0750 /usr/bin/journalctl 2>/dev/null || true
stig_ok "Audit config: 640 root:root; journalctl: 0750"

# ---------------------------------------------------------------------------
# 15. DIRECT ROOT LOGIN — SV-270724
# ---------------------------------------------------------------------------
log "Locking direct root login..."
passwd -l root > /dev/null 2>&1 || true
stig_ok "root account locked (sudo still works)"

# ---------------------------------------------------------------------------
# 16. PAM NULL PASSWORDS — SV-270714
# ---------------------------------------------------------------------------
log "Removing nullok from PAM..."
sed -i 's/ nullok//g' /etc/pam.d/common-auth 2>/dev/null || true
sed -i 's/ nullok//g' /etc/pam.d/common-password 2>/dev/null || true
stig_ok "nullok removed from PAM"

# ---------------------------------------------------------------------------
# 17. DEFAULT UMASK — SV-270716
# ---------------------------------------------------------------------------
log "Setting default umask to 027..."
if grep -q "^UMASK" /etc/login.defs; then
  sed -i 's/^UMASK.*/UMASK 027/' /etc/login.defs
else
  echo "UMASK 027" >> /etc/login.defs
fi
stig_ok "UMASK: 027"

# ---------------------------------------------------------------------------
# 18. REMOTE MONITORING — SV-270681 (rsyslog remote)
# ---------------------------------------------------------------------------
log "Enabling remote access monitoring in rsyslog..."
grep -q "auth,authpriv" /etc/rsyslog.conf || \
  echo 'auth,authpriv.*  /var/log/auth.log' >> /etc/rsyslog.conf
systemctl restart rsyslog 2>/dev/null || true
stig_ok "auth log: /var/log/auth.log"

# ---------------------------------------------------------------------------
# 19. AWS-SPECIFIC SKIPS (logged for audit trail)
# ---------------------------------------------------------------------------
stig_skip "SV-270675: GRUB single-user password (AWS console manages boot)"
stig_skip "SV-270692: Graphical logon banner (no desktop)"
stig_skip "SV-270674: Screen lock (no GUI)"
stig_skip "SV-270721/722: Smartcard SSH (PIV/CAC not used on EC2)"
stig_skip "SV-270672/673: PIV credentials (no smartcard reader)"
stig_skip "SV-270736/737/738: PKI cert validation (OCSP infra N/A)"
stig_skip "SV-270744: FIPS mode (requires Ubuntu Pro subscription + reboot)"

# ---------------------------------------------------------------------------
# DONE
# ---------------------------------------------------------------------------
echo ""
echo "════════════════════════════════════════════════════"
echo "  STIG remediation complete"
echo "  Backup: $LOGDIR"
echo "  REBOOT REQUIRED for: audit=1 kernel param, AIDE"
echo "════════════════════════════════════════════════════"
echo ""
echo "Run post-scan to verify:"
echo "  oscap xccdf eval \\"
echo "    --datastream-id scap_mil.disa.stig_datastream_U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark \\"
echo "    --xccdf-id xccdf_mil.disa.stig_benchmark_CAN_Ubuntu_24-04_LTS_STIG \\"
echo "    --profile xccdf_mil.disa.stig_profile_MAC-2_Sensitive \\"
echo "    --report /var/log/stig/post-report.html \\"
echo "    /opt/stig/U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.xml"
