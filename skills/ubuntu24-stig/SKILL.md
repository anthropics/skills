---
name: ubuntu24-stig
description: Apply and audit DISA STIG V1R1 for Ubuntu 24.04 LTS on AWS EC2 — OpenSCAP scanning with the correct benchmark IDs, idempotent shell remediation for MAC-2_Sensitive/Public profiles, auditd rule generation, SSH FIPS 140-3 hardening, PAM lockout and pwquality, AIDE integrity monitoring, and AWS-specific skip logic. Use this skill whenever the user mentions Ubuntu 24.04 STIG hardening, OpenSCAP, SCAP scanning, DISA compliance, auditd rules, FIPS 140-3 on SSH, PAM lockout, AIDE, or any specific STIG rule ID (SV-270xxx) — even if they just say "harden this server" or "failed a compliance scan" in an Ubuntu 24.04 context.
---

# ubuntu24-stig

DISA STIG V1R1 hardening for Ubuntu 24.04 LTS on AWS EC2. Covers OpenSCAP scanning, idempotent shell remediation for MAC-2_Sensitive, and a catalogue of the most common failures with their exact fixes.

## When to use

- Running an OpenSCAP SCAP scan with `U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.xml`
- Applying MAC-2_Sensitive or MAC-2_Public remediation via shell script
- Fixing individual failing STIG rules (auditd, SSH, PAM, AIDE, sysctl)
- Reviewing a scan result and explaining what each `fail` means
- Preparing an AWS EC2 instance for a STIG compliance audit

Do NOT use for:
- Ubuntu 22.04 (different STIG benchmark — use U_CAN_Ubuntu_22-04_LTS V1R2)
- Non-Ubuntu distros (RHEL, Amazon Linux have separate benchmarks)
- Graphical workstation hardening (most GUI rules are `notapplicable` on headless EC2)

---

## Step 1 — Download the STIG benchmark

Official source: **https://public.cyber.mil/stigs/downloads/**  
Search: `Ubuntu 24.04`  
File: `U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.zip`  
Extract: `U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.xml`

Place at: `/opt/stig/U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.xml`

---

## Step 2 — Install OpenSCAP (Ubuntu 24.04 package names)

```bash
apt-get update
apt-get install -y openscap-scanner openscap-common bzip2
```

> **Ubuntu 24.04 package change**: `libopenscap8` was replaced by `libopenscap25t64`. Use `openscap-scanner` — it pulls the correct library automatically. Do NOT install `libopenscap8`.

---

## Step 3 — Correct SCAP benchmark IDs

The IDs in the XML for V1R1 are:

| Parameter | Value |
|-----------|-------|
| `--datastream-id` | `scap_mil.disa.stig_datastream_U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark` |
| `--xccdf-id` | `xccdf_mil.disa.stig_benchmark_CAN_Ubuntu_24-04_LTS_STIG` |
| Profile (MAC-2 Sensitive) | `xccdf_mil.disa.stig_profile_MAC-2_Sensitive` |
| Profile (MAC-2 Public) | `xccdf_mil.disa.stig_profile_MAC-2_Public` |

> **Common error**: Using `xccdf_mil.disa.stig_benchmark_CAN_Ubuntu_24-04_STIG` (missing `_LTS`) causes  
> `Failed to locate a datastream` — always include `_LTS_` in the benchmark ID.

Verify IDs from the file:
```bash
grep -o 'id="[^"]*benchmark[^"]*"' /opt/stig/U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.xml | head -5
```

---

## Step 4 — Run a scan

```bash
BENCHMARK=/opt/stig/U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark.xml
PROFILE=xccdf_mil.disa.stig_profile_MAC-2_Sensitive
OUTDIR=/var/log/stig

mkdir -p "$OUTDIR"

oscap xccdf eval \
  --datastream-id scap_mil.disa.stig_datastream_U_CAN_Ubuntu_24-04_LTS_V1R1_STIG_SCAP_1-3_Benchmark \
  --xccdf-id xccdf_mil.disa.stig_benchmark_CAN_Ubuntu_24-04_LTS_STIG \
  --profile "$PROFILE" \
  --results "$OUTDIR/results.xml" \
  --report  "$OUTDIR/report.html" \
  "$BENCHMARK" || true   # exit code 2 = findings present, not a script error

echo "Report: $OUTDIR/report.html"
```

---

## Step 5 — Remediation script

See `remediate-mac2-sensitive.sh` in this skill directory.  
Run as root on a **snapshot/AMI first** — this changes system configuration.

```bash
chmod +x remediate-mac2-sensitive.sh
sudo ./remediate-mac2-sensitive.sh 2>&1 | tee /var/log/stig-remediation.log
```

---

## AWS EC2 skip list

The following rules are `notapplicable` or impractical on headless EC2 and are skipped by the script:

| Rule | Reason skipped |
|------|---------------|
| SV-270692 (graphical logon banner) | No desktop environment |
| SV-270674 (session lock) | No GUI screen locker |
| SV-270675 (single-user auth / GRUB password) | AWS console manages boot; GRUB lockout breaks recovery |
| SV-270721/722 (smartcard SSH) | PIV/CAC not used on EC2 |
| SV-270672/673 (PIV credentials) | No smartcard reader |
| SV-270736/737/738 (PKI cert path validation) | OCSP infra N/A |

---

## Top failure categories and fixes

### auditd not installed (SV-270656, SV-270657)
```bash
apt-get install -y auditd audispd-plugins
systemctl enable --now auditd
```

### AIDE integrity monitoring (SV-270649, SV-270652)
```bash
apt-get install -y aide aide-common
aideinit
mv /var/lib/aide/aide.db.new /var/lib/aide/aide.db
# Cron check:
echo "0 5 * * * root /usr/bin/aide --check | mail -s 'AIDE report' root" > /etc/cron.d/aide
```

### SSH FIPS 140-3 ciphers (SV-270667 to SV-270671)
```bash
cat >> /etc/ssh/sshd_config.d/99-stig-fips.conf << 'EOF'
Ciphers aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
MACs hmac-sha2-256,hmac-sha2-512,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com
KexAlgorithms ecdh-sha2-nistp256,ecdh-sha2-nistp384,ecdh-sha2-nistp521,diffie-hellman-group-exchange-sha256
X11Forwarding no
X11UseLocalhost yes
PrintLastLog yes
PermitEmptyPasswords no
PermitUserEnvironment no
ClientAliveInterval 600
ClientAliveCountMax 0
EOF
systemctl restart sshd
```

### SSH client FIPS (SV-270670, SV-270671)
```bash
cat >> /etc/ssh/ssh_config.d/99-stig-fips.conf << 'EOF'
Ciphers aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
MACs hmac-sha2-256,hmac-sha2-512,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com
EOF
```

### PAM pwquality (SV-270704, SV-270705, SV-270726–270733)
```bash
apt-get install -y libpam-pwquality
cat > /etc/security/pwquality.conf << 'EOF'
minlen = 15
ucredit = -1
lcredit = -1
dcredit = -1
ocredit = -1
difok = 8
dictcheck = 1
EOF
```

### PAM lockout after 3 attempts (SV-270690)
```bash
cat > /etc/security/faillock.conf << 'EOF'
deny = 3
unlock_time = 0
fail_interval = 900
EOF
```

### Password aging (SV-270730, SV-270731)
```bash
sed -i 's/^PASS_MAX_DAYS.*/PASS_MAX_DAYS   60/' /etc/login.defs
sed -i 's/^PASS_MIN_DAYS.*/PASS_MIN_DAYS   1/'  /etc/login.defs
```

### Concurrent sessions limit (SV-270677)
```bash
echo "* hard maxlogins 10" >> /etc/security/limits.d/99-stig.conf
```

### Session inactivity timeout (SV-270680)
```bash
cat > /etc/profile.d/99-stig-tmout.sh << 'EOF'
TMOUT=600
readonly TMOUT
export TMOUT
EOF
```

### Disable Ctrl-Alt-Delete (SV-270712)
```bash
systemctl mask ctrl-alt-del.target
systemctl daemon-reload
```

### Disable USB mass storage (SV-270718)
```bash
echo "install usb-storage /bin/true" > /etc/modprobe.d/disable-usb-storage.conf
```

### Kernel sysctl hardening (SV-270749, SV-270753)
```bash
cat >> /etc/sysctl.d/99-stig.conf << 'EOF'
kernel.dmesg_restrict = 1
net.ipv4.tcp_syncookies = 1
EOF
sysctl --system
```

### APT autoremove (SV-270773)
```bash
apt-get -y autoremove
echo 'APT::Get::AutomaticRemove "true";' > /etc/apt/apt.conf.d/99autoremove
```

### Audit config file permissions (SV-270775, 270776, 270777)
```bash
chmod 640 /etc/audit/audit.rules /etc/audit/auditd.conf /etc/audit/rules.d/*.rules 2>/dev/null || true
chown root:root /etc/audit/audit.rules /etc/audit/auditd.conf 2>/dev/null || true
```

### journalctl permissions (SV-270758)
```bash
chmod 0750 /usr/bin/journalctl
```

### Direct root login (SV-270724)
```bash
passwd -l root
```

### FIPS mode (SV-270744)
```bash
# CAUTION: on AWS this may break instance connectivity — test on non-production first
apt-get install -y ubuntu-advantage-tools
# ua enable fips-updates  # Requires Ubuntu Pro subscription
```

---

## Audit rules (abridged)

The remediation script generates the full `/etc/audit/rules.d/99-stig.rules`. Key groups:

```bash
# Identity files
-w /etc/passwd  -p wa -k identity
-w /etc/group   -p wa -k identity
-w /etc/shadow  -p wa -k identity
-w /etc/gshadow -p wa -k identity
-w /etc/opasswd -p wa -k identity

# Privilege escalation
-a always,exit -F arch=b64 -S execve -C uid!=euid -F euid=0 -k setuid
-a always,exit -F arch=b64 -S execve -C gid!=egid -F egid=0 -k setgid

# Sudoers
-w /etc/sudoers         -p wa -k sudoers
-w /etc/sudoers.d/      -p wa -k sudoers

# Module loading
-a always,exit -F arch=b64 -S init_module,finit_module -k modules
-a always,exit -F arch=b64 -S delete_module -k modules

# File attribute changes
-a always,exit -F arch=b64 -S setxattr,fsetxattr,lsetxattr,removexattr,fremovexattr,lremovexattr -k perm_mod
-a always,exit -F arch=b64 -S chown,fchown,fchownat,lchown -k perm_mod
-a always,exit -F arch=b64 -S chmod,fchmod,fchmodat -k perm_mod

# File access
-a always,exit -F arch=b64 -S creat,open,openat,open_by_handle_at,truncate,ftruncate -F exit=-EACCES -k access
-a always,exit -F arch=b64 -S creat,open,openat,open_by_handle_at,truncate,ftruncate -F exit=-EPERM  -k access

# Privileged commands (full list in remediation script)
-a always,exit -F path=/usr/bin/sudo  -F perm=x -k privileged
-a always,exit -F path=/usr/bin/su    -F perm=x -k privileged
-a always,exit -F path=/bin/mount     -F perm=x -k privileged
```

## Example prompts

- *"How do I run an OpenSCAP SCAP scan on Ubuntu 24.04 with the DISA STIG benchmark?"*
- *"My scan fails with `Failed to locate a datastream`. What's the correct benchmark ID?"*
- *"STIG rule SV-270690 failed — how do I configure PAM lockout after 3 failed attempts?"*
- *"Which STIG rules should I skip on an AWS EC2 headless instance?"*
- *"Show me how to configure SSH FIPS 140-3 ciphers for Ubuntu 24.04."*
- *"Walk me through setting up AIDE integrity monitoring with a daily cron check."*
- *"I need to pass a DISA STIG audit next week for our EC2 fleet. What do I run first?"*

## Related skills

- [`postgres-ops`](./postgres-ops/SKILL.md) — STIG hardening for the PostgreSQL layer on this server
- [`arcgis-enterprise-k8s`](./arcgis-enterprise-k8s/SKILL.md) — OS hardening context for ArcGIS worker nodes
