# Security

## Table of contents
1. Threat model for ROS 2 systems
2. SROS2 workflow
3. DDS security plugins
4. Certificate and key management
5. Permissions and governance authoring
6. Supply chain hardening
7. Network security and VPN alternatives
8. Performance impact of encryption
9. Development vs production workflow
10. Common failures and fixes

---

## 1. Threat model for ROS 2 systems

ROS 2 DDS communication is **unencrypted by default**. Any device on the same network and DDS domain can publish, subscribe, call services, and invoke actions without authentication. This is acceptable during development but unacceptable for production deployment.

### Attack surface overview

| Attack vector | Impact | Mitigation |
|---|---|---|
| Unencrypted DDS traffic | Eavesdropping on sensor data, commands | Enable DDS security (SROS2) or VPN |
| Unauthorized topic publishing | Spoofed sensor data, rogue commands | SROS2 access control (governance.xml) |
| Malicious node joining | Full system compromise | SROS2 authentication (mutual TLS) |
| DDS discovery sniffing | Map entire robot architecture | Encrypt discovery with SROS2 |
| Docker image tampering | Supply chain attack | Image signing, pinned base images |
| Rosdep/pip dependency confusion | Malicious package injection | Use official repos, verify checksums |
| Physical access to robot | Firmware tampering, key extraction | Secure boot, encrypted storage, HSM |
| Parameter service abuse | Alter node behavior at runtime | Restrict parameter services in permissions.xml |

### Why DDS domain isolation is not security

```bash
# Domain isolation only changes the UDP port — it is NOT a security mechanism
# An attacker can trivially scan all 232 domain IDs
export ROS_DOMAIN_ID=42  # Does NOT prevent eavesdropping or spoofing
```

---

## 2. SROS2 workflow

### Step 1: Generate keystore and enclaves

```bash
# Install SROS2 if not already present
sudo apt install ros-${ROS_DISTRO}-sros2

# Create SROS2 keystore
ros2 security create_keystore ~/sros2_keystore

# Generate keys for each node — enclave path must match the node's fully qualified name
ros2 security create_enclave ~/sros2_keystore /my_robot/driver
ros2 security create_enclave ~/sros2_keystore /my_robot/planner
ros2 security create_enclave ~/sros2_keystore /my_robot/controller
```

### Step 2: Generate policy from runtime introspection

```bash
# Option A: Auto-generate from running system (run system WITHOUT security first).
# IMPORTANT: This captures only currently-active communications. Run it while
# the system exercises ALL code paths (all topics, services, actions in use).
# Ephemeral communications (service calls during startup) are easily missed.
ros2 security generate_policy policy.xml

# Option B: Write policy manually (recommended for production — more precise)
# See Section 5 for detailed policy authoring
```

### Step 3: Create permissions from policy

```bash
ros2 security create_permission ~/sros2_keystore /my_robot/driver policy.xml
ros2 security create_permission ~/sros2_keystore /my_robot/planner policy.xml
ros2 security create_permission ~/sros2_keystore /my_robot/controller policy.xml
```

### Step 4: Configure environment

```bash
export ROS_SECURITY_KEYSTORE=~/sros2_keystore
export ROS_SECURITY_ENABLE=true
export ROS_SECURITY_STRATEGY=Enforce  # or "Permissive" for testing
```

### Step 5: Launch secured system

```python
# launch/secured_robot.launch.py
from launch import LaunchDescription
from launch.actions import SetEnvironmentVariable
from launch_ros.actions import Node
import os

def generate_launch_description():
    keystore_path = os.path.expanduser('~/sros2_keystore')

    return LaunchDescription([
        SetEnvironmentVariable('ROS_SECURITY_KEYSTORE', keystore_path),
        SetEnvironmentVariable('ROS_SECURITY_ENABLE', 'true'),
        SetEnvironmentVariable('ROS_SECURITY_STRATEGY', 'Enforce'),

        Node(
            package='my_robot_driver',
            executable='driver_node',
            name='driver',
            namespace='my_robot',
            additional_env={'ROS_SECURITY_ENCLAVE_OVERRIDE': '/my_robot/driver'},
        ),
        Node(
            package='my_robot_planner',
            executable='planner_node',
            name='planner',
            namespace='my_robot',
            additional_env={'ROS_SECURITY_ENCLAVE_OVERRIDE': '/my_robot/planner'},
        ),
    ])
```

### Step 6: Monitor and rotate

```bash
# Check certificate expiry
openssl x509 -in ~/sros2_keystore/enclaves/my_robot/driver/cert.pem \
  -noout -enddate

# Check all certificate expiry dates across the keystore
find ~/sros2_keystore -name "cert.pem" -exec sh -c \
  'echo "=== {} ===" && openssl x509 -in {} -noout -enddate -subject' \;
```

Default SROS2-generated certificates have ~2000-day (~5.5 year) validity. For production fleets, implement automated rotation well before expiry.

---

## 3. DDS security plugins

The OMG DDS Security specification defines three plugin interfaces that SROS2 configures automatically.

### Authentication (DDS:Auth:PKI-DH)

Mutual TLS authentication between DDS participants. Each node presents its certificate, both sides verify the chain back to the shared CA. Without authentication, any process on the network can impersonate any node.

### Access control (DDS:Access:Permissions)

Controls which topics, services, and actions each node can publish or subscribe to. Defined by two XML files:

- **governance.xml** -- domain-level rules (what protections are enabled)
- **permissions.xml** -- per-node rules (what each node can access)

Both files are signed by the permissions CA and distributed as `.p7s` (PKCS#7) files.

### Cryptographic (DDS:Crypto:AES-GCM-GMAC)

| Protection kind | Confidentiality | Integrity | Use case |
|---|---|---|---|
| `NONE` | No | No | Development only |
| `SIGN` | No | Yes | High-bandwidth sensor data (verify origin, skip encryption overhead) |
| `ENCRYPT` | Yes | Yes | Commands, credentials, sensitive data |

### How SROS2 configures the plugins

The RMW reads `ROS_SECURITY_KEYSTORE` and `ROS_SECURITY_ENCLAVE_OVERRIDE` to locate all required files automatically. The enclave directory contains: `cert.pem`, `key.pem`, `governance.p7s`, `permissions.p7s`, `identity_ca.cert.pem`, `permissions_ca.cert.pem`. No manual DDS XML configuration is needed when using SROS2 environment variables.

---

## 4. Certificate and key management

### Keystore directory structure

```
~/sros2_keystore/
+-- enclaves/
|   +-- my_robot/
|       +-- driver/
|       |   +-- cert.pem                # Node certificate
|       |   +-- key.pem                 # Node private key (protect!)
|       |   +-- governance.p7s          # Signed governance
|       |   +-- permissions.p7s         # Signed permissions
|       |   +-- permissions.xml         # Human-readable permissions
|       |   +-- identity_ca.cert.pem
|       |   +-- permissions_ca.cert.pem
|       +-- planner/
|           +-- ...
+-- private/
|   +-- ca.key.pem     # CA private key — NEVER distribute this
+-- public/
    +-- ca.cert.pem
    +-- identity_ca.cert.pem
    +-- permissions_ca.cert.pem
```

### CA certificate vs node certificates

```bash
# WRONG — storing CA key on the robot
scp ~/sros2_keystore/private/ca.key.pem robot@192.168.1.100:/opt/robot/keystore/

# CORRECT — only distribute enclave directories (node cert + key, not CA key)
scp -r ~/sros2_keystore/enclaves/my_robot/driver/ \
  robot@192.168.1.100:/opt/robot/keystore/enclaves/my_robot/driver/
```

The CA private key should remain on a secure build server or HSM. Only per-node enclave directories are deployed to robots.

### Certificate rotation at fleet scale

```bash
#!/bin/bash
# scripts/rotate_certs.sh — regenerate and distribute certificates
set -euo pipefail

KEYSTORE="$HOME/sros2_keystore"
POLICY="$HOME/fleet_policy.xml"
ROBOTS_FILE="$HOME/fleet_robots.txt"  # one hostname per line

# Regenerate certificates (requires CA key)
while IFS= read -r enclave; do
    ros2 security create_enclave "$KEYSTORE" "$enclave"
    ros2 security create_permission "$KEYSTORE" "$enclave" "$POLICY"
done < <(find "$KEYSTORE/enclaves" -name "cert.pem" -exec dirname {} \; \
         | sed "s|$KEYSTORE/enclaves||")

# Distribute and rolling restart
while IFS= read -r robot; do
    rsync -avz --delete "$KEYSTORE/enclaves/" \
      "robot@${robot}:/opt/robot/keystore/enclaves/"
    ssh "robot@${robot}" 'sudo systemctl restart ros2-robot'
    sleep 10  # Wait for stabilization before next robot
done < "$ROBOTS_FILE"
```

### HSM integration

For production, store the CA key in a hardware security module. SROS2 does not natively support HSM -- wrap OpenSSL signing operations with your HSM provider's PKCS#11 engine:

```bash
# Generate CA key inside HSM (key never leaves hardware)
pkcs11-tool --module /usr/lib/softhsm/libsofthsm2.so \
  --login --pin 5678 --keypairgen --key-type rsa:4096 \
  --label "ros2-ca-key"

# Sign certificates using the HSM-stored key
openssl req -engine pkcs11 -keyform engine \
  -key "pkcs11:token=ros2-ca;object=ros2-ca-key;type=private" \
  -new -x509 -days 365 -out ca.cert.pem \
  -subj "/CN=ROS2 Security CA"
```

---

## 5. Permissions and governance authoring

### Governance XML

```xml
<?xml version="1.0" encoding="UTF-8"?>
<dds xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
     xsi:noNamespaceSchemaLocation="http://www.omg.org/spec/DDS-SECURITY/20170901/omg_shared_ca_governance.xsd">
  <domain_access_rules>
    <domain_rule>
      <domains><id>0</id></domains>
      <allow_unauthenticated_participants>false</allow_unauthenticated_participants>
      <enable_join_access_control>true</enable_join_access_control>
      <discovery_protection_kind>ENCRYPT</discovery_protection_kind>
      <liveliness_protection_kind>ENCRYPT</liveliness_protection_kind>
      <rtps_protection_kind>ENCRYPT</rtps_protection_kind>
      <topic_access_rules>
        <!-- High-bandwidth sensors: sign only (integrity without encryption overhead) -->
        <topic_rule>
          <topic_expression>rt/camera/*</topic_expression>
          <enable_discovery_protection>true</enable_discovery_protection>
          <enable_liveliness_protection>true</enable_liveliness_protection>
          <enable_read_access_control>true</enable_read_access_control>
          <enable_write_access_control>true</enable_write_access_control>
          <metadata_protection_kind>SIGN</metadata_protection_kind>
          <data_protection_kind>SIGN</data_protection_kind>
        </topic_rule>
        <!-- All other topics: full encryption -->
        <topic_rule>
          <topic_expression>*</topic_expression>
          <enable_discovery_protection>true</enable_discovery_protection>
          <enable_liveliness_protection>true</enable_liveliness_protection>
          <enable_read_access_control>true</enable_read_access_control>
          <enable_write_access_control>true</enable_write_access_control>
          <metadata_protection_kind>ENCRYPT</metadata_protection_kind>
          <data_protection_kind>ENCRYPT</data_protection_kind>
        </topic_rule>
      </topic_access_rules>
    </domain_rule>
  </domain_access_rules>
</dds>
```

### Permissions XML — per-node access control

```xml
<?xml version="1.0" encoding="UTF-8"?>
<dds xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
     xsi:noNamespaceSchemaLocation="http://www.omg.org/spec/DDS-SECURITY/20170901/omg_shared_ca_permissions.xsd">
  <permissions>
    <grant name="/my_robot/driver">
      <subject_name>CN=/my_robot/driver</subject_name>
      <validity>
        <not_before>2025-01-01T00:00:00</not_before>
        <not_after>2028-01-01T00:00:00</not_after>
      </validity>

      <!-- Topics this node can publish -->
      <allow_rule>
        <domains><id>0</id></domains>
        <publish>
          <topics>
            <topic>rt/joint_states</topic>
            <topic>rt/diagnostics</topic>
            <topic>rt/rosout</topic>
          </topics>
        </publish>
      </allow_rule>

      <!-- Topics this node can subscribe to -->
      <allow_rule>
        <domains><id>0</id></domains>
        <subscribe>
          <topics>
            <topic>rt/joint_commands</topic>
            <topic>rt/parameter_events</topic>
          </topics>
        </subscribe>
      </allow_rule>

      <!-- Service request/reply topics (required for services to work) -->
      <allow_rule>
        <domains><id>0</id></domains>
        <publish>
          <topics>
            <topic>rr/my_robot/driver/get_parametersReply</topic>
            <topic>rr/my_robot/driver/set_parametersReply</topic>
          </topics>
        </publish>
        <subscribe>
          <topics>
            <topic>rq/my_robot/driver/get_parametersRequest</topic>
            <topic>rq/my_robot/driver/set_parametersRequest</topic>
          </topics>
        </subscribe>
      </allow_rule>

      <!-- Deny everything else -->
      <deny_rule>
        <domains><id>0</id></domains>
        <publish><topics><topic>*</topic></topics></publish>
        <subscribe><topics><topic>*</topic></topics></subscribe>
      </deny_rule>
      <default>DENY</default>
    </grant>
  </permissions>
</dds>
```

### Topic name prefixes in permissions

DDS topic names differ from ROS 2 topic names:

| ROS 2 entity | DDS topic prefix | Example |
|---|---|---|
| Topic `/foo` | `rt/foo` | `rt/joint_states` |
| Service request `/bar` | `rq/barRequest` | `rq/my_node/get_parametersRequest` |
| Service reply `/bar` | `rr/barReply` | `rr/my_node/get_parametersReply` |
| Action topics | `rt/.../_action/...` | `rt/navigate/_action/feedback` |
| Parameter events | `rt/parameter_events` | `rt/parameter_events` |

### Signing and validating policy files

```bash
# Sign governance/permissions after manual edits (requires CA key)
openssl smime -sign -text \
  -in governance.xml -out governance.p7s \
  -signer ~/sros2_keystore/public/permissions_ca.cert.pem \
  -inkey ~/sros2_keystore/private/ca.key.pem

# Validate XML against OMG schema before signing
xmllint --schema omg_shared_ca_governance.xsd governance.xml --noout
xmllint --schema omg_shared_ca_permissions.xsd permissions.xml --noout
```

---

## 6. Supply chain hardening

### Pin Docker base images by digest

```dockerfile
# WRONG — tag can be overwritten with a compromised image
FROM ros:jazzy-ros-base AS base

# CORRECT — pin by SHA256 digest (immutable reference)
FROM ros:jazzy-ros-base@sha256:a1b2c3d4e5f6... AS base
```

### Minimal packages and verified dependencies

```dockerfile
# WRONG — installs unnecessary packages, larger attack surface
RUN apt-get update && apt-get install -y ros-jazzy-desktop

# CORRECT — install only what you need
RUN apt-get update && apt-get install -y --no-install-recommends \
    ros-jazzy-ros-base \
    ros-jazzy-rmw-cyclonedds-cpp \
    && rm -rf /var/lib/apt/lists/*
```

### Pin Python dependencies with hash verification

```bash
# Generate requirements with hashes
pip-compile --generate-hashes requirements.in -o requirements.txt

# Install with hash verification — rejects tampered packages
pip install --no-cache-dir --require-hashes -r requirements.txt
```

### Container image scanning

```bash
# Scan with Trivy — fail CI on critical vulnerabilities
trivy image --exit-code 1 --severity CRITICAL,HIGH my_robot:latest
```

```yaml
# GitHub Actions integration
- name: Scan for vulnerabilities
  uses: aquasecurity/trivy-action@0.28.0  # Pin to specific version
  with:
    image-ref: my_robot:${{ github.sha }}
    exit-code: 1
    severity: CRITICAL,HIGH
```

### ROS package source verification

```bash
# WRONG — adding untrusted third-party PPAs
sudo add-apt-repository ppa:random-user/ros-packages

# CORRECT — use only the official OSRF repositories
sudo curl -sSL https://raw.githubusercontent.com/ros/rosdistro/master/ros.key \
  -o /usr/share/keyrings/ros-archive-keyring.gpg
```

---

## 7. Network security and VPN alternatives

### Comparison of approaches

| Approach | Latency impact | Per-topic control | Complexity | Best for |
|---|---|---|---|---|
| SROS2 (DDS Security) | ~2x latency | Yes | Medium | Full control, compliance |
| WireGuard VPN | ~10-50 us overhead | No (all-or-nothing) | Low | Simple site-to-site |
| SSH tunnel | ~1-5 ms overhead | No | Low | Development, debugging |
| Tailscale/ZeroTier | ~20-100 us overhead | No | Very low | Fleet with NAT traversal |

### DDS multicast does not work over VPN

DDS multicast discovery is not forwarded over VPN tunnels. Use unicast peer lists:

```xml
<!-- cyclonedds_vpn.xml — unicast discovery for VPN -->
<CycloneDDS>
  <Domain>
    <General>
      <Interfaces>
        <NetworkInterface name="wg0" />
      </Interfaces>
    </General>
    <Discovery>
      <Peers>
        <Peer address="10.0.0.1" />
        <Peer address="10.0.0.2" />
      </Peers>
      <ParticipantIndex>auto</ParticipantIndex>
    </Discovery>
  </Domain>
</CycloneDDS>
```

### Field robots behind NAT

For robots behind firewalls, NAT, or cellular connections, use Tailscale/ZeroTier for zero-config mesh VPN, or use Zenoh which natively supports TCP connections through NAT:

```bash
# Tailscale: install on each robot, assigns 100.x.y.z addresses
curl -fsSL https://tailscale.com/install.sh | sh
sudo tailscale up --hostname=robot-001
# Use Tailscale IPs in CycloneDDS peer list

# Zenoh (Jazzy+): built-in TLS without DDS security stack
# Configure TLS in Zenoh router config for encrypted transport
```

---

## 8. Performance impact of encryption

### Reference performance numbers

Approximate latency measured on x86_64 with CycloneDDS:

| Message size | No security | SIGN only | ENCRYPT | Overhead (ENCRYPT) |
|---|---|---|---|---|
| 64 B (command) | ~80 us | ~120 us | ~160 us | ~2x |
| 1 KB (status) | ~90 us | ~130 us | ~170 us | ~1.9x |
| 64 KB (point cloud chunk) | ~200 us | ~240 us | ~280 us | ~1.4x |
| 1 MB (image) | ~2.5 ms | ~2.8 ms | ~3.2 ms | ~1.3x |

CPU overhead is typically 5-15% additional load depending on message rate. Modern x86 CPUs with AES-NI and ARM CPUs with crypto extensions handle AES-256-GCM in hardware, significantly reducing the cost.

### Selective encryption strategy

Use mixed protection levels in governance.xml to balance security and performance:

- **ENCRYPT** for commands (`cmd_vel`, `joint_commands`) and sensitive data
- **SIGN** for high-bandwidth sensor streams (`camera/*`, `scan`) -- integrity without encryption cost
- **ENCRYPT** as default for everything else

See the governance.xml example in Section 5 for the full pattern.

### Hardware acceleration check

```bash
# Verify AES-NI is available (x86)
grep -o aes /proc/cpuinfo | head -1

# ARM crypto extensions (Raspberry Pi 4+, Jetson)
grep -o 'aes\|pmull\|sha' /proc/cpuinfo | sort -u

# OpenSSL benchmark to verify
openssl speed -evp aes-256-gcm
```

---

## 9. Development vs production workflow

### Three-stage security adoption

```
Development          Testing              Production
+-----------+     +------------+     +---------------+
| No SROS2  |     | Enforce    |     | Enforce       |
| Fast iter | --> | Broad perms| --> | Minimal perms |
+-----------+     +------------+     +---------------+
```

**Development:** No security enabled. Use `ROS_AUTOMATIC_DISCOVERY_RANGE=LOCALHOST`
(Jazzy+) or `ROS_LOCALHOST_ONLY=1` (Humble) and domain IDs for isolation.

**Zenoh note (Kilted+):** SROS2/DDS Security plugins only apply when using a DDS-based
RMW (`rmw_cyclonedds_cpp`, `rmw_fastdds_cpp`). When using `rmw_zenoh_cpp` (Tier 1
in Kilted), security is handled via Zenoh's own TLS configuration, NOT SROS2.
If you switch to Zenoh without configuring Zenoh TLS, your system is unprotected
even with `ROS_SECURITY_ENABLE=true`.

**Testing:** `ROS_SECURITY_STRATEGY=Permissive` first (logs violations but does not block), then `Enforce` with auto-generated broad permissions to catch missing enclaves.

**Production:** `ROS_SECURITY_STRATEGY=Enforce` with hand-crafted minimal permissions (principle of least privilege).

### Common transition gotchas

```bash
# WRONG — forgetting infrastructure nodes
ros2 security create_enclave ~/sros2_keystore /my_robot/driver
ros2 security create_enclave ~/sros2_keystore /my_robot/planner
# Missing: robot_state_publisher, lifecycle_manager, component_container

# CORRECT — create enclaves for ALL nodes including infrastructure
ros2 security create_enclave ~/sros2_keystore /my_robot/driver
ros2 security create_enclave ~/sros2_keystore /my_robot/planner
ros2 security create_enclave ~/sros2_keystore /my_robot/robot_state_publisher
ros2 security create_enclave ~/sros2_keystore /my_robot/lifecycle_manager
```

```bash
# WRONG — using the same enclave for all nodes (defeats access control)
export ROS_SECURITY_ENCLAVE_OVERRIDE=/my_robot/shared

# CORRECT — each node gets its own enclave in the launch file
# Set per-node via additional_env in Node() declaration
```

### Docker deployment

```dockerfile
# Copy only enclaves — NEVER bake the CA private key into images
COPY keystore/enclaves/ /opt/robot/keystore/enclaves/
COPY keystore/public/ /opt/robot/keystore/public/
# The CA key stays on the build server

ENV ROS_SECURITY_KEYSTORE=/opt/robot/keystore
ENV ROS_SECURITY_ENABLE=true
ENV ROS_SECURITY_STRATEGY=Enforce
```

---

## 10. Common failures and fixes

| Symptom | Cause | Fix |
|---|---|---|
| Node fails to start with security enabled | Missing enclave or wrong enclave path | Verify `ROS_SECURITY_ENCLAVE_OVERRIDE` matches a path under `$ROS_SECURITY_KEYSTORE/enclaves/` |
| "unable to find valid identity" | Certificate expired or CA mismatch | Regenerate certs; check `openssl x509 -in cert.pem -noout -enddate` |
| Nodes cannot discover each other | Keystores do not share CA | Ensure all nodes use certs generated from the same CA keystore |
| Performance drops 50%+ | Full encryption on high-bandwidth topics | Use `SIGN` protection for sensor streams in governance.xml |
| Service calls timeout with security | Access control denying request/reply topics | Check permissions.xml includes both `rq/...Request` and `rr/...Reply` patterns |
| "Inconsistent security policy" | governance.xml format error or unsigned | Validate against OMG XSD schema; re-sign with `openssl smime -sign` |
| ros2 CLI tools cannot see topics | CLI process has no security enclave | Create an enclave for the CLI tool or use `Permissive` mode for debugging |
| Nodes start but topics have no data | Permissions allow subscribe but deny publish (or vice versa) | Check both publish and subscribe rules for every topic |
| "PKCS7 signature verification failed" | permissions.p7s signed with wrong CA key | Re-sign with the same CA key used to create the keystore |
| Lifecycle transitions fail | Missing permissions for lifecycle service topics | Add `rq/...change_stateRequest` and `rr/...change_stateReply` to permissions |

### Debugging security issues

```bash
# Step 1: Verify environment
env | grep ROS_SECURITY

# Step 2: Verify enclave directory has all required files
ls -la "$ROS_SECURITY_KEYSTORE/enclaves$(echo $ROS_SECURITY_ENCLAVE_OVERRIDE)"
# Must contain: cert.pem, key.pem, governance.p7s, permissions.p7s,
#               identity_ca.cert.pem, permissions_ca.cert.pem

# Step 3: Check certificate validity
openssl x509 -in cert.pem -noout -text | grep -A2 "Validity"

# Step 4: Switch to Permissive to isolate the problem
export ROS_SECURITY_STRATEGY=Permissive
# Run the system and check logs for SECURITY warnings

# Step 5: Enable CycloneDDS security tracing
```

```xml
<!-- cyclonedds_security_debug.xml -->
<CycloneDDS>
  <Domain>
    <Tracing>
      <Category>discovery,security</Category>
      <OutputFile>/tmp/cyclonedds_security.log</OutputFile>
      <Verbosity>fine</Verbosity>
    </Tracing>
  </Domain>
</CycloneDDS>
```

```bash
export CYCLONEDDS_URI=file:///opt/robot/config/cyclonedds_security_debug.xml
ros2 run my_robot_driver driver_node
cat /tmp/cyclonedds_security.log | grep -i "error\|fail\|denied"
```
