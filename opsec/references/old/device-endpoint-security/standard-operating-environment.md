# Standard Operating Environment

A Standard Operating Environment (SOE) refers to a standardized and controlled computing environment used across a
project. It ensures that all devices and systems adhere to the same security policies, configurations, and software
versions, thereby reducing vulnerabilities and simplifying management.

## Key Components of an SOE

### Device Configuration

1. Ensure all workstations and mobile devices use [full-disk encryption](/encryption/full-disk-encryption) to protect
data at rest.
2. Configure devices to automatically apply critical security patches and updates.
3. Ensure all installed applications are regularly updated to their latest versions to mitigate vulnerabilities.
4. Never leave workstations unlocked and unattended.
5. Operating Systems commonly affected by malicious software should have anti-malware software installed and running.
6. Ensure the plugins you use for your browser are secure.
7. Avoid using an Administrator account for day-to-day activities.
8. Disable macros on Office products.
9. If a device has been left unlocked with a third party having access without you seeing what they did (e.g., at an
airport security check), treat it as having been compromised.

### User Access Controls

1. Grant users the minimum level of access required to perform their job functions. Avoid using administrative accounts
for day-to-day activities.
2. Implement RBAC to manage permissions and access based on user roles within the organization.
3. Require MFA for accessing sensitive systems and data. Use hardware tokens (e.g., Yubikeys) for the highest level of
security.

### Security Software

1. Install and maintain anti-malware software on all devices where relevant. Ensure it is configured to automatically
update and scan regularly.
2. Enable and configure local firewalls on all devices where applicable to control inbound and outbound network traffic.

### Data Management

1. Encrypt sensitive data both in transit and at rest. Use strong encryption standards and manage encryption keys
securely.
2. Implement regular backup procedures for all critical data. Ensure backups are encrypted and stored securely offsite
or in the cloud. Regularly test recovery processes to ensure data integrity.
3. Classify data based on sensitivity and implement appropriate handling and storage procedures for each classification
level.

### Network Security

1. Segment networks to limit access to sensitive systems where applicable. Use virtual LANs (VLANs) and firewalls to
enforce segmentation.
2. Require the use of VPNs for remote access to the organization's network. Ensure VPNs use strong encryption protocols.
3. Secure wireless networks using WPA3 or WPA2 with AES encryption. Regularly update Wi-Fi passwords and manage access
to authorized devices only.

---

