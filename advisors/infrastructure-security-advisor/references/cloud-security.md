# Cloud Security Guide

## AWS Security Essentials

### IAM
- Enable MFA for root account
- Don't use root for daily operations
- Create IAM users with least privilege
- Use IAM roles for services
- Rotate access keys regularly
- Use AWS Organizations for multi-account

### Networking
- Use VPCs with private subnets
- Security groups as primary firewall
- NACLs for additional layer
- VPC Flow Logs enabled
- No public IPs on backend services
- Use NAT Gateway for outbound

### Logging & Monitoring
- CloudTrail enabled in all regions
- CloudWatch Logs for applications
- GuardDuty enabled
- AWS Config for compliance
- SecurityHub for centralized findings

### Data Protection
- S3 buckets private by default
- Enable S3 Block Public Access
- Encrypt EBS volumes
- Use KMS for key management
- Enable versioning on critical buckets

## GCP Security Essentials

### IAM
- Enable 2FA for all users
- Use service accounts for workloads
- Principle of least privilege
- Use organization policies
- Regular IAM audits

### Networking
- Use VPC networks
- Private Google Access enabled
- Cloud NAT for outbound
- Cloud Armor for DDoS/WAF
- VPC Service Controls for data exfiltration prevention

### Logging
- Cloud Audit Logs enabled
- Cloud Logging for applications
- Security Command Center
- Export logs to SIEM

## Azure Security Essentials

### Identity
- Azure AD for identity
- MFA enforced
- Conditional Access policies
- Privileged Identity Management
- Regular access reviews

### Networking
- Virtual Networks with NSGs
- Azure Firewall or third-party
- Private endpoints for services
- DDoS Protection Standard

### Monitoring
- Azure Monitor
- Microsoft Defender for Cloud
- Azure Sentinel for SIEM
- Activity Log retention

## Multi-Cloud Considerations

### Consistent Security Posture
- Unified identity management (e.g., SSO)
- Consistent logging to central SIEM
- Same security policies across clouds
- Single pane of glass monitoring

### Provider Redundancy
- Consider multi-cloud for resilience
- But don't spread too thin
- Ensure equal security across all

## Common Cloud Misconfigurations

### Storage Buckets
- Public read/write access
- Missing encryption
- No access logging
- Overly permissive IAM policies

### Compute
- Excessive IAM permissions
- Public IP on internal services
- Outdated/unpatched images
- Secrets in environment variables

### Network
- 0.0.0.0/0 in security groups
- Unnecessary open ports
- No network segmentation
- VPN/bastion misconfiguration

### Secrets
- Hardcoded in code
- Stored in plaintext
- Overly broad access
- No rotation policy

## Security Tools

### Infrastructure as Code Security
- checkov
- tfsec
- cfn_nag
- KICS

### Cloud Security Posture Management
- Prowler (AWS)
- ScoutSuite
- CloudSploit
- Cloud Custodian

### Runtime Security
- Falco
- Wiz
- Lacework
- Orca Security
