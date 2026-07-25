# CSPM Check Reference

Complete check matrices for cloud security posture management across AWS, Azure, and GCP. Each check includes finding condition, severity, MITRE ATT&CK technique, and remediation guidance.

---

## AWS IAM Checks

| Check | Finding Condition | Severity | MITRE | Remediation |
|-------|------------------|----------|-------|-------------|
| Full admin wildcard | `Action: *` + `Resource: *` in Allow statement | Critical | T1078.004 | Replace with service-specific scoped policies |
| Public principal | `Principal: *` in Allow statement | Critical | T1190 | Restrict to specific account ARNs + aws:PrincipalOrgID condition |
| Lambda PassRole combo | `iam:PassRole` + `lambda:CreateFunction` | Critical | T1078.004 | Remove iam:PassRole or restrict to specific function ARNs |
| EC2 PassRole combo | `iam:PassRole` + `ec2:RunInstances` | Critical | T1078.004 | Remove iam:PassRole or restrict to specific instance profile ARNs |
| CloudFormation PassRole | `iam:PassRole` + `cloudformation:CreateStack` | Critical | T1078.004 | Restrict PassRole to specific service role ARNs |
| Self-attach escalation | `iam:AttachUserPolicy` + `sts:GetCallerIdentity` | Critical | T1484.001 | Remove iam:AttachUserPolicy from non-admin policies |
| Policy version backdoor | `iam:CreatePolicyVersion` + `iam:ListPolicies` | Critical | T1484.001 | Restrict CreatePolicyVersion to named policy ARNs |
| Service-level wildcard | `iam:*`, `s3:*`, `ec2:*`, etc. | High | T1078.004 | Replace with specific required actions |
| Credential harvesting | `iam:CreateAccessKey` + `iam:ListUsers` | High | T1098.001 | Separate roles; restrict CreateAccessKey to self only |
| Data exfil on wildcard | `s3:GetObject` on `Resource: *` | High | T1530 | Restrict to specific bucket ARNs |
| Secrets exfil on wildcard | `secretsmanager:GetSecretValue` on `Resource: *` | High | T1552 | Restrict to specific secret ARNs |

---

## AWS S3 Checks

| Check | Finding Condition | Severity | MITRE | Remediation |
|-------|------------------|----------|-------|-------------|
| Public access block missing | Any of four flags = false or absent | High | T1530 | Enable all four flags at bucket and account level |
| Bucket ACL public-read-write | ACL = public-read-write | Critical | T1530 | Set ACL = private; use bucket policy for access control |
| Bucket ACL public-read | ACL = public-read or authenticated-read | High | T1530 | Set ACL = private |
| Bucket policy Principal:* | Statement with Effect=Allow, Principal=* | Critical | T1190 | Restrict Principal to specific ARNs + aws:PrincipalOrgID |
| No default encryption | No ServerSideEncryptionConfiguration | High | T1530 | Add default encryption rule (AES256 or aws:kms) |
| Non-standard encryption | SSEAlgorithm not in {AES256, aws:kms, aws:kms:dsse} | Medium | T1530 | Switch to standard SSE algorithm |
| Versioning disabled | VersioningConfiguration = Suspended or absent | Medium | T1485 | Enable versioning to protect against ransomware deletion |
| Access logging disabled | LoggingEnabled absent | Low | T1530 | Enable server access logging for audit trail |

---

## AWS Security Group Checks

| Check | Finding Condition | Severity | MITRE | Remediation |
|-------|------------------|----------|-------|-------------|
| All traffic open | Protocol=-1 (all) from 0.0.0.0/0 or ::/0 | Critical | T1190 | Remove rule; add specific required ports only |
| SSH open | Port 22 from 0.0.0.0/0 or ::/0 | Critical | T1110 | Restrict to VPN CIDR or use AWS Systems Manager Session Manager |
| RDP open | Port 3389 from 0.0.0.0/0 or ::/0 | Critical | T1110 | Restrict to VPN CIDR or use AWS Fleet Manager |
| MySQL open | Port 3306 from 0.0.0.0/0 or ::/0 | High | T1190 | Move DB to private subnet; allow only from app tier SG |
| PostgreSQL open | Port 5432 from 0.0.0.0/0 or ::/0 | High | T1190 | Move DB to private subnet; allow only from app tier SG |
| MSSQL open | Port 1433 from 0.0.0.0/0 or ::/0 | High | T1190 | Move DB to private subnet; allow only from app tier SG |
| MongoDB open | Port 27017 from 0.0.0.0/0 or ::/0 | High | T1190 | Move DB to private subnet; allow only from app tier SG |
| Redis open | Port 6379 from 0.0.0.0/0 or ::/0 | High | T1190 | Move Redis to private subnet; allow only from app tier SG |
| Elasticsearch open | Port 9200 from 0.0.0.0/0 or ::/0 | High | T1190 | Move to private subnet; use VPC endpoint |

---

## Azure Checks

| Check | Service | Finding Condition | Severity | Remediation |
|-------|---------|------------------|----------|-------------|
| Owner role assigned broadly | Entra ID RBAC | Owner role assigned to more than break-glass accounts at subscription scope | Critical | Use least-privilege built-in roles; restrict Owner to named individuals |
| Guest user with privileged role | Entra ID | Guest account assigned Contributor or Owner | High | Remove guest from privileged roles; use B2B identity governance |
| Blob container public access | Azure Storage | Container `publicAccess` = Blob or Container | Critical | Set to None; use SAS tokens for external access |
| Storage account HTTPS only = false | Azure Storage | `supportsHttpsTrafficOnly` = false | High | Enable HTTPS-only traffic |
| Storage account network rules allow all | Azure Storage | `networkAcls.defaultAction` = Allow | High | Set defaultAction = Deny; add specific VNet rules |
| NSG rule allows any-to-any | Azure NSG | Inbound rule with SourceAddressPrefix = * and DestinationPortRange = * | Critical | Replace with specific port and source ranges |
| NSG allows SSH from internet | Azure NSG | Port 22 inbound from 0.0.0.0/0 | Critical | Restrict to VPN or use Azure Bastion |
| Key Vault soft-delete disabled | Azure Key Vault | `softDeleteEnabled` = false | High | Enable soft delete and purge protection |
| MFA not required for admin | Entra ID | Global Administrator without MFA enforcement | Critical | Enforce MFA via Conditional Access for all privileged roles |
| PIM not used for privileged roles | Entra ID | Standing assignment to privileged role (not eligible) | High | Migrate to PIM eligible assignments with JIT activation |

---

## GCP Checks

| Check | Service | Finding Condition | Severity | Remediation |
|-------|---------|------------------|----------|-------------|
| Service account has project Owner | Cloud IAM | Service account bound to roles/owner | Critical | Replace with specific required roles |
| Primitive role on project | Cloud IAM | roles/owner, roles/editor, or roles/viewer on project | High | Replace with predefined or custom roles |
| Public storage bucket | Cloud Storage | `allUsers` or `allAuthenticatedUsers` in bucket IAM | Critical | Remove public members; use signed URLs for external access |
| Bucket uniform access disabled | Cloud Storage | `uniformBucketLevelAccess.enabled` = false | Medium | Enable uniform bucket-level access |
| Firewall rule allows all ingress | Cloud VPC | Ingress rule with sourceRanges = 0.0.0.0/0 and ports = all | Critical | Replace with specific ports and source ranges |
| SSH firewall rule from internet | Cloud VPC | Port 22 ingress from 0.0.0.0/0 | Critical | Restrict to IAP CIDR (35.235.240.0/20) or use IAP TCP tunneling |
| Audit logging disabled | Cloud Audit Logs | Admin activity or data access logs disabled for a service | High | Enable audit logging for all services, especially IAM and storage |
| Default service account used | Compute Engine | Instance using the default compute service account | Medium | Create dedicated service accounts with minimal required scopes |
| Serial port access enabled | Compute Engine | `metadata.serial-port-enable` = true | Medium | Disable serial port access; use OS Login instead |

---

## IaC Check Matrix

### Terraform AWS Provider

| Resource | Property | Insecure Value | Remediation |
|----------|----------|---------------|-------------|
| `aws_s3_bucket_acl` | `acl` | `public-read`, `public-read-write` | Set to `private` |
| `aws_s3_bucket_public_access_block` | `block_public_acls` | `false` or absent | Set to `true` |
| `aws_security_group_rule` | `cidr_blocks` with port 22 | `["0.0.0.0/0"]` | Restrict to VPN CIDR |
| `aws_iam_policy_document` | `actions` | `["*"]` | Specify required actions |
| `aws_iam_policy_document` | `resources` | `["*"]` | Specify resource ARNs |

### Kubernetes

| Resource | Property | Insecure Value | Remediation |
|----------|----------|---------------|-------------|
| Pod/Deployment | `securityContext.runAsRoot` | `true` | Run as non-root user |
| Pod/Deployment | `securityContext.privileged` | `true` | Remove privileged flag |
| ServiceAccount | `automountServiceAccountToken` | `true` (default) | Set to `false` unless required |
| NetworkPolicy | Missing | No NetworkPolicy defined for namespace | Add default-deny ingress/egress policy |
| Secret | Type | Credentials in ConfigMap instead of Secret | Move to Kubernetes Secrets or external secrets manager |
