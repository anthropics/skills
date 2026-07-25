---
name: azure-confidential-computing
description: Expert knowledge for Azure Confidential Computing development including decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building SGX/SEV-SNP apps, AKS confidential containers, SKR/Key Vault flows, vTPM/CVMs, or Fortanix CCM, and other Azure Confidential Computing related development tasks. Not for Azure Virtual Enclaves (use azure-virtual-enclaves), Azure Dedicated HSM (use azure-dedicated-hsm), Azure Cloud Hsm (use azure-cloud-hsm), Azure Payment Hsm (use azure-payment-hsm).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure Confidential Computing Skill

This skill provides expert guidance for Azure Confidential Computing. Covers decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Decision Making | L35-L46 | Guidance on choosing Azure confidential computing options: VMs (AMD/Intel), containers, GPUs, deployment models, capabilities, products, and use cases for secure workloads. |
| Architecture & Design Patterns | L47-L56 | Architectural patterns and design guidance for using Azure confidential VMs, SGX enclaves, AKS, and multi-party analytics to build secure AI and containerized workloads. |
| Limits & Quotas | L57-L62 | Intel SGX capacity, quotas, and sizing for Azure confidential computing: AKS confidential node limits, SGX VM sizing guidance, and FAQ on SGX resource constraints. |
| Security | L63-L78 | Security, attestation, and key/secrets management for Azure confidential workloads: SGX enclaves, CVMs, vTPM, AKS confidential containers, clean rooms, and hardening Linux images. |
| Configuration | L79-L90 | Configuring and deploying Azure confidential VMs and containers (AKS SGX, VMMD blob, CMK rotation, ARM/CLI), plus Secure Key Release policies and Virtual Machine Metablob Disk usage. |
| Integrations & Coding Patterns | L91-L101 | Coding patterns and samples for building, running, and attesting Intel SGX/AMD SEV-SNP confidential apps and containers, including SKR flows, tools, and Fortanix/Key Vault integrations. |
| Deployment | L102-L110 | How to deploy and migrate Azure confidential VMs/VMSS and AKS (SGX and confidential node pools), create custom images, and set up Fortanix CCM using CLI and ARM templates. |

### Decision Making
| Topic | URL |
|-------|-----|
| Select Azure confidential container offerings | https://learn.microsoft.com/en-us/azure/confidential-computing/choose-confidential-containers-offerings |
| Choose Azure confidential computing deployment models | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-computing-deployment-models |
| Understand Azure confidential container options | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-containers |
| Overview of confidential containers on Azure | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-containers |
| Understand and choose Azure confidential VM capabilities | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-vm-overview |
| Use Azure confidential GPUs for secure compute offload | https://learn.microsoft.com/en-us/azure/confidential-computing/gpu-options |
| Choose Azure confidential computing use cases | https://learn.microsoft.com/en-us/azure/confidential-computing/use-cases-scenarios |
| Select Azure confidential VM options on AMD or Intel | https://learn.microsoft.com/en-us/azure/confidential-computing/virtual-machine-options |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Apply confidential computing to AI workloads on Azure | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-ai |
| Design solutions with Azure confidential computing options | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-computing-solutions |
| Use SGX enclave nodes in AKS workloads | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-nodes-aks-overview |
| Design enclave-aware container applications on AKS | https://learn.microsoft.com/en-us/azure/confidential-computing/enclave-aware-containers |
| Understand Azure confidential VM guest attestation design | https://learn.microsoft.com/en-us/azure/confidential-computing/guest-attestation-confidential-virtual-machines-design |
| Architect multi-party analytics on Azure confidential computing | https://learn.microsoft.com/en-us/azure/confidential-computing/multi-party-data |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| AKS confidential nodes Intel SGX capacity details | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-nodes-aks-faq |
| Deploy and size Intel SGX VMs on Azure | https://learn.microsoft.com/en-us/azure/confidential-computing/virtual-machine-solutions-sgx |

### Security
| Topic | URL |
|-------|-----|
| Configure attestation for Azure SGX enclaves | https://learn.microsoft.com/en-us/azure/confidential-computing/attestation |
| Use attestation types for Azure confidential workloads | https://learn.microsoft.com/en-us/azure/confidential-computing/attestation-solutions |
| Use Secure Key Release with Azure Key Vault and confidential computing | https://learn.microsoft.com/en-us/azure/confidential-computing/concept-skr-attestation |
| Security model for AKS Confidential Containers | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-containers-aks-security-policy |
| Understand security details for Azure confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-vm-faq |
| Configure guest attestation for Azure confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/guest-attestation-confidential-vms |
| Secure confidential VMs with Defender for Cloud and guest attestation | https://learn.microsoft.com/en-us/azure/confidential-computing/guest-attestation-defender-for-cloud |
| Harden Linux images by removing Azure guest agent | https://learn.microsoft.com/en-us/azure/confidential-computing/harden-a-linux-image-to-remove-azure-guest-agent |
| Harden Linux images by removing sudo users for confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/harden-the-linux-image-to-remove-sudo-users |
| Leverage vTPM features in Linux confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/how-to-leverage-virtual-tpms-in-azure-confidential-vms |
| Manage secrets and keys in Azure confidential computing | https://learn.microsoft.com/en-us/azure/confidential-computing/secret-key-management |
| Use virtual TPMs in Azure confidential VMs securely | https://learn.microsoft.com/en-us/azure/confidential-computing/virtual-tpms-in-azure-confidential-vm |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Confidential Containers on AKS (preview) | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-containers-on-aks-preview |
| Configure AKS Intel SGX device plugin (confcom) | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-nodes-aks-addon |
| Configure opt-out of VMMD blob for Azure Confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/disable-confidential-vm-metadata-blob |
| Rotate customer-managed keys for Azure confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/key-rotation-offline |
| Deploy Azure confidential VMs with ARM templates | https://learn.microsoft.com/en-us/azure/confidential-computing/quick-create-confidential-vm-arm |
| Provision Azure confidential VMs using Azure CLI | https://learn.microsoft.com/en-us/azure/confidential-computing/quick-create-confidential-vm-azure-cli |
| Author Secure Key Release policies for Azure confidential TEEs | https://learn.microsoft.com/en-us/azure/confidential-computing/skr-policy-examples |
| Use Virtual Machine Metablob Disk with confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/virtual-machine-metablob-disk |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use development tools for Intel SGX enclaves on Azure | https://learn.microsoft.com/en-us/azure/confidential-computing/application-development |
| Run confidential containers with Intel SGX enclaves | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-containers-enclaves |
| Build Intel SGX enclave apps with OSS tools | https://learn.microsoft.com/en-us/azure/confidential-computing/enclave-development-oss |
| Use guest attestation sample app with confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/guest-attestation-example |
| Run apps with Fortanix CCM and Node Agent | https://learn.microsoft.com/en-us/azure/confidential-computing/how-to-fortanix-confidential-computing-manager-node-agent |
| Implement SKR with confidential containers on Azure Container Instances | https://learn.microsoft.com/en-us/azure/confidential-computing/skr-flow-confidential-containers-azure-container-instance |
| Implement SKR from Key Vault to AMD SEV-SNP confidential VMs | https://learn.microsoft.com/en-us/azure/confidential-computing/skr-flow-confidential-vm-sev-snp |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy AKS cluster with SGX enclave nodes via CLI | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-enclave-nodes-aks-get-started |
| Use confidential VM node pools in AKS | https://learn.microsoft.com/en-us/azure/confidential-computing/confidential-node-pool-aks |
| Create custom images for Azure confidential VMs with CLI | https://learn.microsoft.com/en-us/azure/confidential-computing/how-to-create-custom-image-confidential-vm |
| Deploy Fortanix CCM as Azure managed app | https://learn.microsoft.com/en-us/azure/confidential-computing/how-to-fortanix-confidential-computing-manager |
| Migrate nested Azure confidential VMs across regions | https://learn.microsoft.com/en-us/azure/confidential-computing/migrate-nested-confidential-vms |
| Deploy VM scale sets with hardened Linux images | https://learn.microsoft.com/en-us/azure/confidential-computing/vmss-deployment-from-hardened-linux-image |