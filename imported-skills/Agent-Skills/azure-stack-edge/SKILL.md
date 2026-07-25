---
name: azure-stack-edge
description: Expert knowledge for Azure Stack Edge development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. Use when deploying IoT Edge modules, Kubernetes/GPU apps, DeepStream pipelines, Arc GitOps, or local ARM workloads, and other Azure Stack Edge related development tasks. Not for Azure Data Box (use azure-data-box-family), Azure IoT Edge (use azure-iot-edge), Azure Local (use azure-local), Azure Virtual Machines (use azure-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-07"
  generator: "docs2skills/1.0.0"
---
# Azure Stack Edge Skill

This skill provides expert guidance for Azure Stack Edge. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L85 | Diagnosing and fixing Azure Stack Edge/Data Box Gateway issues: release-specific critical bugs, ordering/activation, certificates, ARM/Blob/IoT Edge/VM/GPU problems, and using logs/alerts for troubleshooting. |
| Best Practices | L86-L92 | Best practices for Azure Stack Edge Pro: device failure recovery, GPU sharing/partitioning guidance, and operational guidelines for deployment, monitoring, and maintenance. |
| Decision Making | L93-L101 | Guidance on region and data-location choices, resiliency behavior, disconnected deployment planning, and processes for replacing Azure Stack Edge devices. |
| Limits & Quotas | L102-L113 | Limits, capacities, performance, and system requirements for Azure Stack Edge and Data Box Gateway devices, including supported VM sizes and moving Edge resources across subscriptions. |
| Security | L114-L140 | Managing Azure Stack Edge security: user access, certs/TLS, Key Vault secrets, VPN/BCDR, Kubernetes RBAC, data erasure proof, and built-in Azure Policy for device protection. |
| Configuration | L141-L193 | Configuring and managing Azure Stack Edge/Data Box Gateway devices: networking, power, storage, Kubernetes, VMs, GPUs, monitoring, automation, and device lifecycle (reset, wipe, specs). |
| Integrations & Coding Patterns | L194-L204 | How to deploy and integrate workloads on Azure Stack Edge: IoT Edge modules, GPU-sharing/Kubernetes apps, DeepStream, Arc/Kubernetes GitOps, and connecting to local ARM. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Edge Hardware Center ordering issues | https://learn.microsoft.com/en-us/azure/azure-edge-hardware-center/azure-edge-hardware-center-troubleshoot-order |
| Azure Data Box Gateway 1905 GA release known issues | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-1905-release-notes |
| Azure Data Box Edge and Gateway 1906 release issues | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-1906-release-notes |
| Azure Stack Edge and Data Box Gateway 1911 release issues | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-1911-release-notes |
| Azure Stack Edge and Data Box Gateway 2007 release issues | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-2007-release-notes |
| Azure Data Box Gateway 2101 release known issues and workarounds | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-2101-release-notes |
| Azure Data Box Gateway 2105 release known issues and fixes | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-2105-release-notes |
| Azure Data Box Gateway 2301 release issues and fixes | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-2301-release-notes |
| Azure Data Box Gateway 2409 release issues and workarounds | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-2409-release-notes |
| Azure Data Box Gateway general availability release notes | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-release-notes |
| Troubleshoot Azure Data Box Gateway using diagnostics and logs | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-troubleshoot |
| Interpret and respond to Azure Stack Edge alerts | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-alerts |
| Review critical issues for Azure Stack Edge preview | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2008-release-notes |
| Review critical issues for Azure Stack Edge GA release | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2010-release-notes |
| Review critical issues for Azure Stack Edge 2101 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2101-release-notes |
| Review critical issues for Azure Stack Edge 2103 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2103-release-notes |
| Review critical issues for Azure Stack Edge 2105 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2105-release-notes |
| Review critical issues for Azure Stack Edge 2106 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2106-release-notes |
| Review critical issues for Azure Stack Edge 2110 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2110-release-notes |
| Review critical issues for Azure Stack Edge 2111 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2111-release-notes |
| Review critical issues for Azure Stack Edge 2202 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2202-release-notes |
| Review critical issues for Azure Stack Edge 2203 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2203-release-notes |
| Review critical issues for Azure Stack Edge 2205 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2205-release-notes |
| Review critical issues for Azure Stack Edge 2207 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2207-release-notes |
| Review critical issues for Azure Stack Edge 2209 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2209-release-notes |
| Review critical issues for Azure Stack Edge 2210 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2210-release-notes |
| Review critical issues for Azure Stack Edge 2301 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2301-release-notes |
| Review critical issues for Azure Stack Edge 2303 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2303-release-notes |
| Review critical issues for Azure Stack Edge 2304 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2304-release-notes |
| Review critical issues for Azure Stack Edge 2309 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2309-release-notes |
| Review critical issues for Azure Stack Edge 2312 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2312-release-notes |
| Review critical issues for Azure Stack Edge 2403 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2403-release-notes |
| Review critical issues for Azure Stack Edge 2407 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2407-release-notes |
| Review critical issues for Azure Stack Edge 2501 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2501-release-notes |
| Review critical issues for Azure Stack Edge 2506 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2506-release-notes |
| Resolve issues in Azure Stack Edge 2510 release | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2510-release-notes |
| Resolve issues in Azure Stack Edge 2604 release | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-2604-release-notes |
| Troubleshoot certificate issues on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-certificate-troubleshooting |
| Run diagnostics and collect logs on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot |
| Fix Azure Stack Edge activation and Key Vault errors | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-activation |
| Troubleshoot Azure Resource Manager issues on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-azure-resource-manager |
| Troubleshoot Blob storage issues on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-blob-storage |
| Troubleshoot IoT Edge runtime issues on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-iot-edge |
| Troubleshoot GPU extension installation on Azure Stack Edge VMs | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-virtual-machine-gpu-extension-installation |
| Troubleshoot VM image upload and management on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-virtual-machine-image-upload |
| Troubleshoot VM provisioning failures on Azure Stack Edge GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-troubleshoot-virtual-machine-provisioning |
| Troubleshoot Azure Stack Edge ordering problems | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-troubleshoot-ordering |

### Best Practices
| Topic | URL |
|-------|-----|
| Recover from Azure Stack Edge Pro device failure | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-recover-device-failure |
| Use GPU sharing options on Azure Stack Edge Pro GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-sharing |
| Apply operational guidelines for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-operational-guidelines-faq |

### Decision Making
| Topic | URL |
|-------|-----|
| Understand data residency options for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-data-residency |
| Understand data resiliency behavior for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-data-resiliency |
| Plan disconnected Azure Stack Edge deployments | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-disconnected-scenario |
| Choose Azure regions for Azure Stack Edge service and data | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-regions |
| Request and provision a replacement Azure Stack Edge device | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-replace-device |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Move Azure Edge Hardware Center resources across subscriptions | https://learn.microsoft.com/en-us/azure/azure-edge-hardware-center/azure-edge-hardware-center-resource-move-subscription-resource-group |
| Capacity and performance limits for Azure Data Box Gateway | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-limits |
| System requirements for Azure Data Box Gateway deployment | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-system-requirements |
| Supported VM sizes and capacities on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-virtual-machine-sizes |
| Azure Stack Edge Pro GPU service and device limits | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-limits |
| Capacity and system limits for Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-limits |
| Azure Stack Edge Pro 2 device and service limits | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-2-limits |
| Azure Stack Edge Pro R system limits and sizes | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-limits |

### Security
| Topic | URL |
|-------|-----|
| Manage user accounts and access on Azure Data Box Gateway | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-manage-users |
| Security configuration for Azure Data Box Gateway components | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-security |
| Use Azure Key Vault for Azure Stack Edge activation secrets | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-activation-key-vault |
| Certificate requirements and error troubleshooting for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-certificate-requirements |
| Understand certificate types for Azure Stack Edge devices | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-certificates-overview |
| Configure TLS 1.2 on Windows clients for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-configure-tls-settings |
| Create certificates for Azure Stack Edge using Azure PowerShell | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-create-certificates-powershell |
| Generate Azure Stack Edge certificates with Readiness Checker tool | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-create-certificates-tool |
| Configure certificates on Azure Stack Edge Pro GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-configure-certificates |
| Configure Kubernetes RBAC on Azure Stack Edge clusters | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-kubernetes-rbac |
| Manage certificates on Azure Stack Edge devices | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-certificates |
| Manage user access on Azure Stack Edge Pro GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-users |
| Prepare certificates for upload to Azure Stack Edge devices | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-prepare-certificates-device-upload |
| Securely erase Azure Stack Edge data and generate proof certificate | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-secure-erase-certificate |
| Set Azure Resource Manager access password on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-set-azure-resource-manager-password |
| Configure Point-to-Site VPN on Azure Stack Edge Mini R with PowerShell | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-configure-vpn-powershell |
| Configure certificates, VPN, and encryption on Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-deploy-configure-certificates-vpn-encryption |
| Configure certificates on Azure Stack Edge Pro 2 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-2-deploy-configure-certificates |
| Configure BCDR for Azure Stack Edge VPN | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-configure-vpn-bcdr |
| Configure certificates and encryption on Azure Stack Edge Pro R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-deploy-configure-certificates-vpn-encryption |
| Security features for Azure Stack Edge Pro R and Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-security |
| Understand Azure Stack Edge Pro FPGA security features | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-security |
| Apply Azure Policy built-ins for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/policy-reference |

### Configuration
| Topic | URL |
|-------|-----|
| Manage Azure Data Box Gateway using PowerShell commands | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-connect-powershell-interface |
| Configure access, power, and connectivity for Data Box Gateway | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-manage-access-power-connectivity-mode |
| Configure bandwidth schedules on Azure Data Box Gateway | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-manage-bandwidth-schedules |
| Monitor Azure Data Box Gateway metrics, alerts, and events | https://learn.microsoft.com/en-us/azure/databox-gateway/data-box-gateway-monitor |
| Configure custom VM sizes on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-create-vm-with-custom-size |
| Check network readiness for Azure Stack Edge deployments | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-deploy-check-network-readiness |
| Configure compute network access to modules on Azure Stack Edge FPGA | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-extend-compute-access-modules |
| Configure MetalLB BGP load balancing on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-configure-metallb-bgp-mode |
| Connect and manage Azure Stack Edge via Windows PowerShell | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-connect-powershell-interface |
| Configure and manage Kubernetes cluster on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-create-kubernetes-cluster |
| Create virtual switches on Azure Stack Edge via PowerShell | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-create-virtual-switch-powershell |
| Configure GPU/VPU acceleration for Kubernetes on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-compute-acceleration |
| Configure network and proxy for Azure Stack Edge GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-configure-network-compute-web-proxy |
| Configure dynamic storage for stateful Kubernetes apps on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-stateful-application-dynamic-provision-kubernetes |
| Configure static storage for stateful Kubernetes apps on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-stateful-application-static-provision-kubernetes |
| Configure Custom Script Extension for Azure Stack Edge VMs | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-virtual-machine-custom-script-extension |
| Configure GPU driver extension for Azure Stack Edge GPU VMs | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-virtual-machine-install-gpu-extension |
| Configure VM password reset extension on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-virtual-machine-install-password-reset-extension |
| Enable and use Edge container registry on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-edge-container-registry |
| Enable Azure Monitor for Azure Stack Edge Kubernetes | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-enable-azure-monitor |
| Manage access, power, and connectivity modes on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-access-power-connectivity-mode |
| Configure bandwidth schedules on Azure Stack Edge Pro GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-bandwidth-schedules |
| Manage IoT Edge compute settings on Azure Stack Edge Pro GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-compute |
| Manage Azure Stack Edge shares via Azure portal | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-shares |
| Manage Edge and local storage accounts on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-manage-storage-accounts |
| Use Kubernetes dashboard to monitor Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-monitor-kubernetes-dashboard |
| Overview of GPU VM support on Azure Stack Edge Pro GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-overview-gpu-virtual-machines |
| Configure proactive log collection on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-proactive-log-collection |
| Enable remote support and remediation on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-remote-support-diagnostics-repair |
| Review Azure Stack Edge Pro GPU system requirements | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-system-requirements |
| Check Azure Stack Edge Blob storage API and SDK support | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-system-requirements-rest |
| Review Azure Stack Edge Pro GPU technical specifications | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-technical-specifications-compliance |
| Configure network and proxy for Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-deploy-configure-network-compute-web-proxy |
| Set device, update, and time settings on Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-deploy-set-up-device-update-time |
| Manage Wi‑Fi connectivity on Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-manage-wifi |
| System and network requirements for Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-system-requirements |
| Create and use Wi‑Fi profiles for Azure Stack Edge Mini R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-mini-r-use-wifi-profiles |
| Automate Azure Stack Edge provisioning with PowerShell config file | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-powershell-based-configuration |
| Predeployment information checklist for Azure Stack Edge Pro 2 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-2-deploy-checklist |
| Configure network and web proxy for Azure Stack Edge Pro 2 | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-2-deploy-configure-network-compute-web-proxy |
| Review Azure Stack Edge Pro 2 system requirements | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-2-system-requirements |
| Understand Azure Stack Edge Pro 2 technical specifications | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-2-technical-specifications-compliance |
| Configure network and proxy for Azure Stack Edge Pro R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-deploy-configure-network-compute-web-proxy |
| Set device, update, and time settings on Azure Stack Edge Pro R | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-deploy-set-up-device-update-time |
| Review Azure Stack Edge Pro R system requirements | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-system-requirements |
| Understand Azure Stack Edge Pro R technical specifications | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-pro-r-technical-specifications-compliance |
| Azure Resource Manager API profile versions for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-profiles-azure-resource-manager-versions |
| Wipe and return an Azure Stack Edge device | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-return-device |
| Select correct power cords for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-technical-specifications-power-cords-regional |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Deploy NVIDIA DeepStream on Ubuntu VM on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-deploy-nvidia-deepstream-module |
| Connect to local Azure Resource Manager on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-connect-resource-manager |
| Build a C# IoT Edge module for Azure Stack Edge GPU | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-create-iot-edge-module |
| Enable Azure Arc on Kubernetes for Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-arc-kubernetes-cluster |
| Deploy IoT Edge GPU-sharing workloads on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-iot-edge-gpu-sharing |
| Deploy IoT Edge runtime on Ubuntu VM on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-iot-edge-linux-vm |
| Run Kubernetes GPU-sharing workloads on Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-kubernetes-gpu-sharing |
| Deploy PHP Guestbook via GitOps on Arc-enabled Azure Stack Edge | https://learn.microsoft.com/en-us/azure/databox-online/azure-stack-edge-gpu-deploy-stateless-application-git-ops-guestbook |