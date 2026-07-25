---
name: azure-iot-edge
description: Expert knowledge for Azure IoT Edge development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring IoT Edge/EFLOW, DPS/X.509 provisioning, module deployment, gateways, or downstream devices, and other Azure IoT Edge related development tasks. Not for Azure IoT Hub (use azure-iot-hub), Azure IoT Central (use azure-iot-central), Azure IoT Operations (use azure-iot-operations), Azure Stack Edge (use azure-stack-edge).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure IoT Edge Skill

This skill provides expert guidance for Azure IoT Edge. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L47 | Diagnosing and fixing IoT Edge runtime/device errors, monitoring and metrics issues, portal-based troubleshooting, and EFLOW (Linux on Windows) and networking problems. |
| Best Practices | L48-L53 | Monitoring module twins for health/alerts and production-readiness guidance for IoT Edge solutions (deployment hardening, reliability, security, and operational best practices). |
| Decision Making | L54-L60 | Guidance on choosing IoT Edge/EFLOW platforms, provisioning methods, networking setups, and nested virtualization options for different deployment scenarios. |
| Architecture & Design Patterns | L61-L66 | Gateway design patterns for connecting downstream devices and patterns for handling offline/intermittent connectivity, local processing, and sync behavior in Azure IoT Edge setups. |
| Limits & Quotas | L67-L71 | Azure IoT Edge resource limits and quotas, including module, deployment, message, and device constraints, plus scalability and performance-related restrictions. |
| Security | L72-L84 | Securing IoT Edge with certificates, X.509 provisioning, confidential computing, downstream device auth, EST server setup, and network protection via Private Link/endpoints. |
| Configuration | L85-L118 | Configuring IoT Edge devices and EFLOW: networking, gateways, proxies, provisioning (DPS, TPM, X.509), storage, GPU, metrics/monitoring, and module/container deployment settings. |
| Integrations & Coding Patterns | L119-L126 | Remote management and logging via direct methods, building and packaging custom IoT Edge modules, and managing IoT Edge on Windows with EFLOW PowerShell functions |
| Deployment | L127-L136 | Deploying IoT Edge at scale: CI/CD pipelines, CLI/manifest-based module deployment, Kubernetes/KubeVirt installs, automatic deployments, and supported platform requirements. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Monitor integration for IoT Edge metrics | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-troubleshoot-monitoring-and-faq |
| Troubleshoot and diagnose Azure IoT Edge issues | https://learn.microsoft.com/en-us/azure/iot-edge/troubleshoot |
| Diagnose and fix common Azure IoT Edge errors | https://learn.microsoft.com/en-us/azure/iot-edge/troubleshoot-common-errors |
| Troubleshoot Azure IoT Edge devices from the Azure portal | https://learn.microsoft.com/en-us/azure/iot-edge/troubleshoot-in-portal |
| Troubleshoot Azure IoT Edge for Linux on Windows devices | https://learn.microsoft.com/en-us/azure/iot-edge/troubleshoot-iot-edge-for-linux-on-windows |
| Resolve common Azure IoT Edge for Linux on Windows issues | https://learn.microsoft.com/en-us/azure/iot-edge/troubleshoot-iot-edge-for-linux-on-windows-common-errors |
| Troubleshoot networking issues for EFLOW virtual machines | https://learn.microsoft.com/en-us/azure/iot-edge/troubleshoot-iot-edge-for-linux-on-windows-networking |

### Best Practices
| Topic | URL |
|-------|-----|
| Monitor IoT Edge module twins for health | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-monitor-module-twins |
| Prepare Azure IoT Edge solutions for production | https://learn.microsoft.com/en-us/azure/iot-edge/production-checklist |

### Decision Making
| Topic | URL |
|-------|-----|
| Select and configure networking options for EFLOW | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-configure-iot-edge-for-linux-on-windows-networking |
| Choose platform and provisioning options for IoT Edge devices | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-create-iot-edge-device |
| Choose nested virtualization options for EFLOW deployments | https://learn.microsoft.com/en-us/azure/iot-edge/nested-virtualization |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Choose Azure IoT Edge gateway patterns for devices | https://learn.microsoft.com/en-us/azure/iot-edge/iot-edge-as-gateway |
| Design offline operation patterns for Azure IoT Edge | https://learn.microsoft.com/en-us/azure/iot-edge/offline-capabilities |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review Azure IoT Edge limits and restrictions | https://learn.microsoft.com/en-us/azure/iot-edge/iot-edge-limits-and-restrictions |

### Security
| Topic | URL |
|-------|-----|
| Deploy confidential computing applications as IoT Edge modules | https://learn.microsoft.com/en-us/azure/iot-edge/deploy-confidential-applications |
| Configure authentication for IoT Edge downstream devices | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-authenticate-downstream-device |
| Create and install test certificates for Azure IoT Edge | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-create-test-certificates |
| Manage certificates for secure Azure IoT Edge devices | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-manage-device-certificates |
| Provision Linux IoT Edge device using X.509 certificates | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-single-device-linux-x509 |
| Configure certificate-based security for Azure IoT Edge | https://learn.microsoft.com/en-us/azure/iot-edge/iot-edge-certs |
| Understand and configure security principles for IoT Edge for Linux on Windows | https://learn.microsoft.com/en-us/azure/iot-edge/iot-edge-for-linux-on-windows-security |
| Configure EST server security for Azure IoT Edge devices | https://learn.microsoft.com/en-us/azure/iot-edge/tutorial-configure-est-server |
| Secure IoT Edge traffic with Private Link and endpoints | https://learn.microsoft.com/en-us/azure/iot-edge/using-private-link |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure IoT Edge device settings via config.toml | https://learn.microsoft.com/en-us/azure/iot-edge/configure-device |
| Enable GPU acceleration for IoT Edge for Linux on Windows | https://learn.microsoft.com/en-us/azure/iot-edge/gpu-acceleration |
| Configure and access Azure IoT Edge built-in metrics | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-access-built-in-metrics |
| Configure dTPM access for IoT Edge on Windows | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-access-dtpm |
| Configure IoT Edge modules to use host local storage | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-access-host-storage-from-module |
| Publish custom IoT Edge module metrics alongside built-in metrics | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-add-custom-metrics |
| Configure metrics-collector to send IoT Edge metrics to Azure Monitor | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-collect-and-transport-metrics |
| Customize the Azure IoT Edge API proxy module for gateways | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-configure-api-proxy-module |
| Configure EFLOW networking for DMZ and multiple NICs | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-configure-iot-edge-for-linux-on-windows-iiot-dmz |
| Configure IoT Edge module build and deployment options | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-configure-module-build-options |
| Attach and configure multiple NICs for EFLOW VM | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-configure-multiple-nics |
| Configure proxy settings for Azure IoT Edge devices | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-configure-proxy-support |
| Configure downstream devices to connect via IoT Edge gateway | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-connect-downstream-device |
| Configure nested Azure IoT Edge device hierarchies | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-connect-downstream-iot-edge-device |
| Configure USB over IP connectivity to EFLOW VM | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-connect-usb-devices |
| Configure Azure Monitor log alerts for IoT Edge metrics | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-create-alerts |
| Configure Azure IoT Edge as a transparent gateway | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-create-transparent-gateway |
| Create and configure virtual switches for EFLOW | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-create-virtual-switch |
| Configure symmetric key DPS provisioning for EFLOW | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-devices-at-scale-linux-on-windows-symmetric |
| Configure TPM-based DPS provisioning for EFLOW devices | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-devices-at-scale-linux-on-windows-tpm |
| Autoprovision EFLOW IoT Edge devices at scale with X.509 and DPS | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-devices-at-scale-linux-on-windows-x509 |
| Configure large-scale IoT Edge provisioning with X.509 certificates | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-devices-at-scale-linux-x509 |
| Provision a single EFLOW IoT Edge device with symmetric keys | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-single-device-linux-on-windows-symmetric |
| Provision EFLOW IoT Edge device using X.509 certificates | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-single-device-linux-on-windows-x509 |
| Provision a single Linux IoT Edge device with symmetric keys | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-provision-single-device-linux-symmetric |
| Share Windows folders with the EFLOW virtual machine | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-share-windows-folder-to-vm |
| Configure IoT Edge module container createOptions | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-use-create-options |
| Configure networking between Windows host and EFLOW virtual machine | https://learn.microsoft.com/en-us/azure/iot-edge/iot-edge-for-linux-on-windows-networking |
| Author deployment manifests and routes for IoT Edge | https://learn.microsoft.com/en-us/azure/iot-edge/module-composition |
| Configure edgeAgent and edgeHub module twin properties | https://learn.microsoft.com/en-us/azure/iot-edge/module-edgeagent-edgehub |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use IoT Edge agent direct methods for remote management | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-edgeagent-direct-method |
| Retrieve and upload Azure IoT Edge logs via direct methods | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-retrieve-iot-edge-logs |
| Develop and package custom Azure IoT Edge modules | https://learn.microsoft.com/en-us/azure/iot-edge/module-development |
| Use EFLOW PowerShell functions to manage IoT Edge | https://learn.microsoft.com/en-us/azure/iot-edge/reference-iot-edge-for-linux-on-windows-functions |

### Deployment
| Topic | URL |
|-------|-----|
| Set up CI/CD pipelines for Azure IoT Edge modules with Azure DevOps | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-continuous-integration-continuous-deployment |
| Deploy IoT Edge modules at scale using CLI | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-deploy-cli-at-scale |
| Deploy IoT Edge modules with Azure CLI manifests | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-deploy-modules-cli |
| Install Azure IoT Edge on Kubernetes with KubeVirt | https://learn.microsoft.com/en-us/azure/iot-edge/how-to-install-iot-edge-kubernetes |
| Check supported platforms for IoT Edge on Windows | https://learn.microsoft.com/en-us/azure/iot-edge/iot-edge-for-linux-on-windows-support |
| Manage IoT Edge automatic deployments for device groups | https://learn.microsoft.com/en-us/azure/iot-edge/module-deployment-monitoring |
| Check supported platforms for Azure IoT Edge deployment | https://learn.microsoft.com/en-us/azure/iot-edge/support |