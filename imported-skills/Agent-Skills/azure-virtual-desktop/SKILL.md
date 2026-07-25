---
name: azure-virtual-desktop
description: Expert knowledge for Azure Virtual Desktop development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when designing AVD host pools, FSLogix profiles, autoscale, WebRTC/Teams optimization, or secure SSO/MFA, and other Azure Virtual Desktop related development tasks. Not for Azure Virtual Machines (use azure-virtual-machines), Azure Dev Box (use azure-dev-box), Azure Lab Services (use azure-lab-services), Azure VMware Solution (use azure-vmware-solution).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Virtual Desktop Skill

This skill provides expert guidance for Azure Virtual Desktop. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L53 | Diagnosing and fixing AVD issues: agent updates, autoscale, connectivity/FQDN, connection quality logs, graphics/Teams performance, session host health, hybrid onboarding, and Log Analytics queries. |
| Best Practices | L54-L64 | Best practices for autoscaling, host pool validation, proxy usage, Start VM on Connect, Windows multi-session configuration, and resolving Azure Advisor/FAQ guidance for Azure Virtual Desktop. |
| Decision Making | L65-L80 | Guidance on planning and choosing AVD deployment models, autoscale, host pool and session host management, storage, data locations, licensing, costs, ESU, and extended/local zones. |
| Architecture & Design Patterns | L81-L88 | Design patterns for AVD app delivery, stateless hosts, DR, FSLogix profile containers, and automated scaling with Automation/Logic Apps. |
| Limits & Quotas | L89-L94 | Guidance on RDP bandwidth requirements and optimizing Microsoft Teams (audio/video, collaboration features) performance and configuration in Azure Virtual Desktop. |
| Security | L95-L115 | Securing Azure Virtual Desktop: SSO (Entra ID/AD FS), MFA/Conditional Access, RBAC, external identities, managed identities, redirection controls, watermarking, screen capture protection, and Purview forensic setup. |
| Configuration | L116-L175 | Configuring AVD host pools, images, autoscale, networking, RDP/RemoteApp features, redirection, Teams/Office, licensing, monitoring, and client settings for optimized deployments. |
| Integrations & Coding Patterns | L176-L182 | Managing AVD via CLI/PowerShell, integrating partner App Attach delivery, enabling WebRTC multimedia redirection, and launching resources using custom URI schemes. |
| Deployment | L183-L192 | Guides for deploying and migrating AVD: adding session hosts, moving from classic, hybrid/on-prem setups, regional host pools, region moves, and client/MMR deployment via Intune/ConfigMgr. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Monitor and troubleshoot AVD agent updates with logs | https://learn.microsoft.com/en-us/azure/virtual-desktop/agent-updates-diagnostics |
| Test and troubleshoot MSIX packages for App Attach | https://learn.microsoft.com/en-us/azure/virtual-desktop/app-attach-test-msix-packages |
| Monitor and troubleshoot Azure Virtual Desktop autoscale with Insights | https://learn.microsoft.com/en-us/azure/virtual-desktop/autoscale-monitor-operations-insights |
| Validate Azure Virtual Desktop FQDN and endpoint connectivity | https://learn.microsoft.com/en-us/azure/virtual-desktop/check-access-validate-required-fqdn-endpoint |
| Analyze and troubleshoot AVD connection quality | https://learn.microsoft.com/en-us/azure/virtual-desktop/connection-latency |
| Collect and query AVD connection quality logs | https://learn.microsoft.com/en-us/azure/virtual-desktop/connection-quality-monitoring |
| Use diagnostics and Log Analytics for AVD issues | https://learn.microsoft.com/en-us/azure/virtual-desktop/diagnostics-log-analytics |
| Diagnose graphics performance issues with RemoteFX counters | https://learn.microsoft.com/en-us/azure/virtual-desktop/remotefx-graphics-performance-counters |
| Interpret AVD session host statuses and health checks | https://learn.microsoft.com/en-us/azure/virtual-desktop/session-host-status-health-checks |
| Interpret AVD session host statuses and health checks | https://learn.microsoft.com/en-us/azure/virtual-desktop/session-host-status-health-checks |
| Use Log Analytics queries to diagnose session host updates | https://learn.microsoft.com/en-us/azure/virtual-desktop/session-host-update-diagnostics |
| Troubleshoot Azure Virtual Desktop Hybrid onboarding failures | https://learn.microsoft.com/en-us/azure/virtual-desktop/troubleshoot-azure-virtual-desktop-hybrid |
| Troubleshoot Microsoft Teams on Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/troubleshoot-teams |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply autoscale best practices for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/autoscale-faq |
| Resolve Azure Advisor recommendations for AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/azure-advisor-recommendations |
| Configure Azure Virtual Desktop validation host pools | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-validation-environment |
| Apply Azure Virtual Desktop FAQ best practices | https://learn.microsoft.com/en-us/azure/virtual-desktop/faq |
| Apply proxy server guidelines for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/proxy-server-support |
| Start VM on Connect FAQ and usage best practices | https://learn.microsoft.com/en-us/azure/virtual-desktop/start-virtual-machine-connect-faq |
| Apply best practices for Windows Enterprise multi-session | https://learn.microsoft.com/en-us/azure/virtual-desktop/windows-multisession-faq |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and tune Azure Virtual Desktop autoscale plans | https://learn.microsoft.com/en-us/azure/virtual-desktop/autoscale-scenarios |
| Use Azure Extended Zones with Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/azure-extended-zones |
| Plan Azure Virtual Desktop on Azure Local | https://learn.microsoft.com/en-us/azure/virtual-desktop/azure-local-overview |
| Understand Azure Virtual Desktop data locations | https://learn.microsoft.com/en-us/azure/virtual-desktop/data-locations |
| Choose Azure Virtual Desktop host pool management | https://learn.microsoft.com/en-us/azure/virtual-desktop/host-pool-management-approaches |
| Estimate costs for Azure Virtual Desktop Insights | https://learn.microsoft.com/en-us/azure/virtual-desktop/insights-costs |
| Select licensing options for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/licensing |
| Choose management tools for Azure Virtual Desktop session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/management |
| Choose Azure Virtual Desktop deployment models | https://learn.microsoft.com/en-us/azure/virtual-desktop/organization-internal-external-commercial-purposes-recommendations |
| Choose Azure storage options for FSLogix profiles on AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/store-fslogix-profile |
| Estimate and plan Azure Virtual Desktop costs | https://learn.microsoft.com/en-us/azure/virtual-desktop/understand-estimate-costs |
| Plan Windows 10 ESU for Azure Virtual Desktop deployments | https://learn.microsoft.com/en-us/azure/virtual-desktop/understanding-extended-security-updates |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Use ephemeral OS disks for stateless AVD workloads | https://learn.microsoft.com/en-us/azure/virtual-desktop/deploy/session-hosts/ephemeral-os-disks |
| Design disaster recovery architecture for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/disaster-recovery-concepts |
| Design AVD user profile management with FSLogix containers | https://learn.microsoft.com/en-us/azure/virtual-desktop/fslogix-profile-containers |
| Use Automation and Logic Apps to scale AVD session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/scaling-automation-logic-apps |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand RDP bandwidth needs for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/rdp-bandwidth |
| Use Microsoft Teams features on Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/teams-supported-features |

### Security
| Topic | URL |
|-------|-----|
| Control clipboard direction and data types in AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/clipboard-transfer-direction-data-types |
| Configure AD FS single sign-on for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-adfs-sso |
| Configure managed identities and permissions for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-managed-identity |
| Configure Microsoft Entra ID SSO for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-single-sign-on |
| Configure context-based redirection policies in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/context-based-redirections-avd |
| Implement delegated administrative access in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/delegated-access-virtual-desktop |
| Set up Kerberos KDC proxy for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/key-distribution-center-proxy |
| Configure Azure Virtual Desktop access for external identities | https://learn.microsoft.com/en-us/azure/virtual-desktop/provide-access-external-identities |
| Onboard AVD session hosts to Microsoft Purview forensic evidence | https://learn.microsoft.com/en-us/azure/virtual-desktop/purview-forensic-evidence |
| Use built-in Azure RBAC roles for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/rbac |
| Configure WebAuthn redirection for passwordless AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-webauthn |
| Configure Entra ID authentication for Azure Virtual Desktop RDP | https://learn.microsoft.com/en-us/azure/virtual-desktop/require-authentication-using-microsoft-entra-id |
| Configure screen capture protection for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/screen-capture-protection |
| Apply security recommendations to Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/security-recommendations |
| Assign RBAC and Entra roles to AVD service principals | https://learn.microsoft.com/en-us/azure/virtual-desktop/service-principal-assign-roles |
| Enforce MFA for Azure Virtual Desktop with Conditional Access | https://learn.microsoft.com/en-us/azure/virtual-desktop/set-up-mfa |
| Configure watermarking to protect Azure Virtual Desktop sessions | https://learn.microsoft.com/en-us/azure/virtual-desktop/watermarking |

### Configuration
| Topic | URL |
|-------|-----|
| Add Azure Virtual Desktop administrative template to Group Policy and Intune | https://learn.microsoft.com/en-us/azure/virtual-desktop/administrative-template |
| Create MSIX images for Azure Virtual Desktop App Attach | https://learn.microsoft.com/en-us/azure/virtual-desktop/app-attach-create-msix-image |
| Add and manage App Attach apps in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/app-attach-setup |
| Apply Windows licensing to Azure Virtual Desktop session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/apply-windows-license |
| Create and assign autoscale scaling plans for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/autoscale-create-assign-scaling-plan |
| Configure diagnostics for Azure Virtual Desktop autoscale | https://learn.microsoft.com/en-us/azure/virtual-desktop/autoscale-diagnostics |
| Deploy and access Entra-joined AVD session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/azure-ad-joined-session-hosts |
| Configure Azure fabric communication IPs for AVD and Windows 365 | https://learn.microsoft.com/en-us/azure/virtual-desktop/azurecommunicationips |
| Configure Configuration Manager updates for AVD multi-session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-automatic-updates |
| Configure Azure Virtual Desktop host pool load balancing | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-host-pool-load-balancing |
| Configure RDP Shortpath transport for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-rdp-shortpath |
| Configure session lock behavior in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/configure-session-lock-behavior |
| Create and use AVD custom image templates | https://learn.microsoft.com/en-us/azure/virtual-desktop/create-custom-image-templates |
| Configure custom image templates for AVD session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/custom-image-templates |
| Customize Azure Virtual Desktop user feed via portal and PowerShell | https://learn.microsoft.com/en-us/azure/virtual-desktop/customize-feed-for-virtual-desktop-users |
| Set custom RDP properties on Azure Virtual Desktop host pools | https://learn.microsoft.com/en-us/azure/virtual-desktop/customize-rdp-properties |
| Enroll Azure subscriptions in AVD per-user access pricing | https://learn.microsoft.com/en-us/azure/virtual-desktop/enroll-per-user-access-pricing |
| Increase AVD RDP chroma subsampling to 4:4:4 | https://learn.microsoft.com/en-us/azure/virtual-desktop/graphics-chroma-value-increase-4-4-4 |
| Enable GPU-accelerated rendering and encoding in AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/graphics-enable-gpu-acceleration |
| Enable and configure Azure Virtual Desktop Insights | https://learn.microsoft.com/en-us/azure/virtual-desktop/insights |
| Install Microsoft 365 Apps on AVD custom images | https://learn.microsoft.com/en-us/azure/virtual-desktop/install-office-on-wvd-master-image |
| Configure Windows 10 language packs on Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/language-packs |
| Use MSIXMGR tool parameters for AVD App Attach workflows | https://learn.microsoft.com/en-us/azure/virtual-desktop/msixmgr-tool-syntax-description |
| Configure multimedia redirection for Azure Virtual Desktop sessions | https://learn.microsoft.com/en-us/azure/virtual-desktop/multimedia-redirection-video-playback-calls |
| Launch OneDrive automatically with AVD RemoteApps | https://learn.microsoft.com/en-us/azure/virtual-desktop/onedrive-remoteapp |
| Configure preferred application group type for pooled AVD host pools | https://learn.microsoft.com/en-us/azure/virtual-desktop/preferred-application-group-type |
| Set up Private Link endpoints for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/private-link-setup |
| Publish applications with RemoteApp in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/publish-applications-stream-remoteapp |
| Configure supported RDP properties for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/rdp-properties |
| Configure QoS policies for Azure Virtual Desktop RDP | https://learn.microsoft.com/en-us/azure/virtual-desktop/rdp-quality-of-service-qos |
| Understand and plan RDP Shortpath for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/rdp-shortpath |
| Configure audio and video redirection over RDP for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-audio-video |
| Configure RDP camera and video redirection | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-camera-webcam-video-capture |
| Configure RDP clipboard redirection settings | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-clipboard |
| Configure RDP drive and storage redirection | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-drives-storage |
| Configure RDP location redirection for AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-location |
| Configure MTP/PTP device redirection over RDP | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-plug-play-mtp-ptp |
| Configure printer redirection in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-printers |
| Configure serial and COM port redirection over RDP | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-serial-com-ports |
| Configure smart card redirection for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-smart-cards |
| Configure USB redirection on Windows RDP clients | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-configure-usb |
| Configure peripheral and resource redirection over RDP for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/redirection-remote-desktop-protocol |
| Use advanced features of the Windows Remote Desktop client for AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/remote-desktop-client/client-features-windows-msrdc |
| Connect to Azure Virtual Desktop using the Windows Remote Desktop client | https://learn.microsoft.com/en-us/azure/virtual-desktop/remote-desktop-client/connect-windows-cloud-services |
| Enable enhanced RemoteApp windowing in Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/remoteapp-enhancements |
| Allow required FQDNs and endpoints for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/required-fqdn-endpoint |
| Configure scheduled agent updates for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/scheduled-agent-updates |
| Configure session host update for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/session-host-update-configure |
| Set preferred application group type on AVD host pools | https://learn.microsoft.com/en-us/azure/virtual-desktop/set-preferred-application-group-type |
| Prepare and upload a custom VHD image for AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/set-up-customize-master-image |
| Build a golden image for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/set-up-golden-image |
| Set up Automation and Logic Apps scaling for AVD session hosts | https://learn.microsoft.com/en-us/azure/virtual-desktop/set-up-scaling-script |
| Configure Azure Service Health alerts for AVD | https://learn.microsoft.com/en-us/azure/virtual-desktop/set-up-service-alerts |
| Configure Start VM on Connect for Azure Virtual Desktop host pools | https://learn.microsoft.com/en-us/azure/virtual-desktop/start-virtual-machine-connect |
| Configure Microsoft Teams optimizations on Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/teams-on-avd |
| Configure Windows 11 language packs on Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/windows-11-language-packs |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Azure CLI and PowerShell modules to manage Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/cli-powershell |
| Integrate WebRTC calling apps with AVD multimedia redirection | https://learn.microsoft.com/en-us/azure/virtual-desktop/multimedia-redirection-developer-integration |
| Use URI schemes with the AVD Remote Desktop client | https://learn.microsoft.com/en-us/azure/virtual-desktop/uri-scheme |

### Deployment
| Topic | URL |
|-------|-----|
| Automatically migrate from AVD (classic) to Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/automatic-migration |
| Deploy Azure Virtual Desktop Hybrid On-premises | https://learn.microsoft.com/en-us/azure/virtual-desktop/deploy-azure-virtual-desktop-hybrid |
| Deploy Azure Virtual Desktop MMR Insider extension via Intune | https://learn.microsoft.com/en-us/azure/virtual-desktop/deploy-insider-extension |
| Manually migrate from AVD (classic) to Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/virtual-desktop/manual-migration |
| Move Azure Virtual Desktop resources between Azure regions | https://learn.microsoft.com/en-us/azure/virtual-desktop/move-resources |
| Deploy and manage Azure Virtual Desktop regional host pools | https://learn.microsoft.com/en-us/azure/virtual-desktop/regional-host-pools |
| Deploy Windows Remote Desktop client per-user via Intune or Configuration Manager | https://learn.microsoft.com/en-us/azure/virtual-desktop/remote-desktop-client/install-windows-client-per-user |