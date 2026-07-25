---
name: azure-defender-for-iot
description: Expert knowledge for Azure Defender For Iot development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring OT sensors/micro agents, traffic mirroring, Sentinel/SIEM integration, RBAC, or SSL/TLS certs, and other Azure Defender For Iot related development tasks. Not for Azure Defender For Cloud (use azure-defender-for-cloud), Azure Security (use azure-security), Azure Sentinel (use azure-sentinel), Azure IoT Hub (use azure-iot-hub).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Defender For Iot Skill

This skill provides expert guidance for Azure Defender For Iot. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L47 | Diagnosing and resolving Defender for IoT issues: CIS benchmark findings, micro agent problems, OT sensor install/health, and investigating alert types and responses. |
| Best Practices | L48-L53 | Designing OT monitoring architectures and preparing industrial sites, including sensor placement, network topology, and deployment planning for Defender for IoT. |
| Decision Making | L54-L66 | Guidance on planning and choosing OT mirroring methods, appliances, licensing/billing, tracking versions, and transitioning from on‑prem to cloud or retired Defender for IoT components. |
| Architecture & Design Patterns | L67-L73 | OT network architectures for connecting sensors to Azure, sample connectivity models, and mapping Defender for IoT components to Purdue OT network layers. |
| Limits & Quotas | L74-L83 | Data residency, retention limits, networking/port requirements, supported OT sensor/virtual appliance versions, and hardware/software specs for Defender for IoT deployments. |
| Security | L84-L102 | Security alerts, recommendations, auth, and access control for Defender for IoT: configuring alerts/micro agents, SSL/TLS and CA certs, RBAC/roles, SSO, and Zero Trust for OT sensors and IoT Hub. |
| Configuration | L103-L132 | Configuring and managing Defender for IoT micro agents and OT sensors: installation, dependencies, monitoring modes, connectivity, alert forwarding, maintenance, and Azure/Defender for Endpoint integration. |
| Integrations & Coding Patterns | L133-L164 | Integrating Defender for IoT with APIs, SIEMs, firewalls, ServiceNow, Sentinel, and configuring traffic mirroring and micro agent patterns for OT monitoring and automation |
| Deployment | L165-L190 | Guides for deploying, upgrading, and moving Defender for IoT OT sensors and micro agents, including hardware/VM appliance setups, traffic mirroring, and hybrid/air-gapped planning. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Investigate Defender IoT CIS benchmark recommendations | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-investigate-cis-benchmark |
| Troubleshoot Defender for IoT micro agent issues | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/troubleshoot-defender-micro-agent |
| Reference Microsoft Defender for IoT alert types | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/alert-engine-messages |
| Investigate and respond to Defender for IoT alerts | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/alerts |
| Troubleshoot Microsoft Defender for IoT OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-troubleshoot-sensor |
| Validate Defender for IoT OT sensor software installation | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/post-install-validation-ot-software |
| Interpret Defender for IoT sensor health messages | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/sensor-health-messages |

### Best Practices
| Topic | URL |
|-------|-----|
| Plan OT monitoring architecture with Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/plan-corporate-monitoring |
| Prepare OT sites and sensor placement for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/plan-prepare-deploy |

### Decision Making
| Topic | URL |
|-------|-----|
| Review Defender IoT micro agent feature support and retirement | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/edge-security-module-deprecation |
| Choose OT traffic mirroring methods for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/traffic-mirroring-methods |
| Decide between SPAN, RSPAN, ERSPAN for OT mirroring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/traffic-mirroring-methods |
| Plan Defender for IoT billing and site licensing | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/billing |
| Choose and manage Defender for IoT licenses | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/license-and-trial-license-extention |
| Select appropriate OT appliances for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-appliance-sizing |
| Plan for Defender for IoT on-premises console retirement | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/on-premises-management-console-retirement |
| Plan transition from on-premises to cloud Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/transition-on-premises-management-console-to-cloud |
| Track Defender for IoT OT software versions and support | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/release-notes |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Select architectures to connect OT sensors to Azure | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/architecture-connections |
| Use sample OT network connectivity models for sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/sample-connectivity-models |
| Map Defender for IoT to Purdue OT network layers | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/understand-network-architecture |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Defender for IoT data residency mapping | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-data-processing |
| Networking requirements and ports for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/networking-requirements |
| Review catalog of preconfigured OT monitoring appliances | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-pre-configured-appliances |
| Check system requirements for virtual OT appliances | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-virtual-appliances |
| Understand Defender for IoT data retention limits | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/references-data-retention |
| Review archived Defender for IoT OT sensor versions | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/release-notes-ot-monitoring-sensor-archive |

### Security
| Topic | URL |
|-------|-----|
| Use Defender micro agent built-in security alerts | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-agent-based-security-alerts |
| Define custom Defender for IoT Hub alerts | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-customizable-security-alerts |
| Apply Defender for IoT Hub security recommendations | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-recommendations |
| Use Defender for IoT Hub built-in alerts | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-security-alerts |
| Use ThreadX micro agent alerts and recommendations | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-threadx-security-alerts-recommendations |
| Call Defender for IoT sensor authentication APIs | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/api/sensor-auth-apis |
| Meet SSL/TLS certificate requirements for OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/best-practices/certificate-requirements |
| Manage Defender for IoT users and roles | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/manage-users-overview |
| Configure Azure user permissions for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/manage-users-portal |
| Manage on-premises users on Defender for IoT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/manage-users-sensor |
| Apply Zero Trust monitoring to OT networks with Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/monitor-zero-trust |
| Create CA-signed SSL/TLS certificates for OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/create-ssl-certificates |
| Map Azure RBAC roles to Defender for IoT actions | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/roles-azure |
| Configure on-premises Defender for IoT user roles | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/roles-on-premises |
| Set up SSO with Entra ID for IoT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/set-up-sso |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Defender for IoT micro agent behavior | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-micro-agent-configuration |
| Review Linux OS dependencies for Defender micro agent | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/concept-micro-agent-linux-dependencies |
| Configure PAM auditing for Defender IoT sign-in events | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/configure-pam-to-audit-sign-in-events |
| Configure DMI decoder for Defender micro agent | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-configure-dmi-decoder |
| Configure Defender IoT micro agent twin properties | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-configure-micro-agent-twin |
| Install and authenticate Defender IoT micro agent for Edge | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-install-micro-agent-for-edge |
| Configure Defender IoT micro agent for Eclipse ThreadX | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-threadx-security-module |
| Back up and restore Defender for IoT OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/back-up-restore-sensor |
| Use Defender for IoT OT sensor CLI commands | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/cli-ot-sensor |
| Configure OT active monitoring methods in Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/configure-active-monitoring |
| Configure reverse DNS lookup for OT active monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/configure-reverse-dns-lookup |
| Configure OT sensor settings via Azure portal | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/configure-sensor-settings-portal |
| Configure Windows Endpoint Monitoring for OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/configure-windows-endpoint-monitoring |
| Configure Defender for IoT OT sensor proxy connections | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/connect-sensors |
| Enable enterprise IoT security in Defender for Endpoint | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/eiot-defender-for-endpoint |
| Configure OT plans and sensors in Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/getting-started |
| Configure OT sensor alert forwarding to external systems | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-forward-alert-information-to-partners |
| Import additional OT device data into sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-import-device-information |
| Perform OT sensor maintenance via sensor console GUI | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-manage-individual-sensors |
| Manage Defender for IoT OT sensors in Azure | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-manage-sensors-on-the-cloud |
| Set up SNMP MIB health monitoring for OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-set-up-snmp-mib-monitoring |
| Maintain threat intelligence packages on OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/how-to-work-with-threat-intelligence-packages |
| Onboard OT sensors to Defender for IoT in Azure | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/onboard-sensors |
| Configure and activate Microsoft Defender for IoT OT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/activate-deploy-sensor |
| Configure OT sensor connectivity and firewall endpoints | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/provision-cloud-management |
| Audit and track Defender for IoT user activity | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/track-user-activity |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Defender micro agent API for Eclipse ThreadX | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/threadx-security-module-api |
| Manage OT sensor alerts using Defender for IoT APIs | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/api/sensor-alert-apis |
| Manage OT sensor inventory via Defender for IoT APIs | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/api/sensor-inventory-apis |
| Access OT vulnerability data via Defender for IoT APIs | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/api/sensor-vulnerability-apis |
| Automate OT sensor disconnection alerts with Sentinel playbooks | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/automate-sensor-disconnection-alerts |
| Enrich OT sensor data using Windows endpoint script | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/detect-windows-endpoints-script |
| Choose and configure Defender for IoT partner integrations | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrate-overview |
| Integrate ArcSight with Defender for IoT alert forwarding | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrations/arcsight |
| Send Defender for IoT alerts to LogRhythm SIEM | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrations/logrhythm |
| Integrate RSA NetWitness with Defender for IoT alerts | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrations/netwitness |
| Connect on-prem Defender for IoT sensors to Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrations/on-premises-sentinel |
| Stream Defender for IoT cloud alerts to third-party SIEMs | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrations/send-cloud-data-to-partners |
| Configure legacy ServiceNow integration for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/integrations/service-now-legacy |
| Use Sentinel solution to investigate Defender for IoT threats | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/iot-advanced-threat-monitoring |
| Connect Defender for IoT with Microsoft Sentinel via data connector | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/iot-solution |
| Integrate with Microsoft Defender for IoT REST APIs | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/references-work-with-defender-for-iot-apis |
| Configure Cisco ERSPAN for Defender for IoT sensors | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/traffic-mirroring/configure-mirror-erspan |
| Use ESXi vSwitch promiscuous mode for OT traffic mirroring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/traffic-mirroring/configure-mirror-esxi |
| Use Hyper-V vSwitch promiscuous mode for OT mirroring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/traffic-mirroring/configure-mirror-hyper-v |
| Configure Cisco RSPAN mirroring for OT monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/traffic-mirroring/configure-mirror-rspan |
| Configure Cisco SPAN ports for Defender for IoT traffic mirroring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/traffic-mirroring/configure-mirror-span |
| Integrate CyberArk with Defender for IoT for credential security | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-cyberark |
| Integrate Forescout with Defender for IoT for OT visibility | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-forescout |
| Integrate Fortinet firewalls with Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-fortinet |
| Integrate Palo Alto firewalls with Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-palo-alto |
| Integrate IBM QRadar with Defender for IoT alerts | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-qradar |
| Integrate ServiceNow Operational Technology Manager with Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-servicenow |
| Integrate Defender for IoT OT data with Splunk | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/tutorial-splunk |

### Deployment
| Topic | URL |
|-------|-----|
| Provision Defender IoT micro agent with DPS and X.509 | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-provision-micro-agent |
| Move Defender IoT iotsecuritysolutions resource between regions | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/how-to-region-move |
| Upgrade Defender for IoT micro agent on Linux devices | https://learn.microsoft.com/en-us/azure/defender-for-iot/device-builders/upgrade-micro-agent |
| Select and use OT monitoring appliances for Defender for IoT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/ |
| Deploy Dell PowerEdge R350 for OT sensor monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/dell-poweredge-r350-e1800 |
| Deploy Dell PowerEdge R360 for OT sensor monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/dell-poweredge-r360-e1800 |
| Deploy Dell PowerEdge R660 for OT sensor monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/dell-poweredge-r660 |
| Deploy Heptagon YB3x appliance for OT monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/heptagon-yb3x |
| Use HPE ProLiant DL20 Gen 11 (4SFF) for OT monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl20-gen-11 |
| Use HPE ProLiant DL20 Gen 11 (2LFF) for OT monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl20-gen-11-nhp-2lff |
| Use legacy HPE ProLiant DL20 for enterprise OT monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl20-legacy |
| Use HPE ProLiant DL20 Gen10 Plus for enterprise OT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl20-plus-enterprise |
| Use HPE ProLiant DL20 Gen10 Plus (2LFF) for SMB OT | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl20-plus-smb |
| Deploy Defender for IoT on HPE ProLiant DL360 | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl360 |
| Deploy Defender for IoT on HPE ProLiant DL360 Gen 11 | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/hpe-proliant-dl360-gen11 |
| Deploy Defender for IoT OT sensor VM on Hyper-V Gen 2 | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/virtual-sensor-hyper-v |
| Deploy Defender for IoT OT sensor VM on VMware ESXi | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/virtual-sensor-vmware |
| Deploy YS-techsystems YS-FIT2 for OT monitoring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/appliance-catalog/ys-techsystems-ys-fit2 |
| Plan hybrid or air-gapped Defender for IoT deployments | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/air-gapped-deploy |
| Install and initially configure Defender for IoT OT sensor software | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/install-software-ot-sensor |
| Deploy Defender for IoT for OT monitoring environments | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/ot-deploy/ot-deploy-path |
| Deploy OT sensors and configure traffic mirroring | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/traffic-mirroring/set-up-traffic-mirroring |
| Update Defender for IoT OT sensor software versions | https://learn.microsoft.com/en-us/azure/defender-for-iot/organizations/update-ot-software |