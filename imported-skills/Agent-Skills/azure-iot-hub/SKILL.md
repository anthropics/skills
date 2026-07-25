---
name: azure-iot-hub
description: Expert knowledge for Azure IoT Hub development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using IoT Hub/DPS device provisioning, twins/methods/jobs, routing/endpoints, Device Update, or Cosmos DB sinks, and other Azure IoT Hub related development tasks. Not for Azure IoT (use azure-iot), Azure IoT Central (use azure-iot-central), Azure IoT Edge (use azure-iot-edge), Azure Defender For Iot (use azure-defender-for-iot).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure IoT Hub Skill

This skill provides expert guidance for Azure IoT Hub. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L53 | Diagnosing and fixing IoT Hub/DPS connectivity, routing, proxy, and storage issues; interpreting error codes and collecting/using Device Update and device diagnostic logs. |
| Best Practices | L54-L63 | Best practices for secure, scalable IoT Hub/DPS deployments: device provisioning at scale, OEM security, cert renewal/ADR, resilient reconnection, auto device config, and IoT Hub hardening. |
| Decision Making | L64-L76 | Guidance for choosing IoT Hub vs alternatives, DR usage, routing options, C2D/D2C patterns, pricing and tiers, and methods for monitoring device connections. |
| Architecture & Design Patterns | L77-L83 | Design patterns for DPS lifecycle/HA/DR, VNet connectivity, secure device streams, and reliably persisting ordered IoT Hub events with Cosmos DB. |
| Limits & Quotas | L84-L90 | Limits, quotas, and throttling for IoT Hub, Device Provisioning Service, and Device Update, including per‑service caps, scaling behavior, and what happens when limits are exceeded. |
| Security | L91-L129 | Securing IoT Hub, DPS, and Device Update: auth (Entra ID, RBAC, SAS, X.509), cert lifecycle, key rotation, TLS/ciphers, network/IP controls, private endpoints, and policy/compliance. |
| Configuration | L130-L165 | Configuring IoT Hub, DPS, and Device Update: enroll devices, set allocation/IP policies, manage twins, jobs, routing, endpoints, file upload, certificates, and monitor via metrics/logs and VS Code. |
| Integrations & Coding Patterns | L166-L191 | Patterns and code samples for connecting devices/DPUs to IoT Hub/DPS (MQTT/HTTPS/AMQP), managing identities, twins, methods, jobs, file upload, and message formats/endpoints. |
| Deployment | L192-L204 | Deploying and updating IoT devices and hubs: Device Update setup (image/package/delta/proxy), platform support, regional failover, and IoT Hub migration and job scheduling. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and fix common Azure DPS provisioning errors | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-troubleshoot-dps |
| Reference monitoring data for Azure IoT DPS | https://learn.microsoft.com/en-us/azure/iot-dps/monitor-iot-dps-reference |
| Use Agent Check to diagnose missing Device Update devices | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-agent-check |
| Use Device Update diagnostics, error codes, and logs | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-diagnostics |
| Interpret Device Update for IoT Hub error codes | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-error-codes |
| Collect and review Device Update diagnostic logs remotely | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-log-collection |
| Resolve proxy update import errors in Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-proxy-update-troubleshooting |
| Diagnose and fix common Device Update issues | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/troubleshoot-device-update |
| Fix storage permission errors when importing Device Updates | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/troubleshoot-storage |
| Collect device debug logs using IoT SDKs | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-collect-device-logs |
| Diagnose and fix Azure IoT Hub device connectivity | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-troubleshoot-connectivity |
| Resolve Azure IoT Hub error codes | https://learn.microsoft.com/en-us/azure/iot-hub/troubleshoot-error-codes |
| Troubleshoot Azure IoT Hub message routing issues | https://learn.microsoft.com/en-us/azure/iot-hub/troubleshoot-message-routing |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply DPS best practices for large-scale IoT deployments | https://learn.microsoft.com/en-us/azure/iot-dps/concepts-deploy-at-scale |
| Implement OEM security practices for DPS-enabled devices | https://learn.microsoft.com/en-us/azure/iot-dps/concepts-device-oem-security-practices |
| Plan and execute IoT certificate renewal with ADR | https://learn.microsoft.com/en-us/azure/iot-hub/concept-certificate-renewal |
| Design resilient Azure IoT Hub device reconnection | https://learn.microsoft.com/en-us/azure/iot-hub/concepts-manage-device-reconnections |
| Apply IoT Hub automatic device configuration best practices | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-configuration-best-practices |
| Apply security best practices to Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/secure-azure-iot-hub |

### Decision Making
| Topic | URL |
|-------|-----|
| Decide when to disable IoT Hub disaster recovery | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-disable-dr |
| Decide between Azure IoT Hub and Event Hubs | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-compare-event-hubs |
| Choose IoT Hub cloud-to-device communication option | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-c2d-guidance |
| Choose IoT Hub device-to-cloud communication option | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-d2c-guidance |
| Understand Azure IoT Hub pricing and metering | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-pricing |
| Decide between IoT Hub routing and Event Grid | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-event-grid-routing-comparison |
| Select the right Azure IoT Hub tier and scale | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-scaling |
| Select and upgrade Azure IoT Hub tier and size | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-upgrade |
| Choose IoT Hub device connection monitoring method | https://learn.microsoft.com/en-us/azure/iot-hub/monitor-device-connection-state |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Plan DPS device lifecycle and reprovisioning policies | https://learn.microsoft.com/en-us/azure/iot-dps/concepts-device-reprovision |
| Design DPS high availability and disaster recovery | https://learn.microsoft.com/en-us/azure/iot-dps/iot-dps-ha-dr |
| Use virtual network connectivity patterns with DPS | https://learn.microsoft.com/en-us/azure/iot-dps/virtual-network-support |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure IoT DPS FAQs on limits and behavior | https://learn.microsoft.com/en-us/azure/iot-dps/dps-faq |
| Review Azure Device Update service limits | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-limits |
| Azure IoT Hub quotas, limits, and throttling behavior | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-quotas-throttling |

### Security
| Topic | URL |
|-------|-----|
| Secure DPS APIs using Microsoft Entra ID and RBAC | https://learn.microsoft.com/en-us/azure/iot-dps/concepts-control-access-dps-azure-ad |
| Configure DPS access control with SAS tokens | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-control-access |
| Revoke or disenroll device access in DPS securely | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-revoke-device-access-portal |
| Roll and update X.509 certificates in DPS | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-roll-certificates |
| Deprovision DPS devices and revoke IoT Hub access | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-unprovision-devices |
| Verify X.509 CA certificates with DPS proof-of-possession | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-verify-certificates |
| Configure IP filtering rules for Azure IoT DPS | https://learn.microsoft.com/en-us/azure/iot-dps/iot-dps-ip-filtering |
| Manage public network access and private endpoints for DPS | https://learn.microsoft.com/en-us/azure/iot-dps/public-network-access |
| Configure TLS versions and ciphers for DPS connections | https://learn.microsoft.com/en-us/azure/iot-dps/tls-support |
| Assign RBAC roles for Device Update and IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/configure-access-control-device-update |
| Set up private endpoints for Device Update accounts | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/configure-private-endpoints |
| Configure RBAC and Entra auth for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-control-access |
| Configure data encryption and CMKs for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-data-encryption |
| Configure network ports for Device Update traffic | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-networking |
| Manage root key rotation for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-rootkey |
| Understand end-to-end security in Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-security |
| Configure network security and private access for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/network-security |
| Secure IoT Hub APIs with Microsoft Entra ID and RBAC | https://learn.microsoft.com/en-us/azure/iot-hub/authenticate-authorize-azure-ad |
| Control IoT Hub access with SAS tokens | https://learn.microsoft.com/en-us/azure/iot-hub/authenticate-authorize-sas |
| Authenticate IoT Hub devices with X.509 certificates | https://learn.microsoft.com/en-us/azure/iot-hub/authenticate-authorize-x509 |
| Manage certificate revocation and policies for IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/concepts-certificate-policy-management |
| Manage IoT Hub device identities and connection strings | https://learn.microsoft.com/en-us/azure/iot-hub/create-connect-device |
| Revoke device certificates and clean up ADR policies | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-revoke-certificate-delete-policy |
| Use Azure IoT Hub identity registry for device management | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-identity-registry |
| Configure IP filtering rules for Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-ip-filtering |
| Use managed identities with Azure IoT Hub egress | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-managed-identity |
| Manage public network access for Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-public-network-access |
| Restrict IoT Hub outbound network access for DLP | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-restrict-outbound-network-access |
| Configure TLS versions and cipher suites for Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-tls-support |
| Migrate IoT Hub TLS root certificate to DigiCert G2 | https://learn.microsoft.com/en-us/azure/iot-hub/migrate-tls-certificate |
| Built-in Azure Policy definitions for IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/policy-reference |
| Regenerate IoT Hub shared access keys safely | https://learn.microsoft.com/en-us/azure/iot-hub/regenerate-keys |
| Azure Policy compliance controls for IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/security-controls-policy |
| Create and upload X.509 test certificates for IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/tutorial-x509-test-certs |
| Use virtual network and Private Link connectivity with Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/virtual-network-support |

### Configuration
| Topic | URL |
|-------|-----|
| Manage DPS device enrollments in Azure portal | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-manage-enrollments |
| Link and manage IoT hubs in DPS | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-manage-linked-iot-hubs |
| Configure DPS allocation policies across IoT hubs | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-use-allocation-policies |
| Query and manage DPS instance IP address properties | https://learn.microsoft.com/en-us/azure/iot-dps/iot-dps-understand-ip-address |
| Create apt manifests for package-based Device Updates | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-apt-manifest |
| Configure adu-config.json for Device Update agent | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-configuration-file |
| Configure multistep execution in Device Update manifests | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-multi-step-updates |
| Author JSON import manifests for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/import-schema |
| Configure related files in Device Update import manifests | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/related-files |
| Define update manifest payloads for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/update-manifest |
| Configure ADR credential for Microsoft-backed certificates | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-configure-credential |
| Create or edit Microsoft-root CA policy in ADR | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-create-policy |
| Configure ADR policy with external root CA | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-create-policy-external-certificate |
| Disable or enable IoT devices in Azure Device Registry | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-disable-enable-device |
| Configure IoT Hub file upload to Azure Storage | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-configure-file-upload |
| Handle customer data requests for IoT Hub devices | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-customer-data-requests |
| Understand and configure Azure IoT Hub device twins | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-device-twins |
| Configure and use IoT Hub direct methods | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-direct-methods |
| Use IoT Hub file upload for large device data | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-file-upload |
| Configure and manage Azure IoT Hub jobs for device fleets | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-jobs |
| Configure cloud-to-device messaging in IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-messages-c2d |
| Configure IoT Hub device-to-cloud message routing | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-messages-d2c |
| Understand and configure Azure IoT Hub module twins | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-module-twins |
| Configure IoT Hub communication protocols and ports | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-protocols |
| Use IoT Hub message routing query language | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-routing-query-syntax |
| Configure message enrichments in Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-message-enrichments-overview |
| Non-telemetry event schemas for Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-non-telemetry-event-schema |
| Understand and manage Azure IoT Hub IP addresses | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-understand-ip-address |
| Manage IoT Hub device and module twins via portal and CLI | https://learn.microsoft.com/en-us/azure/iot-hub/manage-device-twins |
| Reference metrics and logs for monitoring Azure IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/monitor-iot-hub-reference |
| Use the Azure IoT Hub VS Code extension | https://learn.microsoft.com/en-us/azure/iot-hub/reference-iot-hub-extension |
| Set up and use IoT Hub message enrichments | https://learn.microsoft.com/en-us/azure/iot-hub/tutorial-message-enrichments |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Send additional payload data between devices and DPS | https://learn.microsoft.com/en-us/azure/iot-dps/how-to-send-additional-data |
| Use raw HTTPS with DPS symmetric key provisioning | https://learn.microsoft.com/en-us/azure/iot-dps/iot-dps-https-sym-key-support |
| Use raw HTTPS with DPS X.509 certificate provisioning | https://learn.microsoft.com/en-us/azure/iot-dps/iot-dps-https-x509-support |
| Connect devices to Azure IoT DPS over MQTT | https://learn.microsoft.com/en-us/azure/iot-dps/iot-mqtt-connect-to-iot-dps |
| Programmatically create DPS TPM individual enrollments | https://learn.microsoft.com/en-us/azure/iot-dps/quick-enroll-device-tpm |
| Programmatically create DPS X.509 enrollment groups | https://learn.microsoft.com/en-us/azure/iot-dps/quick-enroll-device-x509 |
| Implement Device Update component enumerator via proxy | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/components-enumerator |
| Use Device Update agent status API on devices | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-agent-status |
| Send and receive IoT Hub cloud-to-device messages with SDKs | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-cloud-to-device-messaging |
| Implement device management actions using IoT Hub direct methods | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-device-management |
| Use IoT Hub device and service SDKs with device twins | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-device-twins |
| Upload device files to cloud using IoT Hub SDKs | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-file-upload |
| Use module identities and twins with IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-module-twins |
| Use IoT Hub service SDK to schedule broadcast jobs | https://learn.microsoft.com/en-us/azure/iot-hub/how-to-schedule-broadcast-jobs |
| Use AMQP protocol with Azure IoT Hub endpoints | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-amqp-support |
| Bulk import and export IoT Hub device identities | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-bulk-identity-mgmt |
| Construct Azure IoT Hub message formats | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-messages-construct |
| Read IoT Hub messages from built-in endpoint | https://learn.microsoft.com/en-us/azure/iot-hub/iot-hub-devguide-messages-read-builtin |
| Connect devices to Azure IoT Hub using MQTT | https://learn.microsoft.com/en-us/azure/iot-hub/iot-mqtt-connect-to-iot-hub |
| Control IoT devices via direct methods using .NET samples | https://learn.microsoft.com/en-us/azure/iot-hub/quickstart-control-device |
| Use PowerShell script to self-sign IoT Hub CSR certificates | https://learn.microsoft.com/en-us/azure/iot-hub/reference-self-sign-script |
| Connect IoT devices to Azure IoT Hub via MQTT | https://learn.microsoft.com/en-us/azure/iot-hub/tutorial-use-mqtt |

### Deployment
| Topic | URL |
|-------|-----|
| Generate and deploy delta updates with Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/deploy-delta-updates |
| Provision Device Update agent as IoT Edge module | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-agent-provisioning |
| Perform proxy updates with Device Update for IoT Hub | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-howto-proxy-updates |
| Deploy image-based Device Update on Raspberry Pi | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-raspberry-pi |
| Use regional failover mappings for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-region-mapping |
| Deploy package-based Device Update with Ubuntu agent | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/device-update-ubuntu-agent |
| Check supported platforms for Device Update | https://learn.microsoft.com/en-us/azure/iot-hub-device-update/support |
| Manually migrate Azure IoT Hub across regions or SKUs | https://learn.microsoft.com/en-us/azure/iot-hub/migrate-hub-arm |
| Migrate Azure IoT Hub using Azure CLI state commands | https://learn.microsoft.com/en-us/azure/iot-hub/migrate-hub-state-cli |
| Schedule IoT Hub jobs for device groups using Azure CLI | https://learn.microsoft.com/en-us/azure/iot-hub/schedule-jobs-cli |