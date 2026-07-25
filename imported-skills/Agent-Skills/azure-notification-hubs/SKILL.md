---
name: azure-notification-hubs
description: Expert knowledge for Azure Notification Hubs development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. Use when integrating FCM/APNS/WNS, configuring PNS creds, targeting devices/tags, scheduling pushes, or scaling multi-tenant hubs, and other Azure Notification Hubs related development tasks. Not for Azure Event Hubs (use azure-event-hubs), Azure Service Bus (use azure-service-bus), Azure Web PubSub (use azure-web-pubsub), Azure Communication Services (use azure-communication-services).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-17"
  generator: "docs2skills/1.0.0"
---
# Azure Notification Hubs Skill

This skill provides expert guidance for Azure Notification Hubs. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L41 | Diagnosing and fixing common Notification Hubs issues, including delivery failures, dropped notifications, platform-specific errors, and steps to trace, test, and resolve send problems. |
| Best Practices | L42-L48 | Guidance on designing Notification Hubs apps: registration patterns, tags and routing, templates, and implementation FAQs for scalable, targeted push notifications. |
| Decision Making | L49-L53 | Guidance on choosing and switching Notification Hubs pricing tiers, comparing feature limits, scale, and cost implications for different workloads. |
| Architecture & Design Patterns | L54-L58 | Guidance on designing large-scale, multi-tenant, and geo-distributed push notification architectures with Azure Notification Hubs, including patterns, best practices, and integration approaches. |
| Limits & Quotas | L59-L63 | Scheduling push notifications in Azure Notification Hubs, including creating, managing, and sending time-based or recurring notifications across platforms |
| Security | L64-L72 | Security, encryption, TLS, and network isolation for Notification Hubs: data-at-rest encryption, EU data boundary, SAS/role-based access, TLS version planning, and Private Link setup. |
| Configuration | L73-L92 | Configuring Notification Hubs: PNS credentials (APNS, FCM/FCM v1, WNS, MPNS, Baidu), IaC setup (Bicep/ARM/Terraform), monitoring/logging, iOS push changes, and PowerShell management. |
| Integrations & Coding Patterns | L93-L119 | Implementing and migrating push notification integrations (FCM v1, APNS, WNS), device/user targeting, templates, localization, and using REST/SDKs (Java, PHP, Python, UWP, Android, iOS). |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and resolve common Azure Notification Hubs issues | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-push-notification-faq |
| Diagnose and fix dropped notifications in Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-push-notification-fixer |

### Best Practices
| Topic | URL |
|-------|-----|
| Choose registration patterns for Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-push-notification-registration-management |
| Use tags and routing expressions in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-tags-segment-push-message |
| Design and use Notification Hubs templates for push | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-templates-cross-platform-push-messages |

### Decision Making
| Topic | URL |
|-------|-----|
| Select and change Azure Notification Hubs pricing tiers | https://learn.microsoft.com/en-us/azure/notification-hubs/change-pricing-tier |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design enterprise push architectures with Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-enterprise-push-notification-architecture |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use scheduled notifications in Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-send-push-notifications-scheduled |

### Security
| Topic | URL |
|-------|-----|
| Azure Notification Hubs data-at-rest encryption details | https://learn.microsoft.com/en-us/azure/notification-hubs/encrypt-at-rest |
| Understand EU Data Boundary behavior in Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/eu-data-boundary |
| Apply Notification Hubs security model and access rules | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-push-notification-security |
| Plan for TLS version support in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-tls12 |
| Configure Private Link for Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/private-link |

### Configuration
| Topic | URL |
|-------|-----|
| Configure APNS credentials in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/configure-apple-push-notification-service |
| Configure Baidu Cloud Push in Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/configure-baidu-cloud-push |
| Configure FCM settings in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/configure-google-firebase-cloud-messaging |
| Configure MPNS settings in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/configure-microsoft-push-notification-service |
| Configure PNS settings for Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/configure-notification-hub-portal-pns-settings |
| Configure WNS settings in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/configure-windows-push-notification-service |
| Define Azure Notification Hubs with Bicep templates | https://learn.microsoft.com/en-us/azure/notification-hubs/create-notification-hub-bicep |
| Configure Azure Notification Hubs using ARM templates | https://learn.microsoft.com/en-us/azure/notification-hubs/create-notification-hub-template |
| Provision Azure Notification Hubs with Terraform | https://learn.microsoft.com/en-us/azure/notification-hubs/create-notification-hub-terraform |
| Configure FCM v1 credentials on Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/firebase-migration-update-sdk |
| Configure monitoring and alerts for Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/monitor-notification-hubs |
| Reference for Azure Notification Hubs monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/notification-hubs/monitor-notification-hubs-reference |
| Configure Azure Notification Hubs diagnostic and resource logs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-diagnostic-logs |
| Configure APNS HTTP/2 token-based auth in Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-push-notification-http2-token-authentication |
| Handle iOS 13 push changes in Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/push-notification-updates-ios-13 |
| Manage Notification Hubs with Azure PowerShell scripts | https://learn.microsoft.com/en-us/azure/notification-hubs/samples-powershell |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Notification Hubs with Android using FCM v1 SDK | https://learn.microsoft.com/en-us/azure/notification-hubs/android-sdk |
| Update Notification Hubs REST integrations for FCM v1 | https://learn.microsoft.com/en-us/azure/notification-hubs/firebase-migration-rest |
| Migrate Notification Hubs SDK integrations to FCM v1 | https://learn.microsoft.com/en-us/azure/notification-hubs/firebase-migration-sdk |
| Use Notification Hubs iOS SDK 3.0.0-preview1 for push | https://learn.microsoft.com/en-us/azure/notification-hubs/ios-sdk-current |
| Connect iOS apps to Notification Hubs via APNS | https://learn.microsoft.com/en-us/azure/notification-hubs/ios-sdk-get-started |
| Integrate Notification Hubs with Android using FCM SDK 0.6 | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-android-push-notification-google-fcm-get-started |
| Send user-specific iOS notifications with Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-aspnet-backend-ios-apple-apns-notification |
| Send user-targeted UWP notifications with Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-aspnet-backend-windows-dotnet-wns-notification |
| Send cross-platform user notifications with Notification Hubs templates | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-aspnet-cross-platform-notification |
| Migrate Notification Hubs from FCM legacy to FCM v1 via REST and SDKs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-gcm-to-fcm |
| Register iOS users via ASP.NET Web API for pushes | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-ios-aspnet-register-user-from-backend-to-push-notification |
| Send localized iOS push notifications using Notification Hubs templates | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-ios-xplat-localized-apns-push-notification |
| Target specific iOS devices with Azure Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-ios-xplat-segmented-apns-push-notification |
| Use the Azure Notification Hubs Java SDK | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-java-push-notification-tutorial |
| Integrate Azure Notification Hubs with PHP | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-php-push-notification-tutorial |
| Deliver location-based push with Notification Hubs and Bing Spatial Data | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-push-bing-spatial-data-geofencing-notification |
| Send Azure Notification Hubs pushes with Python | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-python-push-notification-tutorial |
| Send UWP notifications to specific devices using tags | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-windows-notification-dotnet-push-xplat-segmented-wns |
| Integrate UWP apps with Azure Notification Hubs via WNS | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-windows-store-dotnet-get-started-wns-push-notification |
| Send localized UWP notifications with Notification Hubs templates | https://learn.microsoft.com/en-us/azure/notification-hubs/notification-hubs-windows-store-dotnet-xplat-localized-wns-push-notification |
| Target specific Android devices with Notification Hubs and FCM | https://learn.microsoft.com/en-us/azure/notification-hubs/push-notifications-android-specific-devices-firebase-cloud-messaging |
| Send user-targeted Android notifications with Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/push-notifications-android-specific-users-firebase-cloud-messaging |
| Use Notification Hubs for cross-platform Android and iOS push | https://learn.microsoft.com/en-us/azure/notification-hubs/uwp-react |
| Send APNS VOIP notifications via Notification Hubs | https://learn.microsoft.com/en-us/azure/notification-hubs/voip-apns |