---
name: azure-managed-applications
description: Expert knowledge for Azure Managed Applications development including limits & quotas, security, configuration, and deployment. Use when designing createUiDefinition UIs, JIT access, managed identities, StorageAccountSelector, or Bicep-based catalog publishing, and other Azure Managed Applications related development tasks. Not for Azure Blueprints (use azure-blueprints), Azure Resource Manager (use azure-resource-manager), Azure Lighthouse (use azure-lighthouse), Azure Partner Solutions (use azure-partner-solutions).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-14"
  generator: "docs2skills/1.0.0"
---
# Azure Managed Applications Skill

This skill provides expert guidance for Azure Managed Applications. Covers limits & quotas, security, configuration, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Limits & Quotas | L32-L37 | Guidance on storage-related limits: using StorageAccountSelector with naming rules and configuring external storage for large managed application definition packages. |
| Security | L38-L49 | Security and access control for managed apps: JIT access, Azure Policy associations, managed identities (incl. cross-tenant), Key Vault/CMK use, and avoiding hardcoded credentials. |
| Configuration | L50-L94 | Designing and configuring managed app deployments: createUiDefinition UI schema, functions, built-in controls, networking/VNet use, policies, webhooks, and ARM template/view references. |
| Deployment | L95-L99 | Creating and publishing Azure Managed Application definitions using Bicep and deploying them into an internal service catalog for reuse. |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use StorageAccountSelector UI element and name constraints | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-storage-storageaccountselector |
| Use custom storage for large managed app definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/publish-service-catalog-bring-your-own-storage |

### Security
| Topic | URL |
|-------|-----|
| Approve publisher just-in-time access to managed apps | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/approve-just-in-time-access |
| Use Azure Policy to associate managed applications | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/concepts-built-in-policy |
| Configure delegatedManagedIdentityResourceId for cross-tenant apps | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/concepts-delegated-managed-identity-resource-id |
| Deploy storage with customer-managed keys in managed apps | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-storage-customer-managed-key |
| Comply with hardcoded credential restrictions in templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/hardcoded-credentials-restrictions |
| Grant Key Vault access for managed app deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/key-vault-access |
| Configure managed identity for Azure managed applications | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/publish-managed-identity |
| Request just-in-time access to managed resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/request-just-in-time-access |

### Configuration
| Topic | URL |
|-------|-----|
| Configure artifactsLocation parameters for managed apps | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/artifacts-location |
| Use collection functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-collection-functions |
| Use conversion functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-conversion-functions |
| Use date functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-date-functions |
| Use logical functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-logical-functions |
| Use math functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-math-functions |
| Use referencing functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-referencing-functions |
| Use string functions in UI definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-ui-definition-string-functions |
| Use CreateUiDefinition elements in Azure portal UIs | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-uidefinition-elements |
| Use functions in createUiDefinition.json | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-uidefinition-functions |
| Author createUiDefinition.json for Azure managed apps | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/create-uidefinition-overview |
| Configure managed apps to use existing virtual networks | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/existing-vnet-integration |
| Configure Microsoft.Common.CheckBox UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-checkbox |
| Configure Microsoft.Common.DropDown UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-dropdown |
| Configure Microsoft.Common.EditableGrid UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-editablegrid |
| Configure Microsoft.Common.FileUpload UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-fileupload |
| Configure Microsoft.Common.InfoBox UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-infobox |
| Configure Microsoft.Common.OptionsGroup UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-optionsgroup |
| Configure Microsoft.Common.PasswordBox UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-passwordbox |
| Configure Microsoft.Common.Section UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-section |
| Configure ServicePrincipalSelector UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-serviceprincipalselector |
| Configure Microsoft.Common.Slider UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-slider |
| Configure TagsByResource UI element for ARM deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-tagsbyresource |
| Configure Microsoft.Common.TextBlock UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-textblock |
| Configure Microsoft.Common.TextBox UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-common-textbox |
| Configure Microsoft.Compute.CredentialsCombo UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-compute-credentialscombo |
| Configure Microsoft.Compute.SizeSelector UI element for VMs | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-compute-sizeselector |
| Configure Microsoft.Compute.UserNameTextBox UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-compute-usernametextbox |
| Configure KeyVaultCertificateSelector UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-keyvault-keyvaultcertificateselector |
| Configure ManagedIdentity IdentitySelector UI element | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-managedidentity-identityselector |
| Configure PublicIpAddressCombo UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-network-publicipaddresscombo |
| Configure VirtualNetworkCombo UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-network-virtualnetworkcombo |
| Configure ArmApiControl UI element for ARM API calls | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-solutions-armapicontrol |
| Configure ResourceSelector UI element for existing resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-solutions-resourceselector |
| Configure MultiStorageAccountCombo UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-storage-multistorageaccountcombo |
| Configure StorageBlobSelector UI element in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/microsoft-storage-storageblobselector |
| Reference built-in Azure Policy definitions for Managed Apps | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/policy-reference |
| Configure webhook notifications for managed applications | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/publish-notifications |
| Reference schema for createUiDefinition artifact | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/reference-createuidefinition-artifact |
| Reference mainTemplate.json for managed applications | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/reference-main-template-artifact |
| Reference viewDefinition.json for managed applications | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/reference-view-definition-artifact |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy managed app definitions with Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/publish-bicep-definition |
| Publish Azure Managed Application to service catalog | https://learn.microsoft.com/en-us/azure/azure-resource-manager/managed-applications/publish-service-catalog-app |