#!/usr/bin/env python3
"""
Azure Bicep template generator.
Generates Bicep infrastructure-as-code scaffolds for common Azure architecture patterns.

Usage:
    python bicep_generator.py --arch-type web-app
    python bicep_generator.py --arch-type microservices --output main.bicep
    python bicep_generator.py --arch-type serverless --json
    python bicep_generator.py --help
"""

import argparse
import json
import sys
from typing import Dict


# ---------------------------------------------------------------------------
# Bicep templates
# ---------------------------------------------------------------------------

def _web_app_template() -> str:
    return r"""// =============================================================================
// Azure Web App Architecture — Bicep Template
// App Service + Azure SQL + Front Door + Key Vault + Application Insights
// =============================================================================

@description('Environment name')
@allowed(['dev', 'staging', 'production'])
param environment string = 'dev'

@description('Azure region')
param location string = resourceGroup().location

@description('Application name (lowercase, no spaces)')
@minLength(3)
@maxLength(20)
param appName string

@description('SQL admin Entra ID object ID')
param sqlAdminObjectId string

// ---------------------------------------------------------------------------
// Key Vault
// ---------------------------------------------------------------------------

resource keyVault 'Microsoft.KeyVault/vaults@2023-07-01' = {
  name: '${environment}-${appName}-kv'
  location: location
  properties: {
    sku: { family: 'A', name: 'standard' }
    tenantId: subscription().tenantId
    enableRbacAuthorization: true
    enableSoftDelete: true
    softDeleteRetentionInDays: 30
    networkAcls: {
      defaultAction: 'Deny'
      bypass: 'AzureServices'
    }
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// App Service Plan + App Service
// ---------------------------------------------------------------------------

resource appServicePlan 'Microsoft.Web/serverfarms@2023-01-01' = {
  name: '${environment}-${appName}-plan'
  location: location
  sku: {
    name: environment == 'production' ? 'P1v3' : 'B1'
    tier: environment == 'production' ? 'PremiumV3' : 'Basic'
    capacity: 1
  }
  properties: {
    reserved: true // Linux
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource appService 'Microsoft.Web/sites@2023-01-01' = {
  name: '${environment}-${appName}-web'
  location: location
  properties: {
    serverFarmId: appServicePlan.id
    httpsOnly: true
    siteConfig: {
      linuxFxVersion: 'NODE|20-lts'
      minTlsVersion: '1.2'
      ftpsState: 'Disabled'
      alwaysOn: environment == 'production'
      healthCheckPath: '/health'
    }
  }
  identity: {
    type: 'SystemAssigned'
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Azure SQL (Serverless)
// ---------------------------------------------------------------------------

resource sqlServer 'Microsoft.Sql/servers@2023-05-01-preview' = {
  name: '${environment}-${appName}-sql'
  location: location
  properties: {
    administrators: {
      administratorType: 'ActiveDirectory'
      azureADOnlyAuthentication: true
      principalType: 'Group'
      sid: sqlAdminObjectId
      tenantId: subscription().tenantId
    }
    minimalTlsVersion: '1.2'
    publicNetworkAccess: environment == 'production' ? 'Disabled' : 'Enabled'
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource sqlDatabase 'Microsoft.Sql/servers/databases@2023-05-01-preview' = {
  parent: sqlServer
  name: '${appName}-db'
  location: location
  sku: {
    name: 'GP_S_Gen5_2'
    tier: 'GeneralPurpose'
  }
  properties: {
    autoPauseDelay: environment == 'production' ? -1 : 60
    minCapacity: json('0.5')
    zoneRedundant: environment == 'production'
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Application Insights + Log Analytics
// ---------------------------------------------------------------------------

resource logAnalytics 'Microsoft.OperationalInsights/workspaces@2022-10-01' = {
  name: '${environment}-${appName}-logs'
  location: location
  properties: {
    sku: { name: 'PerGB2018' }
    retentionInDays: environment == 'production' ? 90 : 30
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource appInsights 'Microsoft.Insights/components@2020-02-02' = {
  name: '${environment}-${appName}-ai'
  location: location
  kind: 'web'
  properties: {
    Application_Type: 'web'
    WorkspaceResourceId: logAnalytics.id
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Outputs
// ---------------------------------------------------------------------------

output appServiceUrl string = 'https://${appService.properties.defaultHostName}'
output keyVaultUri string = keyVault.properties.vaultUri
output appInsightsKey string = appInsights.properties.InstrumentationKey
output sqlServerFqdn string = sqlServer.properties.fullyQualifiedDomainName
"""


def _microservices_template() -> str:
    return r"""// =============================================================================
// Azure Microservices Architecture — Bicep Template
// AKS + API Management + Cosmos DB + Service Bus + Key Vault
// =============================================================================

@description('Environment name')
@allowed(['dev', 'staging', 'production'])
param environment string = 'dev'

@description('Azure region')
param location string = resourceGroup().location

@description('Application name')
@minLength(3)
@maxLength(20)
param appName string

@description('AKS admin Entra ID group object ID')
param aksAdminGroupId string

// ---------------------------------------------------------------------------
// Key Vault
// ---------------------------------------------------------------------------

resource keyVault 'Microsoft.KeyVault/vaults@2023-07-01' = {
  name: '${environment}-${appName}-kv'
  location: location
  properties: {
    sku: { family: 'A', name: 'standard' }
    tenantId: subscription().tenantId
    enableRbacAuthorization: true
    enableSoftDelete: true
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// AKS Cluster
// ---------------------------------------------------------------------------

resource aksCluster 'Microsoft.ContainerService/managedClusters@2024-01-01' = {
  name: '${environment}-${appName}-aks'
  location: location
  identity: { type: 'SystemAssigned' }
  properties: {
    dnsPrefix: '${environment}-${appName}'
    kubernetesVersion: '1.29'
    enableRBAC: true
    aadProfile: {
      managed: true
      adminGroupObjectIDs: [aksAdminGroupId]
      enableAzureRBAC: true
    }
    networkProfile: {
      networkPlugin: 'azure'
      networkPolicy: 'azure'
      serviceCidr: '10.0.0.0/16'
      dnsServiceIP: '10.0.0.10'
    }
    agentPoolProfiles: [
      {
        name: 'system'
        count: environment == 'production' ? 3 : 1
        vmSize: 'Standard_D2s_v5'
        mode: 'System'
        enableAutoScaling: true
        minCount: 1
        maxCount: 3
        availabilityZones: environment == 'production' ? ['1', '2', '3'] : []
      }
      {
        name: 'app'
        count: environment == 'production' ? 3 : 1
        vmSize: 'Standard_D4s_v5'
        mode: 'User'
        enableAutoScaling: true
        minCount: 1
        maxCount: 10
        availabilityZones: environment == 'production' ? ['1', '2', '3'] : []
      }
    ]
    addonProfiles: {
      omsagent: {
        enabled: true
        config: {
          logAnalyticsWorkspaceResourceID: logAnalytics.id
        }
      }
    }
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Container Registry
// ---------------------------------------------------------------------------

resource acr 'Microsoft.ContainerRegistry/registries@2023-07-01' = {
  name: '${environment}${appName}acr'
  location: location
  sku: { name: environment == 'production' ? 'Standard' : 'Basic' }
  properties: {
    adminUserEnabled: false
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Cosmos DB (Serverless for dev, Autoscale for prod)
// ---------------------------------------------------------------------------

resource cosmosAccount 'Microsoft.DocumentDB/databaseAccounts@2023-11-15' = {
  name: '${environment}-${appName}-cosmos'
  location: location
  kind: 'GlobalDocumentDB'
  properties: {
    databaseAccountOfferType: 'Standard'
    consistencyPolicy: { defaultConsistencyLevel: 'Session' }
    locations: [
      { locationName: location, failoverPriority: 0, isZoneRedundant: environment == 'production' }
    ]
    capabilities: environment == 'dev' ? [{ name: 'EnableServerless' }] : []
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Service Bus
// ---------------------------------------------------------------------------

resource serviceBus 'Microsoft.ServiceBus/namespaces@2022-10-01-preview' = {
  name: '${environment}-${appName}-sb'
  location: location
  sku: { name: 'Standard', tier: 'Standard' }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Log Analytics + Application Insights
// ---------------------------------------------------------------------------

resource logAnalytics 'Microsoft.OperationalInsights/workspaces@2022-10-01' = {
  name: '${environment}-${appName}-logs'
  location: location
  properties: {
    sku: { name: 'PerGB2018' }
    retentionInDays: environment == 'production' ? 90 : 30
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource appInsights 'Microsoft.Insights/components@2020-02-02' = {
  name: '${environment}-${appName}-ai'
  location: location
  kind: 'web'
  properties: {
    Application_Type: 'web'
    WorkspaceResourceId: logAnalytics.id
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Outputs
// ---------------------------------------------------------------------------

output aksClusterName string = aksCluster.name
output acrLoginServer string = acr.properties.loginServer
output cosmosEndpoint string = cosmosAccount.properties.documentEndpoint
output serviceBusEndpoint string = '${serviceBus.name}.servicebus.windows.net'
output keyVaultUri string = keyVault.properties.vaultUri
"""


def _serverless_template() -> str:
    return r"""// =============================================================================
// Azure Serverless Architecture — Bicep Template
// Azure Functions + Event Grid + Service Bus + Cosmos DB
// =============================================================================

@description('Environment name')
@allowed(['dev', 'staging', 'production'])
param environment string = 'dev'

@description('Azure region')
param location string = resourceGroup().location

@description('Application name')
@minLength(3)
@maxLength(20)
param appName string

// ---------------------------------------------------------------------------
// Storage Account (required by Functions)
// ---------------------------------------------------------------------------

resource storageAccount 'Microsoft.Storage/storageAccounts@2023-01-01' = {
  name: '${environment}${appName}st'
  location: location
  sku: { name: 'Standard_LRS' }
  kind: 'StorageV2'
  properties: {
    supportsHttpsTrafficOnly: true
    minimumTlsVersion: 'TLS1_2'
    allowBlobPublicAccess: false
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Azure Functions (Consumption Plan)
// ---------------------------------------------------------------------------

resource functionPlan 'Microsoft.Web/serverfarms@2023-01-01' = {
  name: '${environment}-${appName}-func-plan'
  location: location
  sku: {
    name: 'Y1'
    tier: 'Dynamic'
  }
  properties: {
    reserved: true // Linux
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource functionApp 'Microsoft.Web/sites@2023-01-01' = {
  name: '${environment}-${appName}-func'
  location: location
  kind: 'functionapp,linux'
  identity: { type: 'SystemAssigned' }
  properties: {
    serverFarmId: functionPlan.id
    httpsOnly: true
    siteConfig: {
      linuxFxVersion: 'NODE|20'
      minTlsVersion: '1.2'
      ftpsState: 'Disabled'
      appSettings: [
        { name: 'AzureWebJobsStorage', value: 'DefaultEndpointsProtocol=https;AccountName=${storageAccount.name};EndpointSuffix=core.windows.net;AccountKey=${storageAccount.listKeys().keys[0].value}' }
        { name: 'FUNCTIONS_EXTENSION_VERSION', value: '~4' }
        { name: 'FUNCTIONS_WORKER_RUNTIME', value: 'node' }
        { name: 'APPINSIGHTS_INSTRUMENTATIONKEY', value: appInsights.properties.InstrumentationKey }
        { name: 'COSMOS_ENDPOINT', value: cosmosAccount.properties.documentEndpoint }
        { name: 'SERVICE_BUS_CONNECTION', value: listKeys('${serviceBus.id}/AuthorizationRules/RootManageSharedAccessKey', serviceBus.apiVersion).primaryConnectionString }
      ]
    }
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Cosmos DB (Serverless)
// ---------------------------------------------------------------------------

resource cosmosAccount 'Microsoft.DocumentDB/databaseAccounts@2023-11-15' = {
  name: '${environment}-${appName}-cosmos'
  location: location
  kind: 'GlobalDocumentDB'
  properties: {
    databaseAccountOfferType: 'Standard'
    consistencyPolicy: { defaultConsistencyLevel: 'Session' }
    locations: [
      { locationName: location, failoverPriority: 0 }
    ]
    capabilities: [{ name: 'EnableServerless' }]
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Service Bus
// ---------------------------------------------------------------------------

resource serviceBus 'Microsoft.ServiceBus/namespaces@2022-10-01-preview' = {
  name: '${environment}-${appName}-sb'
  location: location
  sku: { name: 'Basic', tier: 'Basic' }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource orderQueue 'Microsoft.ServiceBus/namespaces/queues@2022-10-01-preview' = {
  parent: serviceBus
  name: 'orders'
  properties: {
    maxDeliveryCount: 5
    defaultMessageTimeToLive: 'P7D'
    deadLetteringOnMessageExpiration: true
    lockDuration: 'PT1M'
  }
}

// ---------------------------------------------------------------------------
// Application Insights + Log Analytics
// ---------------------------------------------------------------------------

resource logAnalytics 'Microsoft.OperationalInsights/workspaces@2022-10-01' = {
  name: '${environment}-${appName}-logs'
  location: location
  properties: {
    sku: { name: 'PerGB2018' }
    retentionInDays: 30
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource appInsights 'Microsoft.Insights/components@2020-02-02' = {
  name: '${environment}-${appName}-ai'
  location: location
  kind: 'web'
  properties: {
    Application_Type: 'web'
    WorkspaceResourceId: logAnalytics.id
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Outputs
// ---------------------------------------------------------------------------

output functionAppUrl string = 'https://${functionApp.properties.defaultHostName}'
output cosmosEndpoint string = cosmosAccount.properties.documentEndpoint
output serviceBusEndpoint string = '${serviceBus.name}.servicebus.windows.net'
output appInsightsKey string = appInsights.properties.InstrumentationKey
"""


def _data_pipeline_template() -> str:
    return r"""// =============================================================================
// Azure Data Pipeline Architecture — Bicep Template
// Event Hubs + Data Lake Gen2 + Synapse Analytics + Azure Functions
// =============================================================================

@description('Environment name')
@allowed(['dev', 'staging', 'production'])
param environment string = 'dev'

@description('Azure region')
param location string = resourceGroup().location

@description('Application name')
@minLength(3)
@maxLength(20)
param appName string

// ---------------------------------------------------------------------------
// Data Lake Storage Gen2
// ---------------------------------------------------------------------------

resource dataLake 'Microsoft.Storage/storageAccounts@2023-01-01' = {
  name: '${environment}${appName}dl'
  location: location
  sku: { name: environment == 'production' ? 'Standard_ZRS' : 'Standard_LRS' }
  kind: 'StorageV2'
  properties: {
    isHnsEnabled: true  // Hierarchical namespace for Data Lake Gen2
    supportsHttpsTrafficOnly: true
    minimumTlsVersion: 'TLS1_2'
    allowBlobPublicAccess: false
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource rawContainer 'Microsoft.Storage/storageAccounts/blobServices/containers@2023-01-01' = {
  name: '${dataLake.name}/default/raw'
  properties: { publicAccess: 'None' }
}

resource curatedContainer 'Microsoft.Storage/storageAccounts/blobServices/containers@2023-01-01' = {
  name: '${dataLake.name}/default/curated'
  properties: { publicAccess: 'None' }
}

// ---------------------------------------------------------------------------
// Event Hubs
// ---------------------------------------------------------------------------

resource eventHubNamespace 'Microsoft.EventHub/namespaces@2023-01-01-preview' = {
  name: '${environment}-${appName}-eh'
  location: location
  sku: {
    name: 'Standard'
    tier: 'Standard'
    capacity: environment == 'production' ? 2 : 1
  }
  properties: {
    minimumTlsVersion: '1.2'
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

resource eventHub 'Microsoft.EventHub/namespaces/eventhubs@2023-01-01-preview' = {
  parent: eventHubNamespace
  name: 'ingest'
  properties: {
    partitionCount: environment == 'production' ? 8 : 2
    messageRetentionInDays: 7
  }
}

resource consumerGroup 'Microsoft.EventHub/namespaces/eventhubs/consumergroups@2023-01-01-preview' = {
  parent: eventHub
  name: 'processing'
}

// ---------------------------------------------------------------------------
// Synapse Analytics (Serverless SQL)
// ---------------------------------------------------------------------------

resource synapse 'Microsoft.Synapse/workspaces@2021-06-01' = {
  name: '${environment}-${appName}-syn'
  location: location
  identity: { type: 'SystemAssigned' }
  properties: {
    defaultDataLakeStorage: {
      accountUrl: 'https://${dataLake.name}.dfs.core.windows.net'
      filesystem: 'curated'
    }
    sqlAdministratorLogin: 'sqladmin'
    sqlAdministratorLoginPassword: 'REPLACE_WITH_KEYVAULT_REFERENCE'
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Log Analytics
// ---------------------------------------------------------------------------

resource logAnalytics 'Microsoft.OperationalInsights/workspaces@2022-10-01' = {
  name: '${environment}-${appName}-logs'
  location: location
  properties: {
    sku: { name: 'PerGB2018' }
    retentionInDays: 30
  }
  tags: {
    environment: environment
    'app-name': appName
  }
}

// ---------------------------------------------------------------------------
// Outputs
// ---------------------------------------------------------------------------

output dataLakeEndpoint string = 'https://${dataLake.name}.dfs.core.windows.net'
output eventHubNamespace string = eventHubNamespace.name
output synapseEndpoint string = synapse.properties.connectivityEndpoints.sql
"""


TEMPLATES: Dict[str, callable] = {
    "web-app": _web_app_template,
    "microservices": _microservices_template,
    "serverless": _serverless_template,
    "data-pipeline": _data_pipeline_template,
}

TEMPLATE_DESCRIPTIONS = {
    "web-app": "App Service + Azure SQL + Front Door + Key Vault + Application Insights",
    "microservices": "AKS + API Management + Cosmos DB + Service Bus + Key Vault",
    "serverless": "Azure Functions + Event Grid + Service Bus + Cosmos DB",
    "data-pipeline": "Event Hubs + Data Lake Gen2 + Synapse Analytics + Azure Functions",
}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Azure Bicep Generator — generate Bicep IaC templates for common Azure architecture patterns.",
        epilog="Examples:\n"
               "  python bicep_generator.py --arch-type web-app\n"
               "  python bicep_generator.py --arch-type microservices --output main.bicep\n"
               "  python bicep_generator.py --arch-type serverless --json",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--arch-type",
        required=True,
        choices=list(TEMPLATES.keys()),
        help="Architecture pattern type",
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Write Bicep to file instead of stdout",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        help="Output metadata as JSON (template content + description)",
    )

    args = parser.parse_args()

    template_fn = TEMPLATES[args.arch_type]
    bicep_content = template_fn()

    if args.json_output:
        result = {
            "arch_type": args.arch_type,
            "description": TEMPLATE_DESCRIPTIONS[args.arch_type],
            "bicep_template": bicep_content,
            "lines": len(bicep_content.strip().split("\n")),
        }
        print(json.dumps(result, indent=2))
    elif args.output:
        with open(args.output, "w") as f:
            f.write(bicep_content)
        print(f"Bicep template written to {args.output} ({len(bicep_content.strip().split(chr(10)))} lines)")
        print(f"Pattern: {TEMPLATE_DESCRIPTIONS[args.arch_type]}")
        print(f"\nNext steps:")
        print(f"  1. az bicep build --file {args.output}")
        print(f"  2. az deployment group validate --resource-group <rg> --template-file {args.output}")
        print(f"  3. az deployment group create --resource-group <rg> --template-file {args.output}")
    else:
        print(bicep_content)


if __name__ == "__main__":
    main()
