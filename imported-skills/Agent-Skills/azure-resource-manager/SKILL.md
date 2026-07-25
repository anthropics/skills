---
name: azure-resource-manager
description: Expert knowledge for Azure Resource Manager development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when authoring Bicep/ARM templates, using CLI/PowerShell/REST, configuring policy/Key Vault, or multi-scope deployments, and other Azure Resource Manager related development tasks. Not for Azure Policy (use azure-policy), Azure Resource Graph (use azure-resource-graph), Azure Portal (use azure-portal), Azure Networking (use azure-networking).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Resource Manager Skill

This skill provides expert guidance for Azure Resource Manager. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L134 | Diagnosing and fixing Bicep/ARM deployment issues: compiler diagnostics (BCP codes), decorator/type errors, template/resource name/scope problems, policy/SKU/region/provider failures, and debug logging. |
| Best Practices | L135-L179 | Best practices for authoring and validating ARM/Bicep templates: lint rules, naming, locations, dependencies, resource IDs, module versions, and ARM toolkit tests for quality and resiliency. |
| Decision Making | L180-L193 | Guidance on migration and relocation decisions: moving from classic/ASM to ARM/Bicep, blueprint-to-stack migration, regional move planning, resource move/tag support, and relocation strategies. |
| Architecture & Design Patterns | L194-L201 | Bicep architecture patterns for reusable configs, flexible parameters, deterministic name generation, and sharing variables across templates for scalable ARM deployments. |
| Limits & Quotas | L202-L231 | ARM/Bicep limits, quotas, and constraints: deployment history, job size, resources per group, parameters/outputs/variables, naming/tag rules, throttling, and quota-exceeded error troubleshooting. |
| Security | L232-L259 | Securing ARM/Bicep deployments: secrets handling, secure parameters, RBAC, Key Vault integration, Private Link/VNet access, locks, policy/regulatory mapping, and TLS/network security. |
| Configuration | L260-L316 | Configuring ARM and Bicep templates: file structure, parameters, scopes, tags, networking, monitoring, policy, custom providers, portal Form view UI, and deployment/AI tooling setup. |
| Integrations & Coding Patterns | L317-L378 | Bicep and ARM integration patterns, functions, and operators, plus CLI/PowerShell/Python/REST usage for deploying, querying, tagging, and programmatically managing Azure resources. |
| Deployment | L379-L436 | Deploying and moving Azure resources with ARM/Bicep: scripts, stacks, registries, multi-scope deployments, CI/CD, and region/subscription relocation for many Azure services. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Understand and manage Bicep diagnostic codes | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-core-diagnostics |
| Fix BCP007 unrecognized Bicep declaration type | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp007 |
| Resolve BCP009 incomplete Bicep declarations | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp009 |
| Resolve BCP018 missing character syntax errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp018 |
| Fix BCP029 invalid Bicep resource type format | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp029 |
| Resolve BCP033 type mismatch diagnostics in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp033 |
| Resolve BCP034 Bicep array type mismatch errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp034 |
| Fix BCP035 missing required Bicep resource properties | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp035 |
| Resolve BCP036 Bicep property type mismatch issues | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp036 |
| Fix BCP037 invalid property on Bicep object type | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp037 |
| Resolve BCP040 unsupported string interpolation for keys | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp040 |
| Fix BCP048 unresolved Bicep function overloads | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp048 |
| Resolve BCP052 missing property type errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp052 |
| Fix BCP053 undefined property errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp053 |
| Address BCP055 invalid property access in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp055 |
| Resolve BCP057 undefined name errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp057 |
| Handle BCP062 invalid referenced declaration in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp062 |
| Fix BCP063 invalid name kind errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp063 |
| Resolve BCP070 function argument type mismatch in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp070 |
| Fix BCP071 incorrect function argument count in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp071 |
| Resolve BCP072 invalid symbol references in parameter defaults | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp072 |
| Fix BCP073 assignments to read-only properties in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp073 |
| Fix BCP076 invalid index operator usage in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp076 |
| Resolve BCP077 access to write-only properties in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp077 |
| Fix BCP078 missing values for tagged union properties | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp078 |
| Handle BCP081 missing resource type metadata in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp081 |
| Resolve BCP082 undefined name with suggestions in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp082 |
| Fix BCP083 mistyped property names in Bicep types | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp083 |
| Resolve BCP088 property value type typos in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp088 |
| Fix BCP089 invalid or mistyped object properties in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp089 |
| Resolve BCP091 file path not found errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp091 |
| Fix BCP124 invalid decorator targets in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp124 |
| Resolve BCP125 invalid parameter decorators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp125 |
| Fix BCP126 invalid variable decorators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp126 |
| Resolve BCP127 invalid resource decorators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp127 |
| Fix BCP128 invalid module decorators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp128 |
| Resolve BCP129 invalid output decorators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp129 |
| Fix BCP130 invalid decorator usage in Bicep param files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp130 |
| Resolve BCP132 missing declaration after decorator in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp132 |
| Fix BCP135 invalid deployment scope for Bicep resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp135 |
| Resolve BCP138 unsupported for-expression contexts in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp138 |
| Fix BCP139 mismatched resource and file scopes in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp139 |
| Fix BCP144 invalid collection references without index in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp144 |
| Resolve BCP147 missing parameter after decorator in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp147 |
| Fix BCP152 invalid function usage as decorator in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp152 |
| Resolve BCP153 missing resource or module after decorator | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp153 |
| Fix BCP166 duplicate decorator usage in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp166 |
| Resolve BCP170 invalid child resource names with slashes | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp170 |
| Handle BCP192 failed artifact restore for Bicep modules | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp192 |
| Resolve BCP201 invalid Bicep extension specification strings | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp201 |
| Resolve BCP226 missing diagnostic codes in #disable-next-line | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp226 |
| Fix BCP238 unexpected newline after comma in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp238 |
| Resolve BCP266 metadata identifier errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp266 |
| Fix BCP288 type-used-as-value errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp288 |
| Resolve BCP290 decorator declaration errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp290 |
| Fix BCP292 decorator parameter/output/type errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp292 |
| Resolve BCP293 invalid union member type errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp293 |
| Fix BCP294 non-reducible union type errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp294 |
| Resolve BCP302 invalid Bicep type name errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp302 |
| Fix BCP311 invalid array index errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp311 |
| Resolve BCP318 null-access and conditional resource errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp318 |
| Resolve BCP321 type mismatch diagnostics in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp321 |
| Fix BCP327 value-too-large assignment errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp327 |
| Resolve BCP328 value-too-small assignment errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp328 |
| Fix BCP332 maximum length validation errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp332 |
| Resolve BCP333 minimum length validation errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp333 |
| Handle BCP335 potential maximum length violations | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp335 |
| Fix BCP337 invalid declaration types in parameters files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp337 |
| Resolve BCP338 parameter evaluation failures in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp338 |
| Fix BCP364 discriminator property errors in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp364 |
| Fix BCP401 invalid spread operator usage in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp401 |
| Resolve BCP414 invalid reverse index operator usage | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp414 |
| Resolve BCP416 string pattern mismatch errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp416 |
| Fix BCP420 unresolved or complex scope expressions in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp420 |
| Handle BCP422 function calls on non-existent resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp422 |
| Resolve common Azure Bicep deployment questions and issues | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/frequently-asked-questions |
| Diagnose and fix Bicep installation errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/installation-troubleshoot |
| Delete Azure resource groups and handle deletion responses | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/delete-resource-group |
| Resolve common Azure ARM template issues and questions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/frequently-asked-questions |
| Resolve common Azure ARM deployment errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/common-deployment-errors |
| Create ARM templates for targeted troubleshooting | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/create-troubleshooting-template |
| Enable debug logging for ARM deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/enable-debug-logging |
| Fix invalid resource name and type segment errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-invalid-name-segments |
| Diagnose and fix Azure ARM invalid template errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-invalid-template |
| Resolve resource not found errors in Azure | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-not-found |
| Fix parent resource dependency errors in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-parent-resource |
| Resolve RequestDisallowedByPolicy errors in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-policy-requestdisallowedbypolicy |
| Resolve location ineligible errors for Azure regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-region-access-policy |
| Fix resource provider registration errors in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-register-resource-provider |
| Fix reserved resource name errors in Azure | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-reserved-resource-name |
| Fix SKU not available errors in Azure deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-sku-not-available |
| Fix storage account name errors in ARM deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-storage-account-name |
| Find ARM and Bicep deployment error codes | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/find-error-code |
| Troubleshoot Azure management group SDK errors | https://learn.microsoft.com/en-us/azure/governance/management-groups/troubleshoot/general |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply recommended development practices for Bicep files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/best-practices |
| Use ARM preflight validation to catch deployment errors early | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deploy-preflight |
| Apply and customize Bicep linter best practices | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter |
| Use explicit locations for Bicep module parameters | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-explicit-values-for-loc-params |
| Scope nested deployment templates correctly in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-nested-deployment-template-scoping |
| Avoid conflicting metadata decorators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-conflicting-metadata |
| Avoid root-level deployment resources in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-deployments-resources |
| Discourage explicit any type usage in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-explicit-any |
| Apply Bicep linter rule for environment-specific URLs | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-hardcoded-environment-urls |
| Avoid hardcoded Azure locations in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-hardcoded-location |
| Restrict location expressions to parameter defaults | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-loc-expr-outside-params |
| Enforce no explicit module name in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-module-name |
| Remove unnecessary dependsOn entries in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-unnecessary-dependson |
| Detect unused existing resources in Bicep files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-unused-existing-resources |
| Detect unused imports in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-unused-imports |
| Detect unused parameters in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-unused-parameters |
| Detect unused variables in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-no-unused-variables |
| Prefer string interpolation over concat in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-prefer-interpolation |
| Prefer unquoted property names in Bicep objects | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-prefer-unquoted-property-names |
| Simplify unnecessary string interpolation in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-simplify-interpolation |
| Simplify JSON null usage in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-simplify-json-null |
| Use parent property for child resources in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-parent-property |
| Use recent API versions with Bicep linter | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-recent-api-versions |
| Use recent Az PowerShell versions in scripts | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-recent-az-powershell-version |
| Use recent public Bicep module versions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-recent-module-versions |
| Apply Bicep linter rule for resource ID functions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-resource-id-functions |
| Use resource symbol references instead of list/reference | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-resource-symbol-reference |
| Refactor Bicep code to use safe access operator | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-safe-access |
| Avoid non-deterministic resource names in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-stable-resource-identifier |
| Prevent preview VM images with Bicep linter | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-stable-vm-image |
| Apply Bicep linter rule for user-defined types | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-user-defined-types |
| Detect what-if short-circuiting in Bicep modules | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-what-if-short-circuiting |
| Apply best practices for custom action endpoints in Azure | https://learn.microsoft.com/en-us/azure/azure-resource-manager/custom-providers/custom-providers-action-endpoint-how-to |
| Implement custom resource endpoints with Azure best practices | https://learn.microsoft.com/en-us/azure/azure-resource-manager/custom-providers/custom-providers-resources-endpoint-how-to |
| Tag mission-critical Azure workloads for resiliency assessments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-mission-critical-workload |
| Use ARM toolkit tests for all JSON files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/all-files-test-cases |
| Apply recommended authoring practices for ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/best-practices |
| Test createUiDefinition.json with ARM toolkit | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/createuidefinition-test-cases |
| Validate ARM parameter files with test toolkit | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/parameter-file-test-cases |
| Apply ARM template test cases for quality | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-test-cases |
| Run ARM template test toolkit for best practices | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/test-toolkit |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan migration from ARM JSON templates to Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/migrate |
| Migrate Azure Blueprints to deployment stacks | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/migrate-blueprint |
| Plan migration from Azure Service Manager to ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/asm-retirement |
| Choose between classic and Resource Manager deployment models | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/deployment-models |
| Determine which Azure resources support move operations | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-support-resources |
| Evaluate Azure workloads for regional relocation | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocate-evaluate |
| Plan Azure workload relocation projects by phase | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocate-index |
| Initiate large-scale Azure relocation projects | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocate-initiate |
| Choose strategies for Azure workload relocation | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocate-select |
| Determine Azure resource types that support tags | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-support |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Apply the configuration set pattern in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/patterns-configuration-set |
| Use logical parameter pattern for flexible Bicep deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/patterns-logical-parameter |
| Implement robust name generation patterns in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/patterns-name-generation |
| Use shared variable file pattern in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/patterns-shared-variable-file |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Deploy Bicep to subscriptions within RG limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deploy-to-subscription |
| Review deployment stack limitations and known issues | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-stacks-known-issues |
| Enforce maximum predeployment asserts in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-max-asserts |
| Validate Bicep outputs against ARM template limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-max-outputs |
| Validate Bicep parameters against ARM template limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-max-parameters |
| Validate Bicep resources against ARM template limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-max-resources |
| Enforce ARM variable count limits in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-max-variables |
| Configure outputs in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/outputs |
| Define and manage parameters in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/parameters |
| Declare Bicep resources within file limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/resource-declaration |
| Understand template spec limitations and workarounds | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/template-specs-known-issues |
| Review Azure subscription and service limits and quotas | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/azure-subscription-service-limits |
| Networking resource move limitations across subscriptions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-limitations/networking-move-limitations |
| Handle Azure Resource Manager request throttling limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/request-limits-and-throttling |
| Apply Azure resource naming rules and restrictions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/resource-name-rules |
| Identify Azure resources exempt from 800-per-group limit | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/resources-without-resource-group-limit |
| Apply and understand Azure resource tag limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-resources |
| Deploy ARM templates at subscription scope | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-to-subscription |
| View and manage ARM deployment history limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deployment-history |
| Understand ARM deployment history limits and cleanup behavior | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deployment-history-deletions |
| Configure outputs and respect ARM output limits | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/outputs |
| Define and constrain parameters in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/parameters |
| Use ARM template expressions and syntax rules | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-expressions |
| Resolve deployment quota exceeded errors in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/deployment-quota-exceeded |
| Resolve ARM job size exceeded deployment errors | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-job-size-exceeded |
| Resolve resource quota errors in ARM deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/troubleshooting/error-resource-quota |

### Security
| Topic | URL |
|-------|-----|
| Run Bicep deployment scripts inside private virtual networks | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-script-vnet |
| Execute Bicep deployment scripts via private endpoints | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-script-vnet-private-endpoint |
| Resolve BCP446 trusted registry restriction in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/diagnostics/bcp446 |
| Prevent exposing secrets in Bicep outputs | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-outputs-should-not-contain-secrets |
| Protect commandToExecute secrets in Bicep scripts | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-protect-commandtoexecute-secrets |
| Avoid hardcoded defaults for secure Bicep parameters | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-secure-parameter-default |
| Secure parameters in nested Bicep deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-secure-params-in-nested-deploy |
| Ensure secret-like parameters are marked secure | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-secure-secrets-in-parameters |
| Enforce secure adminPassword values in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-use-secure-value-for-secure-inputs |
| Define Azure RBAC roles and assignments with Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/scenarios-rbac |
| Manage deployment secrets with Bicep and Key Vault | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/scenarios-secrets |
| Authenticate Azure Resource Manager requests across tenants | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/authenticate-multi-tenant |
| Configure ARM management access through Private Link (commands) | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/create-private-link-access-commands |
| Secure ARM management with Private Link via Azure portal | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/create-private-link-access-portal |
| Protect Azure resources with management locks | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/lock-resources |
| Manage existing Azure Resource Manager Private Links via API | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-private-link-access-commands |
| Map Azure Policy regulatory controls for ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/security-controls-policy |
| Use Azure Resource Manager service tags in network security rules | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/service-tags |
| Plan for TLS version support changes in Azure Resource Manager | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tls-support |
| Use Key Vault secrets as ARM template parameters | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/key-vault-parameter |
| Securely deploy private ARM templates with SAS | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/secure-template-with-sas-token |
| Create and share ARM template specs securely | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-specs |
| Secure ARM template parameters with Azure Key Vault | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-tutorial-use-key-vault |
| Configure hierarchy protection for Azure management groups | https://learn.microsoft.com/en-us/azure/governance/management-groups/how-to/protect-resource-hierarchy |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Bicep environment with bicepconfig.json | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-config |
| Configure Bicep linter settings in bicepconfig.json | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-config-linter |
| Configure Bicep module aliases and credentials | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-config-modules |
| Configure and use Bicep extensions for external resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-extension |
| Run and configure the Bicep MCP server for AI tools | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-mcp-server |
| Configure child resource names and types in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/child-resource-name-type |
| Use supported data types in Bicep files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/data-types |
| Configure dev environments for Bicep deployment scripts | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-script-bicep-configure-dev |
| Understand Bicep file structure and syntax | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/file |
| Configure artifacts parameters for Bicep linter compliance | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/linter-rule-artifacts-parameters |
| Use iterative loops to generate Bicep resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/loops |
| Define and use Bicep parameter files for deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/parameter-files |
| Configure resource dependencies in Bicep deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/resource-dependencies |
| Define Azure monitoring resources using Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/scenarios-monitoring |
| Configure Azure virtual networks using Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/scenarios-virtual-networks |
| Set scope for extension resources in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/scope-extension-resources |
| Create and use user-defined functions in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/user-defined-functions |
| Use built-in Azure Policy definitions for custom providers | https://learn.microsoft.com/en-us/azure/azure-resource-manager/custom-providers/policy-reference |
| Configure cache custom resources for Azure Custom Providers | https://learn.microsoft.com/en-us/azure/azure-resource-manager/custom-providers/proxy-cache-resource-endpoint-reference |
| Configure proxy custom resources for Azure Custom Providers | https://learn.microsoft.com/en-us/azure/azure-resource-manager/custom-providers/proxy-resource-endpoint-reference |
| Track long-running Azure operations via ARM async status | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/async-operations |
| Map Azure services to Resource Manager provider namespaces | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/azure-services-resource-providers |
| Configure Azure Resource Manager for EU data boundary | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-data-boundary |
| Configure monitoring and alerts for Azure Resource Manager | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/monitor-resource-manager |
| Reference metrics and logs for monitoring Azure Resource Manager | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/monitor-resource-manager-reference |
| Use built-in Azure Policy definitions for ARM governance | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/policy-reference |
| Configure and manage Azure preview features via Microsoft.Features | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/preview-features |
| Use Resource Group insights to monitor application health | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/resource-group-insights |
| Manage and delete personal data in Azure Resource Manager | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/resource-manager-personal-data |
| Discover Azure resource providers, types, and API versions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/resource-providers-and-types |
| Enforce tag compliance with Azure Policy definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-policies |
| Configure resource tags using Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-resources-bicep |
| Configure tags in ARM templates during deployment | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-resources-templates |
| Configure dev environment for ARM deployment scripts | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deployment-script-template-configure-dev |
| Use supported Form view UI elements in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-elements |
| Configure Grid UI element in Form view | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-grid |
| Configure LocationSelector element for ARM forms | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-locationselector |
| Configure ManagementGroupSelector in Form view | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-managementgroupselector |
| Configure ResourceGroupSelector in Azure Form view | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-resourcegroupselector |
| Configure ResourceScope element for ARM deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-resourcescope |
| Configure SubscriptionSelector in Form view templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-subscriptionselector |
| Configure TenantSelector for tenant-scope deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-common-tenantselector |
| Configure BladeInvokeControl element in Form view | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-microsoft-solutions-bladeinvokecontrol |
| Author Azure portal Form view JSON definitions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/form-view-overview |
| Create and use ARM template parameter files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/parameter-files |
| Configure scope for ARM extension resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/scope-extension-resources |
| Understand template function behavior in scoped deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/scope-functions |
| Configure ARM template structure and JSON sections | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/syntax |
| Author ARM templates reusable across Azure clouds | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-cloud-consistency |
| Use deployment functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-deployment |
| Define Azure portal Form view JSON for template specs | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-specs-create-portal-forms |
| Update Visual Studio ARM deployment to Az PowerShell | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/update-visual-studio-deployment-script |
| Configure and manage Azure Service Group membership at scale | https://learn.microsoft.com/en-us/azure/governance/service-groups/manage-membership |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Bicep CLI commands with Azure CLI and PowerShell | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-cli |
| Use Bicep CLI jsonrpc for programmatic tooling integration | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-cli-jsonrpc |
| Use Bicep any() to bypass type checking | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-any |
| Use Azure Bicep array functions in templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-array |
| Manipulate CIDR IP ranges in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-cidr |
| Work with date functions in Bicep files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-date |
| Retrieve deployment metadata with Bicep functions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-deployment |
| Load external file content in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-files |
| Control Bicep deployment flow with fail() | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-flow-control |
| Use lambda expressions and functions in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-lambda |
| Apply logical functions and bool() in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-logical |
| Use numeric functions and operators in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-numeric |
| Work with object functions in Bicep templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-object |
| Use functions in Bicep parameters files | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-parameters-file |
| Retrieve Azure resource values with Bicep functions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-resource |
| Get deployment scope values using Bicep functions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-scope |
| Use Azure Bicep string functions in templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-functions-string |
| Deploy Kubernetes resources to AKS using Bicep extension | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/bicep-kubernetes-extension |
| Map JSON ARM template syntax to Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/compare-template-syntax |
| Use Key Vault secrets as Bicep deployment parameters | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/key-vault-parameter |
| Convert Bicep to JSON ARM templates with MSBuild | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/msbuild-bicep-file |
| Use the Bicep null-forgiving operator safely | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operator-null-forgiving |
| Prevent null reference errors with Bicep safe-dereference | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operator-safe-dereference |
| Expand arrays and objects with Bicep spread operator | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operator-spread |
| Use core Bicep operators in ARM deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operators |
| Access resources and properties with Bicep accessor operators | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operators-access |
| Compare values using Bicep comparison operators | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operators-comparison |
| Evaluate conditions with Bicep logical operators | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operators-logical |
| Perform calculations with Bicep numeric operators | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/operators-numeric |
| Build C# Azure Function endpoints for custom providers | https://learn.microsoft.com/en-us/azure/azure-resource-manager/custom-providers/reference-custom-providers-csharp-endpoint |
| Manage Azure resource groups using Azure CLI | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resource-groups-cli |
| Manage Azure resource groups with PowerShell cmdlets | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resource-groups-powershell |
| Create and manage resource groups using Python SDK | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resource-groups-python |
| Deploy and manage Azure resources using Azure CLI | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resources-cli |
| Deploy and manage Azure resources with PowerShell | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resources-powershell |
| Manage Azure resources programmatically with Python and ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resources-python |
| Manage Azure resources via ARM REST API operations | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/manage-resources-rest |
| Sample Azure Resource Graph queries for ARM resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/resource-graph-samples |
| Tag Azure resources using Azure CLI commands | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-resources-cli |
| Manage Azure resource tags with PowerShell | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-resources-powershell |
| Tag Azure resources programmatically with Python SDK | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/tag-resources-python |
| Use built-in functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions |
| Use ARM template array functions in deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-array |
| Use CIDR functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-cidr |
| Use comparison functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-comparison |
| Work with date functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-date |
| Use lambda functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-lambda |
| Apply logical functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-logical |
| Use numeric functions in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-numeric |
| Manipulate objects with ARM template functions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-object |
| Retrieve resource values with ARM functions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-resource |
| Get deployment scope values in ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-scope |
| Use ARM template string functions effectively | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-functions-string |
| Deploy VM Custom Script extensions with ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/template-tutorial-deploy-vm-extensions |
| Use Azure Resource Graph queries for management groups | https://learn.microsoft.com/en-us/azure/governance/management-groups/resource-graph-samples |
| Add Azure Service Group members via REST API | https://learn.microsoft.com/en-us/azure/governance/service-groups/create-service-group-member-rest-api |
| Create Azure Service Groups using REST API | https://learn.microsoft.com/en-us/azure/governance/service-groups/create-service-group-rest-api |
| Run Azure Resource Graph queries for Service Groups | https://learn.microsoft.com/en-us/azure/governance/service-groups/resource-graph-samples |

### Deployment
| Topic | URL |
|-------|-----|
| Create Azure resource groups using Bicep deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/create-resource-group |
| Use deploymentScripts resources in Bicep deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-script-bicep |
| Develop and structure deployment scripts in Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-script-develop |
| Manage Azure deployment stacks using Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/deployment-stacks |
| Set up a private Azure container registry for Bicep modules | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/private-module-registry |
| Create and deploy ARM template specs with Bicep | https://learn.microsoft.com/en-us/azure/azure-resource-manager/bicep/template-specs |
| Move Azure App Service across subscriptions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-limitations/app-service-move-limitations |
| Move classic Azure resources with ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-limitations/classic-model-move-limitations |
| Move Cloud Services (extended support) resources | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-limitations/cloud-services-extended-support |
| Handle special cases when moving Azure VMs | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-limitations/virtual-machines-move-limitations |
| Execute ARM move operations between subscriptions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/move-resource-group-and-subscription |
| Cut over Azure workloads after migration | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocate-cutover |
| Migrate Azure workloads to a new region | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocate-migrate |
| Relocate Azure Application Gateway and WAF between regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-app-gateway |
| Relocate Azure App Service to another region | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-app-service |
| Relocate Azure Automation accounts across regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-automation |
| Relocate Azure Backup protection to another region | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-backup |
| Relocate Azure Container Registry or use geo-replication | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-container-registry |
| Relocate Azure Cosmos DB NoSQL accounts regionally | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-cosmos-db |
| Relocate Azure Event Grid custom topics regionally | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-event-grid-custom-topics |
| Relocate Azure Event Grid domains via ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-event-grid-domains |
| Relocate Azure Event Grid system topics to new regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-event-grid-system-topics |
| Relocate Azure Event Hubs namespaces by template | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-event-hub |
| Relocate Azure Event Hubs dedicated clusters | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-event-hub-cluster |
| Relocate Azure Firewall protecting a virtual network | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-firewall |
| Relocate Azure Functions apps between regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-functions |
| Relocate Azure HDInsight clusters across regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-hdinsight |
| Work around lack of Azure Key Vault relocation | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-key-vault |
| Relocate Azure Kubernetes Service clusters by region | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-kubernetes-service |
| Relocate Log Analytics workspaces and reconfigure senders | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-log-analytics |
| Relocate Azure NetApp Files volumes across regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-netapp |
| Relocate Azure Database for PostgreSQL across regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-postgresql-flexible-server |
| Relocate Azure Private Link Service to new regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-private-link |
| Relocate Recovery Services vault and Site Recovery | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-site-recovery |
| Relocate Azure Static Web Apps to new regions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-static-web-apps |
| Relocate Azure Virtual Machine Scale Sets regionally | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-virtual-machine-scale-sets |
| Relocate Azure Virtual Networks using ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-virtual-network |
| Relocate Azure Network Security Groups via templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/management/relocation/relocation-virtual-network-nsg |
| Configure Azure Pipelines CI/CD for ARM templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/add-template-to-azure-pipelines |
| Create and deploy ARM projects in Visual Studio | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/create-visual-studio-deployment-project |
| Deploy ARM templates with Azure CLI | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-cli |
| Deploy ARM templates from Azure Cloud Shell | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-cloud-shell |
| Deploy ARM templates using GitHub Actions | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-github-actions |
| Deploy ARM templates using Azure portal | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-portal |
| Deploy ARM templates with Azure PowerShell | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-powershell |
| Deploy ARM templates using Python SDK | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-python |
| Deploy ARM templates via Azure REST API | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-rest |
| Use Deploy to Azure button for remote templates | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-to-azure-button |
| Deploy ARM templates at management group scope | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-to-management-group |
| Deploy ARM templates to one or many resource groups | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-to-resource-group |
| Deploy ARM templates at tenant scope | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-to-tenant |
| Use what-if analysis for ARM template changes | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deploy-what-if |
| Understand complete mode deletion behavior in ARM | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/deployment-complete-mode-deletion |
| Use linked and nested ARM templates for modular deployments | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/linked-templates |
| Configure rollback to previous ARM deployments on error | https://learn.microsoft.com/en-us/azure/azure-resource-manager/templates/rollback-on-error |