---
name: azure-active-directory-b2c
description: Expert knowledge for Azure Active Directory B2C development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building B2C user flows/custom policies, configuring IdPs/MFA, securing APIs, automating CI/CD, or monitoring with Sentinel, and other Azure Active Directory B2C related development tasks. Not for Azure Role-based access control (use azure-rbac), Azure Information Protection (use azure-information-protection), Azure Security (use azure-security), Azure Sentinel (use azure-sentinel).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-14"
  generator: "docs2skills/1.0.0"
---
# Azure Active Directory B2C Skill

This skill provides expert guidance for Azure Active Directory B2C. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L43 | Diagnosing and fixing Azure AD B2C errors, debugging custom policies and user flows, and using Application Insights to trace and troubleshoot policy execution. |
| Best Practices | L44-L52 | Best practices for configuring Azure AD B2C, designing user flows/custom policies, securing MFA and architecture, and detecting/mitigating credential and account attacks. |
| Decision Making | L53-L60 | Guidance on planning Azure AD B2C usage: choosing app types, understanding MAU billing, regions/data residency, retirement impact, and selecting a user migration strategy. |
| Architecture & Design Patterns | L61-L69 | Global Azure AD B2C customer identity architectures, comparing funnel- vs region-based designs, and step-by-step proof-of-concept implementations for each pattern |
| Limits & Quotas | L70-L77 | Service limits, quotas, and restrictions for Azure AD B2C tenants, including directory size, token formats/constraints, and tenant creation and scaling limits. |
| Security | L78-L94 | Security hardening for Azure AD B2C: MFA, Conditional Access, Identity Protection, CAPTCHA, TLS/ciphers, policy keys, admin/tenant access control, API security, and Sentinel-based monitoring. |
| Configuration | L95-L209 | Configuring Azure AD B2C: custom policies, user flows, tokens, MFA, identity providers, claims/transformations, app/API registration, UI/localization, SSO, security, and advanced auth options. |
| Integrations & Coding Patterns | L210-L322 | Patterns and step-by-step guides for integrating Azure AD B2C into apps, securing APIs, configuring IdPs/social logins, custom policies, fraud/risk tools, and routing logs/monitoring. |
| Deployment | L323-L327 | Automating deployment of Azure AD B2C custom policies using CI/CD pipelines, including setup steps, YAML examples, and best practices for Azure Pipelines and GitHub Actions. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Azure AD B2C error codes and troubleshooting reference | https://learn.microsoft.com/en-us/azure/active-directory-b2c/error-codes |
| Troubleshoot Azure AD B2C custom policies and user flows | https://learn.microsoft.com/en-us/azure/active-directory-b2c/troubleshoot |
| Troubleshoot Azure AD B2C custom policies with Application Insights | https://learn.microsoft.com/en-us/azure/active-directory-b2c/troubleshoot-with-application-insights |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Azure AD B2C integration and configuration best practices | https://learn.microsoft.com/en-us/azure/active-directory-b2c/best-practices |
| Developer guidance for Azure AD B2C user flows and custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policy-developer-notes |
| Secure phone-based MFA in Azure AD B2C using monitoring and alerts | https://learn.microsoft.com/en-us/azure/active-directory-b2c/phone-based-mfa |
| Apply security best practices to Azure AD B2C architecture | https://learn.microsoft.com/en-us/azure/active-directory-b2c/security-architecture |
| Mitigate credential attacks in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/threat-management |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose appropriate application types for Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/application-types |
| Understand Azure AD B2C MAU billing and tier selection | https://learn.microsoft.com/en-us/azure/active-directory-b2c/billing |
| Plan Azure AD B2C region availability and data residency | https://learn.microsoft.com/en-us/azure/active-directory-b2c/data-residency |
| Choose a user migration approach to Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/user-migration |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Apply funnel-based global identity design with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/b2c-global-identity-funnel-based-design |
| Implement funnel-based global identity proof of concept in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/b2c-global-identity-proof-of-concept-funnel |
| Implement region-based global identity proof of concept in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/b2c-global-identity-proof-of-concept-regional |
| Apply region-based global identity design with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/b2c-global-identity-region-based-design |
| Design a global customer identity solution with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/b2c-global-identity-solutions |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review Azure AD B2C service limits and restrictions | https://learn.microsoft.com/en-us/azure/active-directory-b2c/service-limits |
| Monitor and manage Azure AD B2C directory size quota | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tenant-management-directory-quota |
| Understand Azure AD B2C token types, contents, and constraints | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tokens-overview |
| Create Azure AD B2C tenant and understand tenant limits | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tutorial-create-tenant |

### Security
| Topic | URL |
|-------|-----|
| Enable CAPTCHA protection in Azure AD B2C user flows and policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-captcha |
| Use Identity Protection and Conditional Access with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/conditional-access-identity-protection-overview |
| Add Conditional Access and MFA to Azure AD B2C user flows | https://learn.microsoft.com/en-us/azure/active-directory-b2c/conditional-access-user-flow |
| Configure Microsoft Sentinel analytics for Azure AD B2C logs | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-security-analytics-sentinel |
| Configure TLS and cipher suite requirements for Azure AD B2C endpoints | https://learn.microsoft.com/en-us/azure/active-directory-b2c/https-cipher-tls-requirements |
| Investigate and remediate identity risk in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-protection-investigate-risk |
| Enable and configure multifactor authentication in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/multi-factor-authentication |
| Manage Azure AD B2C policy keys for secure token signing | https://learn.microsoft.com/en-us/azure/active-directory-b2c/policy-keys-overview |
| Assign Azure AD B2C roles for resource access control | https://learn.microsoft.com/en-us/azure/active-directory-b2c/roles-resource-access-control |
| Secure REST APIs used by Azure AD B2C API connectors | https://learn.microsoft.com/en-us/azure/active-directory-b2c/secure-rest-api |
| Control tenant creation permissions in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tenant-management-check-tenant-creation-permission |
| Configure emergency access administrator accounts in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tenant-management-emergency-access-account |
| Manage administrator accounts in Azure AD B2C tenants | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tenant-management-manage-administrator |

### Configuration
| Topic | URL |
|-------|-----|
| Configure SSPR technical profiles in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/aad-sspr-technical-profile |
| Configure Microsoft Entra technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/active-directory-technical-profile |
| Add and configure API connectors in Azure AD B2C sign-up flows | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-api-connector |
| Configure token enrichment with external APIs in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-api-connector-token-enrichment |
| Add external identity providers to Azure AD B2C tenant | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-identity-provider |
| Add and configure native client apps in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-native-application |
| Configure Azure AD B2C custom policy for password change | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-password-change-policy |
| Configure password reset user flows in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-password-reset-policy |
| Configure profile editing user flows in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-profile-editing-policy |
| Configure resource owner password credentials (ROPC) flow in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-ropc-policy |
| Configure sign-in-only user flows in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-sign-in-policy |
| Configure sign-up and sign-in user flows in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-sign-up-and-sign-in-policy |
| Register and expose a web API in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/add-web-api-application |
| Enable age gating policies in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/age-gating |
| Track Azure AD B2C user journeys with Application Insights | https://learn.microsoft.com/en-us/azure/active-directory-b2c/analytics-with-application-insights |
| Migrate Azure AD B2C apps and APIs to b2clogin.com | https://learn.microsoft.com/en-us/azure/active-directory-b2c/b2clogin |
| Use boolean claims transformations in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/boolean-transformations |
| Configure BuildingBlocks section in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/buildingblocks |
| Configure CAPTCHA technical profiles in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/captcha-technical-profile |
| Use claim resolvers in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/claim-resolver-overview |
| Define claims transformation technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/claims-transformation-technical-profile |
| Configure ClaimsProvider elements in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/claimsproviders |
| Define ClaimsSchema and claim types in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/claimsschema |
| Configure ClaimsTransformations in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/claimstransformations |
| Configure OAuth 2.0 client credentials flow in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/client-credentials-grant-flow |
| Configure Conditional Access technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/conditional-access-technical-profile |
| Configure Azure AD B2C authentication in Azure Web App via configuration file | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-in-azure-web-app-file-based |
| Configure token lifetimes and formats in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-tokens |
| Configure user attributes and input fields in Azure AD B2C journeys | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-user-input |
| Configure ContentDefinitions in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/contentdefinitions |
| Understand Azure AD B2C cookie definitions and behavior | https://learn.microsoft.com/en-us/azure/active-directory-b2c/cookie-definitions |
| Enable and configure custom domains in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-domain |
| Create and deploy a basic Azure AD B2C custom policy | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-hello-world |
| Validate Azure AD B2C custom policies with VS Code schema | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-install-xml-extensions |
| Configure Azure AD B2C custom policies with Identity Experience Framework | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policy-overview |
| Configure single sign-on session providers in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policy-reference-sso |
| Customize Azure AD B2C user interface branding | https://learn.microsoft.com/en-us/azure/active-directory-b2c/customize-ui |
| Use date claims transformations in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/date-transformations |
| Set up direct sign-in and prefilled usernames in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/direct-signin |
| Disable email verification during Azure AD B2C sign-up | https://learn.microsoft.com/en-us/azure/active-directory-b2c/disable-email-verification |
| Configure CAPTCHA display controls in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/display-control-captcha |
| Configure TOTP display controls for MFA in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/display-control-time-based-one-time-password |
| Configure verification display controls for claims in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/display-control-verification |
| Configure display controls in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/display-controls |
| Configure advanced Android authentication options in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-android-app-options |
| Configure advanced authentication options for Angular SPAs with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-angular-spa-app-options |
| Configure advanced Azure AD B2C authentication options for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-azure-static-app-options |
| Configure advanced authentication options for Node.js web apps with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-in-node-web-app-options |
| Configure Node.js API authentication options in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-in-node-web-app-with-api-options |
| Configure advanced iOS Swift authentication options in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-ios-app-options |
| Configure advanced authentication options for Python web apps with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-python-web-app-options |
| Configure advanced authentication options for React SPAs with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-react-spa-app-options |
| Customize SPA authentication options with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-spa-app-options |
| Customize web app authentication options in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-web-app-with-api-options |
| Configure advanced authentication options for ASP.NET web apps with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-web-application-options |
| Customize WPF desktop authentication options in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-wpf-desktop-app-options |
| Restore and manage the Azure AD B2C extensions app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/extensions-app |
| Configure forced password reset flows in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/force-password-reset |
| Use general claims transformations in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/general-transformations |
| Configure ID token hint technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/id-token-hint |
| Configure advanced SAML identity provider options in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-generic-saml-options |
| Configure Azure AD B2C local account identity provider | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-local |
| Pass identity provider access tokens through Azure AD B2C user flows | https://learn.microsoft.com/en-us/azure/active-directory-b2c/idp-pass-through-user-flow |
| Use integer claims transformations in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/integer-transformations |
| Enable JavaScript and select page layout versions in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/javascript-and-page-layout |
| Use JSON claims transformations in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/json-transformations |
| Configure JWT issuer technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/jwt-issuer-technical-profile |
| Configure language customization for Azure AD B2C user flows | https://learn.microsoft.com/en-us/azure/active-directory-b2c/language-customization |
| Configure Localization element in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/localization |
| Use localization string IDs for Azure AD B2C signup/signin | https://learn.microsoft.com/en-us/azure/active-directory-b2c/localization-string-ids |
| Manage Azure AD B2C custom policies with Microsoft Graph PowerShell | https://learn.microsoft.com/en-us/azure/active-directory-b2c/manage-custom-policies-powershell |
| Configure user access controls in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/manage-user-access |
| Delete and export user data in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/manage-user-data |
| Register a Microsoft Graph management app for Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/microsoft-graph-get-started |
| Configure multifactor authentication technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/multi-factor-auth-technical-profile |
| Configure OAuth1 technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/oauth1-technical-profile |
| Configure OAuth2 custom error technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/oauth2-error-technical-profile |
| Configure OAuth2 technical profiles in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/oauth2-technical-profile |
| Enable one-time password verification with Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/one-time-password-technical-profile |
| Configure OpenID Connect technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/openid-connect-technical-profile |
| Edit Azure AD B2C custom policy XML with Grit Visual Editor | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-grit-editor |
| Configure password complexity policies in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/password-complexity |
| Enable phone-based sign-up and sign-in in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/phone-authentication-user-flows |
| Configure phone factor technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/phone-factor-technical-profile |
| Configure phone number claims transformations in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/phone-number-claims-transformations |
| Configure Predicates and PredicateValidations in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/predicates |
| Publish an Azure AD B2C app to the Entra app gallery | https://learn.microsoft.com/en-us/azure/active-directory-b2c/publish-app-to-azure-ad-app-gallery |
| Register and configure applications in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/register-apps |
| Configure RelyingParty elements in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/relyingparty |
| Configure RESTful technical profiles in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/restful-technical-profile |
| Configure SAML identity provider technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/saml-identity-provider-technical-profile |
| Configure SAML issuer technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/saml-issuer-technical-profile |
| Configure Azure AD B2C as a SAML identity provider | https://learn.microsoft.com/en-us/azure/active-directory-b2c/saml-service-provider |
| Configure Azure AD B2C SAML service provider options | https://learn.microsoft.com/en-us/azure/active-directory-b2c/saml-service-provider-options |
| Configure self-asserted technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/self-asserted-technical-profile |
| Configure Azure AD B2C session and SSO behavior | https://learn.microsoft.com/en-us/azure/active-directory-b2c/session-behavior |
| Use social account claims transformations in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/social-transformations |
| Use string claims transformations in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/string-transformations |
| Use StringCollection claims transformations in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/stringcollection-transformations |
| Configure sub journeys in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/subjourneys |
| Configure technical profiles in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/technicalprofiles |
| Define TrustFrameworkPolicy elements in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/trustframeworkpolicy |
| Register a single-page application in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/tutorial-register-spa |
| Define and manage custom user attributes in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/user-flow-custom-attributes |
| Select and configure Azure AD B2C user flow versions | https://learn.microsoft.com/en-us/azure/active-directory-b2c/user-flow-versions |
| Use legacy Azure AD B2C user flow versions | https://learn.microsoft.com/en-us/azure/active-directory-b2c/user-flow-versions-legacy |
| Use and extend Azure AD B2C user profile attributes | https://learn.microsoft.com/en-us/azure/active-directory-b2c/user-profile-attributes |
| Define and expose a UserInfo endpoint in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/userinfo-endpoint |
| Configure UserJourneys in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/userjourneys |
| Define validation technical profiles in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/validation-technical-profile |
| Access and review Azure AD B2C audit logs | https://learn.microsoft.com/en-us/azure/active-directory-b2c/view-audit-logs |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Request and use access tokens from Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/access-tokens |
| Extend Azure AD B2C user flows with API connectors | https://learn.microsoft.com/en-us/azure/active-directory-b2c/api-connectors-overview |
| Implement OAuth 2.0 authorization code flow in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/authorization-code-flow |
| Route Azure AD B2C logs to Azure Monitor | https://learn.microsoft.com/en-us/azure/active-directory-b2c/azure-monitor |
| Integrate Azure AD B2C authentication into a sample Node.js web app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-a-sample-node-web-app |
| Integrate Azure AD B2C authentication into an Azure Static Web App | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-in-azure-static-app |
| Integrate Azure AD B2C authentication into an Azure Web App | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-in-azure-web-app |
| Configure Node.js web app and API with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-in-sample-node-web-app-with-api |
| Configure Azure AD B2C authentication in sample Android app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-android-app |
| Integrate Azure AD B2C authentication into an Angular SPA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-angular-spa-app |
| Configure Azure AD B2C authentication in sample iOS Swift app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-ios-app |
| Integrate Azure AD B2C authentication into a sample Python web app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-python-web-app |
| Integrate Azure AD B2C authentication into a React SPA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-react-spa-app |
| Integrate Azure AD B2C authentication into a sample JavaScript SPA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-spa-app |
| Integrate Azure AD B2C authentication into a sample ASP.NET web app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-web-app |
| Configure ASP.NET web app and API with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-web-app-with-api |
| Configure Azure AD B2C authentication in sample WPF app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/configure-authentication-sample-wpf-desktop-app |
| Customize Azure AD B2C verification emails using Mailjet | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-email-mailjet |
| Customize Azure AD B2C verification emails using SendGrid | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-email-sendgrid |
| Implement branching user journeys in Azure AD B2C policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-branch-user-journey |
| Call external REST APIs from Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-call-rest-api |
| Collect and process user input in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-collect-user-input |
| Configure local account sign-up and sign-in in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-sign-up-or-sign-in |
| Add social account sign-in to Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-sign-up-or-sign-in-federation |
| Create and read user accounts with Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-store-user |
| Validate user input in Azure AD B2C custom policies | https://learn.microsoft.com/en-us/azure/active-directory-b2c/custom-policies-series-validate-user-input |
| Embed Azure AD B2C login UI inside applications via custom policy | https://learn.microsoft.com/en-us/azure/active-directory-b2c/embedded-login |
| Enable Azure AD B2C authentication in your Android app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-android-app |
| Add Azure AD B2C authentication to your own Angular SPA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-angular-spa-app |
| Add Azure AD B2C authentication to your own Node.js web app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-in-node-web-app |
| Enable Node.js web app to call protected API via Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-in-node-web-app-with-api |
| Enable Azure AD B2C authentication in your iOS Swift app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-ios-app |
| Add Azure AD B2C authentication to your own Python web app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-python-web-app |
| Add Azure AD B2C authentication to your own React SPA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-react-spa-app |
| Implement Azure AD B2C building blocks in your own SPA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-spa-app |
| Protect a web API with Azure AD B2C access tokens | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-web-api |
| Enable ASP.NET Core web app authentication with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-web-app-with-api |
| Add Azure AD B2C authentication to your own ASP.NET web app | https://learn.microsoft.com/en-us/azure/active-directory-b2c/enable-authentication-web-application |
| Integrate AD FS as OpenID Connect IdP with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-adfs |
| Integrate AD FS as SAML identity provider with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-adfs-saml |
| Set up Amazon as social identity provider in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-amazon |
| Set up Apple ID sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-apple-id |
| Federate between Azure AD B2C tenants for sign-in | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-azure-ad-b2c |
| Configure multitenant Microsoft Entra ID as IdP in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-azure-ad-multi-tenant |
| Enable sign-in from a single Microsoft Entra tenant in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-azure-ad-single-tenant |
| Set up eBay account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-ebay |
| Set up Facebook account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-facebook |
| Configure generic OpenID Connect identity provider in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-generic-openid-connect |
| Configure generic SAML identity provider in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-generic-saml |
| Set up GitHub account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-github |
| Set up Google account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-google |
| Set up ID.me account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-id-me |
| Set up LinkedIn account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-linkedin |
| Set up Microsoft account sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-microsoft-account |
| Configure Mobile ID as Azure AD B2C identity provider | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-mobile-id |
| Integrate PingOne sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-ping-one |
| Configure QQ social login in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-qq |
| Set up Salesforce OAuth sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-salesforce |
| Configure Salesforce SAML provider for Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-salesforce-saml |
| Integrate SwissID sign-up and sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-swissid |
| Configure X (Twitter) sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-twitter |
| Configure WeChat login as Azure AD B2C identity provider | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-wechat |
| Set up Weibo social sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/identity-provider-weibo |
| Configure SPA sign-in using OAuth 2.0 implicit flow in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/implicit-flow-single-page-application |
| Manage Azure AD B2C resources using Microsoft Graph | https://learn.microsoft.com/en-us/azure/active-directory-b2c/microsoft-graph-operations |
| Support multiple token issuers in OWIN APIs during Azure AD B2C migration | https://learn.microsoft.com/en-us/azure/active-directory-b2c/multiple-token-endpoints |
| Implement OpenID Connect web sign-in with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/openid-connect |
| Protect Azure AD B2C with Akamai Web Application Protector | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-akamai |
| Configure Akamai Enterprise Application Access with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-akamai-secure-hybrid-access |
| Integrate Arkose Labs platform with Azure AD B2C to detect fraud | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-arkose-labs |
| Integrate Asignio MFA with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-asignio |
| Integrate Transmit Security hosted passkeys with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-bindid |
| Configure BioCatch behavioral biometrics with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-biocatch |
| Configure BlokSec passwordless authentication with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-bloksec |
| Use Cloudflare Web Application Firewall with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-cloudflare |
| Integrate Datawiza Access Proxy with Azure AD B2C for hybrid access | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-datawiza |
| Integrate Azure AD B2C with Deduce for fraud prevention | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-deduce |
| Integrate Dynamics 365 Fraud Protection with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-dynamics-365-fraud-protection |
| Configure Azure AD B2C with Bluink eID-Me | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-eid-me |
| Integrate Azure AD B2C with Experian CrossCore | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-experian |
| Enable secure hybrid access with F5 BIG-IP and Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-f5 |
| Migrate header-based legacy apps to Azure AD B2C using Grit app proxy | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-grit-app-proxy |
| Configure Grit biometric authentication with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-grit-authentication |
| Configure Grit IAM B2B2C with Azure AD B2C authentication | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-grit-iam |
| Integrate Haventec Authenticate passwordless MFA with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-haventec |
| Configure HYPR passwordless authentication with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-hypr |
| Integrate IDEMIA Mobile ID with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-idemia |
| Integrate Azure AD B2C with IDology ExpectID | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-idology |
| Integrate itsme OpenID Connect with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-itsme |
| Configure Azure AD B2C with Jumio ID verification | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-jumio |
| Configure Keyless passwordless authentication with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-keyless |
| Integrate Azure AD B2C with LexisNexis ThreatMetrix | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-lexisnexis |
| Integrate N8 Identity TheAccessHub with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-n8identity |
| Enable Nevis passwordless authentication in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-nevis |
| Configure Nok Nok S3 FIDO passkey authentication with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-nok-nok |
| Configure Azure AD B2C with Onfido document and biometric checks | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-onfido |
| Integrate Azure AD B2C with PingAccess and PingFederate | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-ping-identity |
| Integrate Saviynt Security Manager with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-saviynt |
| Integrate Azure AD B2C with Strata Maverics | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-strata |
| Configure Transmit Security risk detection with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-transmit-security |
| Add Trusona Authentication Cloud as an IdP in Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-trusona |
| Integrate Twilio Verify with Azure AD B2C for PSD2 SCA | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-twilio |
| Use TypingDNA behavioral biometrics with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-typingdna |
| Configure Azure Web Application Firewall for Azure AD B2C tenants | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-web-application-firewall |
| Configure WhoIAM BRIMS verification with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-whoiam |
| Configure WhoIAM Rampart with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-whoiam-rampart |
| Integrate xID digital ID passwordless auth with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-xid |
| Configure Zscaler Private Access with Azure AD B2C | https://learn.microsoft.com/en-us/azure/active-directory-b2c/partner-zscaler |
| Secure Azure API Management APIs with Azure AD B2C tokens | https://learn.microsoft.com/en-us/azure/active-directory-b2c/secure-api-management |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure AD B2C custom policies with Azure Pipelines | https://learn.microsoft.com/en-us/azure/active-directory-b2c/deploy-custom-policies-devops |
| Deploy Azure AD B2C custom policies with GitHub Actions | https://learn.microsoft.com/en-us/azure/active-directory-b2c/deploy-custom-policies-github-action |