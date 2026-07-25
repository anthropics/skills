---
name: azure-boards
description: Expert knowledge for Azure Boards development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. Use when managing work items/backlogs, queries/charts, GitHub/Office integrations, WIQL, or process templates, and other Azure Boards related development tasks. Not for Azure DevOps (use azure-devops), Azure Test Plans (use azure-test-plans), Azure Pipelines (use azure-pipelines), Azure Repos (use azure-repos).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Boards Skill

This skill provides expert guidance for Azure Boards. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L43 | Diagnosing and fixing Azure Boards issues with Office integration, backlog nesting/reordering, and common query problems (filters, clauses, results). |
| Best Practices | L44-L54 | Guidance on Agile/Scrum best practices in Azure Boards: work item management, scalable product and sprint planning, process customization, and querying for workflow/board changes. |
| Decision Making | L55-L61 | Guidance on selecting Azure Boards migration/integration options, cross-team reporting tools, and the best process template (Agile/Scrum/CMMI) for your project. |
| Limits & Quotas | L62-L67 | Managing limits, quotas, and recovery for Azure Boards test artifacts and work item attachments, including deletion, restoration, size/count constraints, and best practices. |
| Security | L68-L74 | Managing Azure Boards security: default permissions, configuring query/folder access, and setting access controls and policies for teams and users. |
| Configuration | L75-L85 | Configuring Azure Boards: work item fields and processes (Agile/Scrum/CMMI), bug/risk tracking, code review/feedback fields, query fields/macros, charts, and GitHub Enterprise integration. |
| Integrations & Coding Patterns | L86-L95 | Connecting Azure Boards to GitHub, Copilot, Slack, and Teams, adding status badges, linking work items to code/artifacts, and querying work items with WIQL syntax. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure DevOps Office integration issues | https://learn.microsoft.com/en-us/azure/devops/boards/backlogs/office/tfs-office-integration-issues?view=azure-devops |
| Troubleshoot Azure DevOps Office integration issues | https://learn.microsoft.com/en-us/azure/devops/boards/backlogs/office/tfs-office-integration-issues?view=azure-devops |
| Troubleshoot Azure DevOps Office integration issues | https://learn.microsoft.com/en-us/azure/devops/boards/backlogs/office/tfs-office-integration-issues?view=azure-devops |
| Troubleshoot Azure Boards backlog nesting and reordering | https://learn.microsoft.com/en-us/azure/devops/boards/backlogs/resolve-backlog-reorder-issues?view=azure-devops |
| Resolve common Azure Boards query issues | https://learn.microsoft.com/en-us/azure/devops/boards/queries/query-faqs?view=azure-devops |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Azure Boards work item management best practices | https://learn.microsoft.com/en-us/azure/devops/boards/backlogs/manage-work-items?view=azure-devops |
| Apply Azure Boards Agile product management practices | https://learn.microsoft.com/en-us/azure/devops/boards/best-practices-agile-project-management?view=azure-devops |
| Plan and configure Azure Boards process customization | https://learn.microsoft.com/en-us/azure/devops/boards/configure-customize?view=azure-devops |
| Apply scalable Agile practices in Azure Boards | https://learn.microsoft.com/en-us/azure/devops/boards/plans/practices-that-scale?view=azure-devops |
| Create queries for workflow and board changes | https://learn.microsoft.com/en-us/azure/devops/boards/queries/query-by-workflow-changes?view=azure-devops |
| Query work items by titles and rich-text fields | https://learn.microsoft.com/en-us/azure/devops/boards/queries/titles-ids-descriptions?view=azure-devops |
| Apply Azure Boards sprint and Scrum best practices | https://learn.microsoft.com/en-us/azure/devops/boards/sprints/best-practices-scrum?view=azure-devops |

### Decision Making
| Topic | URL |
|-------|-----|
| Select migration and integration options for Azure Boards | https://learn.microsoft.com/en-us/azure/devops/boards/extensions/migrate-integrate?view=azure-devops |
| Choose Azure Boards tools for cross-team visibility | https://learn.microsoft.com/en-us/azure/devops/boards/plans/visibility-across-teams?view=azure-devops |
| Choose the right Azure Boards process template | https://learn.microsoft.com/en-us/azure/devops/boards/work-items/guidance/choose-process?view=azure-devops |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Manage and restore deleted Azure Boards test artifacts | https://learn.microsoft.com/en-us/azure/devops/boards/backlogs/delete-test-artifacts?view=azure-devops |
| Manage Azure Boards work item attachments and limits | https://learn.microsoft.com/en-us/azure/devops/boards/work-items/manage-attachments?view=azure-devops |

### Security
| Topic | URL |
|-------|-----|
| Understand default permissions and access in Azure Boards | https://learn.microsoft.com/en-us/azure/devops/boards/get-started/permissions-access-boards?view=azure-devops |
| Configure query and folder permissions in Azure Boards | https://learn.microsoft.com/en-us/azure/devops/boards/queries/set-query-permissions?view=azure-devops |
| Secure Azure Boards with access controls and policies | https://learn.microsoft.com/en-us/azure/devops/boards/secure-your-azure-boards?view=azure-devops |

### Configuration
| Topic | URL |
|-------|-----|
| Configure on-premises Azure DevOps with GitHub Enterprise | https://learn.microsoft.com/en-us/azure/devops/boards/github/connect-on-premises-to-github?view=azure-devops-server |
| Configure Azure Boards query charts for dashboards | https://learn.microsoft.com/en-us/azure/devops/boards/queries/example-query-charts?view=azure-devops |
| Use Azure Boards query fields, operators, and macros | https://learn.microsoft.com/en-us/azure/devops/boards/queries/query-operators-variables?view=azure-devops |
| Track bugs, issues, and risks fields in CMMI process | https://learn.microsoft.com/en-us/azure/devops/boards/work-items/guidance/cmmi/guidance-bugs-issues-risks-field-reference-cmmi?view=azure-devops |
| Use code review and feedback fields in Azure Boards | https://learn.microsoft.com/en-us/azure/devops/boards/work-items/guidance/guidance-code-review-feedback-field-reference?view=azure-devops |
| Reference Agile and Scrum work item fields in Azure Boards | https://learn.microsoft.com/en-us/azure/devops/boards/work-items/guidance/work-item-field?view=azure-devops |
| Configure and manage Azure Boards work item fields | https://learn.microsoft.com/en-us/azure/devops/boards/work-items/work-item-fields?view=azure-devops |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Add Azure Boards status badges to GitHub repos | https://learn.microsoft.com/en-us/azure/devops/boards/github/configure-status-badges?view=azure-devops |
| Integrate Azure Boards projects with GitHub repositories | https://learn.microsoft.com/en-us/azure/devops/boards/github/connect-to-github?view=azure-devops |
| Integrate Azure Boards work items with GitHub artifacts | https://learn.microsoft.com/en-us/azure/devops/boards/github/link-to-from-github?view=azure-devops |
| Integrate GitHub Copilot with Azure Boards work items | https://learn.microsoft.com/en-us/azure/devops/boards/github/work-item-integration-github-copilot?view=azure-devops |
| Integrate Azure Boards with Slack channels | https://learn.microsoft.com/en-us/azure/devops/boards/integrations/boards-slack?view=azure-devops |
| Use Azure Boards with Microsoft Teams channels | https://learn.microsoft.com/en-us/azure/devops/boards/integrations/boards-teams?view=azure-devops |
| Use WIQL syntax for Azure Boards queries | https://learn.microsoft.com/en-us/azure/devops/boards/queries/wiql-syntax?view=azure-devops |