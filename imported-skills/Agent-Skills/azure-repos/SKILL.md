---
name: azure-repos
description: Expert knowledge for Azure Repos development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. Use when managing Git/TFVC repos, PR policies, branch permissions, Copilot reviews, or Advanced Security scanning, and other Azure Repos related development tasks. Not for Azure DevOps (use azure-devops), Azure Artifacts (use azure-artifacts), Azure Pipelines (use azure-pipelines), Azure Test Plans (use azure-test-plans).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Repos Skill

This skill provides expert guidance for Azure Repos. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L50 | Diagnosing and fixing Git/TFVC repo issues (locks, merge conflicts, push errors, undo/recovery) and troubleshooting CodeQL, dependency, and secret scanning in Azure DevOps/GitHub. |
| Best Practices | L51-L65 | Git and TFVC best practices: branching, merges, large files, history cleanup, cross‑platform compatibility, author/identity management, repo health, and post‑migration validation. |
| Decision Making | L66-L73 | Guidance on choosing and migrating version control in Azure DevOps: Git vs TFVC, local vs server workspaces, mixed Git/TFVC use, and migration paths from TFVC/SVN to Git or GitHub. |
| Architecture & Design Patterns | L74-L82 | Designing and choosing TFVC branching structures/strategies, planning strategic branches, implementing feature isolation, and managing branches for DevOps workflows in Azure Repos. |
| Limits & Quotas | L83-L90 | Limits, quotas, and monitoring for Azure Repos: Git repo size/usage limits, Enterprise Live Migration cutover/sync windows, and supported ecosystems for GitHub Advanced Security dependency scanning. |
| Security | L91-L118 | Securing Azure Repos and TFVC: auth methods (PAT/SSH/Entra, credential managers, Xcode/Go), permissions, branch policies/locks, secure imports, and GitHub Advanced Security setup and management. |
| Configuration | L119-L153 | Configuring Azure Repos/DevOps behavior: PR policies, notifications, Copilot reviews, Git/TFVC settings, check-in policies, workspaces, and GitHub Advanced Security scanning. |
| Integrations & Coding Patterns | L154-L205 | Integrating Azure Repos with CLIs, IDEs, notifications, and scanners, plus detailed TFVC/tf.exe commands and Git permissions for automating and extending repo workflows |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and resolve Azure DevOps ELM migration errors | https://learn.microsoft.com/en-us/azure/devops/repos/enterprise-live-migrations/troubleshoot?view=azure-devops |
| Handle Git index.lock issues in Visual Studio and Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/git-index-lock?view=azure-devops |
| Troubleshoot Git issues in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/howto?view=azure-devops |
| Troubleshoot and resolve Git merge conflicts in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/merging?view=azure-devops |
| Fix RPC failure errors when pushing to Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/rpc-failures-http-postbuffer?view=azure-devops |
| Undo and recover Git changes in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/undo?view=azure-devops |
| Troubleshoot CodeQL code scanning in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-code-scanning-troubleshoot?view=azure-devops |
| Troubleshoot dependency scanning in GitHub Advanced Security | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-dependency-scanning-troubleshoot?view=azure-devops |
| Troubleshoot secret scanning issues in GitHub Advanced Security | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-secret-scanning-troubleshoot?view=azure-devops |
| Resolve TFVC file and merge conflicts effectively | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/resolve-team-foundation-version-control-conflicts?view=azure-devops |
| Resolve TFVC locks and undo changes in other workspaces | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/undo-changes-another-user-workspace?view=azure-devops |

### Best Practices
| Topic | URL |
|-------|-----|
| Complete, abandon, or revert Azure Repos pull requests | https://learn.microsoft.com/en-us/azure/devops/repos/git/complete-pull-requests?view=azure-devops |
| Adopt effective Git branching strategies in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/git-branching-guidance?view=azure-devops |
| Manage author names and emails for Azure Repos commits | https://learn.microsoft.com/en-us/azure/devops/repos/git/git-names?view=azure-devops |
| Configure Git ignore rules for Azure Repos projects | https://learn.microsoft.com/en-us/azure/devops/repos/git/ignore-files?view=azure-devops |
| Manage large binary files in Azure Repos Git | https://learn.microsoft.com/en-us/azure/devops/repos/git/manage-large-files?view=azure-devops |
| Choose merge strategies and use squash merges in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/merging-with-squash?view=azure-devops |
| Ensure cross-platform Git compatibility in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/os-compatibility?view=azure-devops |
| Remove large binaries from Azure Repos Git history | https://learn.microsoft.com/en-us/azure/devops/repos/git/remove-binaries?view=azure-devops |
| Maintain healthy Git repositories in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/repo-health?view=azure-devops |
| Clean up TFVC workspaces and files when users leave | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/clean-up-files-when-users-leave?view=azure-devops |
| Optimize TFVC workspaces for performance | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/optimize-your-workspace?view=azure-devops |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and execute TFVC to Git migration in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/git/import-from-tfvc?view=azure-devops |
| Decide how to migrate from SVN to Git in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/git/perform-migration-from-svn-to-git?view=azure-devops |
| Choose between Git and TFVC in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/comparison-git-tfvc?view=azure-devops |
| Choose between local and server TFVC workspaces | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/decide-between-using-local-server-workspace?view=azure-devops |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design TFVC branch structures for teams | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/branch-folders-files?view=azure-devops |
| Plan strategic branching in TFVC | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/branch-strategically?view=azure-devops |
| Choose effective TFVC branching strategies | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/branching-strategies-with-tfvc?view=azure-devops |
| Implement feature isolation strategy in TFVC | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/effective-feature-isolation-on-tfvc?view=azure-devops |
| Manage TFVC branching for DevOps workflows | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/effective-tfvc-branching-strategies-for-devops?view=azure-devops |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Execute cutover for Enterprise Live Migrations | https://learn.microsoft.com/en-us/azure/devops/repos/enterprise-live-migrations/cut-over-to-github?view=azure-devops |
| Monitor Enterprise Live Migration sync windows | https://learn.microsoft.com/en-us/azure/devops/repos/enterprise-live-migrations/monitor-migration?view=azure-devops |
| Git repository limits and quotas in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/limits?view=azure-devops |
| Supported ecosystems for GitHub Advanced Security dependency scanning | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-dependency-scanning-ecosystems?view=azure-devops |

### Security
| Topic | URL |
|-------|-----|
| Manage Azure Repos pull requests and permissions | https://learn.microsoft.com/en-us/azure/devops/repos/git/about-pull-requests?view=azure-devops |
| Authenticate to Azure Repos Git with Entra, PAT, or SSH | https://learn.microsoft.com/en-us/azure/devops/repos/git/auth-overview?view=azure-devops |
| Set Azure Repos Git branch permissions and access | https://learn.microsoft.com/en-us/azure/devops/repos/git/branch-permissions?view=azure-devops |
| Configure Azure Repos Git branch policies securely | https://learn.microsoft.com/en-us/azure/devops/repos/git/branch-policies?view=azure-devops |
| Clone Azure Repos Git repositories with secure authentication | https://learn.microsoft.com/en-us/azure/devops/repos/git/clone?view=azure-devops |
| Secure Azure Repos SSH keys with passphrases | https://learn.microsoft.com/en-us/azure/devops/repos/git/gcm-ssh-passphrase?view=azure-devops |
| Authenticate Go install with Azure Repos Git | https://learn.microsoft.com/en-us/azure/devops/repos/git/go-install?view=azure-devops |
| Securely import external Git repositories into Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/import-git-repository?view=azure-devops |
| Lock Azure Repos Git branches to prevent updates | https://learn.microsoft.com/en-us/azure/devops/repos/git/lock-branches?view=azure-devops |
| Enforce branch folder structure and secure auth in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/require-branch-folders?view=azure-devops |
| Secure Azure Repos with permissions and policies | https://learn.microsoft.com/en-us/azure/devops/repos/git/secure-repositories-pull-requests?view=azure-devops |
| Configure Azure Repos Git repository permissions | https://learn.microsoft.com/en-us/azure/devops/repos/git/set-git-repository-permissions?view=azure-devops |
| Securely authenticate to Azure Repos with credential managers | https://learn.microsoft.com/en-us/azure/devops/repos/git/set-up-credential-managers?view=azure-devops |
| Configure secure authentication for Xcode with Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/share-your-code-in-git-xcode?view=azure-devops |
| Configure SSH key authentication for Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/use-ssh-keys-to-authenticate?view=azure-devops |
| Configure GitHub Advanced Security in Azure DevOps Repos | https://learn.microsoft.com/en-us/azure/devops/repos/security/configure-github-advanced-security-features?view=azure-devops |
| Use Copilot Autofix for CodeQL alerts in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-code-scanning-autofix?view=azure-devops |
| Configure GitHub Advanced Security code scanning in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-code-scanning?view=azure-devops |
| Manage permissions for GitHub Advanced Security in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-permissions?view=azure-devops |
| Control TFVC access with permissions and inheritance | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/control-access-team-foundation-version-control?view=azure-devops |
| Permanently destroy TFVC version-controlled files safely | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/destroy-version-controlled-files?view=azure-devops |
| Use TFVC permission command to manage ACLs | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/permission-command?view=azure-devops |
| Remove or restrict access to TFVC version-controlled files | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/remove-access-version-control-files?view=azure-devops |
| Configure TFVC repository permissions and access control | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/set-tfvc-repository-permissions?view=azure-devops |

### Configuration
| Topic | URL |
|-------|-----|
| Configure prerequisites for Enterprise Live Migrations | https://learn.microsoft.com/en-us/azure/devops/repos/enterprise-live-migrations/prerequisites?view=azure-devops |
| Configure and start Enterprise Live Migration sync | https://learn.microsoft.com/en-us/azure/devops/repos/enterprise-live-migrations/start-migration?view=azure-devops |
| Configure Azure DevOps pull request status checks | https://learn.microsoft.com/en-us/azure/devops/repos/git/available-pr-status-checks?view=azure-devops |
| Configure Azure Repos Git branch policies for code quality | https://learn.microsoft.com/en-us/azure/devops/repos/git/branch-policies-overview?view=azure-devops |
| Use Visual Studio Git commands and Azure DevOps integration | https://learn.microsoft.com/en-us/azure/devops/repos/git/command-prompt?view=azure-devops |
| Enable and configure Copilot PR reviews in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/copilot-code-reviews?view=azure-devops |
| Configure Git preferences and config files in Visual Studio | https://learn.microsoft.com/en-us/azure/devops/repos/git/git-config?view=azure-devops |
| Configure external status branch policies in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/pr-status-policy?view=azure-devops |
| Configure Azure Repos pull request notification subscriptions | https://learn.microsoft.com/en-us/azure/devops/repos/git/pull-request-notifications?view=azure-devops |
| Configure custom pull request target branches in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/pull-request-targets?view=azure-devops |
| Configure pull request templates in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/pull-request-templates?view=azure-devops |
| Configure Azure Repos Git repository-level settings | https://learn.microsoft.com/en-us/azure/devops/repos/git/repository-settings?view=azure-devops |
| Configure commit message keywords to close Azure Boards work items | https://learn.microsoft.com/en-us/azure/devops/repos/git/resolution-mentions?view=azure-devops |
| Configure custom CodeQL queries in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-code-scanning-queries?view=azure-devops |
| Configure dependency scanning for GitHub Advanced Security in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-dependency-scanning?view=azure-devops |
| Understand secret scanning patterns in GitHub Advanced Security | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-secret-scan-patterns?view=azure-devops |
| Configure secret scanning for GitHub Advanced Security in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-secret-scanning?view=azure-devops |
| Configure TFVC check-in policies in Visual Studio | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/add-check-policies?view=azure-devops |
| Configure external diff tools for TFVC file types | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/associate-file-type-file-comparison-tool?view=azure-devops |
| Configure TFVC check-in notes requirements | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/configure-check-notes?view=azure-devops |
| Configure TFVC check-out behavior in Visual Studio | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/configure-check-out-settings?view=azure-devops |
| Configure TFVC project settings with the configure command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/configure-command?view=azure-devops |
| Create and configure TFVC workspaces | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/create-work-workspaces?view=azure-devops |
| Edit TFVC check-in policy settings | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/edit-check-policies?view=azure-devops |
| Enable or disable TFVC check-in policies | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/enable-disable-check-policies?view=azure-devops |
| Configure TFVC folder comparison filters in Visual Studio | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/folder-comparison-filters?view=azure-devops |
| Configure TFVC proxy command for server access | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/proxy-command?view=azure-devops |
| Remove check-in policies from TFVC projects | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/remove-check-policies?view=azure-devops |
| Configure TFVC check-in policies and quality gates | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/set-enforce-quality-gates?view=azure-devops |
| Configure Test Impact for partially mapped TFVC repos | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/test-impact-for-partially-mapped-tfvc-repositories?view=azure-devops |
| Migrate custom TFVC check-in policy implementations | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/tfvc-check-in-policy-migrate-guide?view=azure-devops |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Azure DevOps ELM CLI commands and parameters | https://learn.microsoft.com/en-us/azure/devops/repos/enterprise-live-migrations/elm-cli-reference?view=azure-devops |
| Create Azure Functions-based custom branch policy for PRs | https://learn.microsoft.com/en-us/azure/devops/repos/git/create-pr-status-server-with-azure-functions?view=azure-devops |
| Build a Node.js pull request status server for Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/create-pr-status-server?view=azure-devops |
| Use Azure DevOps IntelliJ plugin with Git repositories | https://learn.microsoft.com/en-us/azure/devops/repos/git/create-repo-intellij?view=azure-devops |
| Extend Azure Repos pull request workflow with status and policy | https://learn.microsoft.com/en-us/azure/devops/repos/git/pull-request-status?view=azure-devops |
| Use Azure CLI and Git to share code in Azure Repos | https://learn.microsoft.com/en-us/azure/devops/repos/git/share-your-code-in-git-cmdline?view=azure-devops |
| Connect Azure Repos notifications to Slack channels | https://learn.microsoft.com/en-us/azure/devops/repos/integrations/repos-slack?view=azure-devops |
| Monitor Azure Repos activity in Microsoft Teams | https://learn.microsoft.com/en-us/azure/devops/repos/integrations/repos-teams?view=azure-devops |
| Integrate third-party scanners via SARIF in Azure DevOps | https://learn.microsoft.com/en-us/azure/devops/repos/security/github-advanced-security-code-scanning-third-party?view=azure-devops |
| Use the TFVC add command to track new files | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/add-command?view=azure-devops |
| Create TFVC branches using the branch command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/branch-command?view=azure-devops |
| View TFVC branch history with the branches command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/branches-command?view=azure-devops |
| Inspect and edit TFVC changesets using the changeset command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/changeset-command?view=azure-devops |
| Check in TFVC pending changes with the checkin command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/checkin-command?view=azure-devops |
| Check out and edit TFVC files using checkout/edit command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/checkout-or-edit-command?view=azure-devops |
| Delete TFVC items using the delete command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/delete-command-team-foundation-version-control?view=azure-devops |
| Permanently destroy TFVC items using the destroy command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/destroy-command-team-foundation-version-control?view=azure-devops |
| Compare TFVC files and folders with the difference command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/difference-command?view=azure-devops |
| List TFVC server items using the dir command | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/dir-command?view=azure-devops |
| Use TFVC folderdiff command to compare folders | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/folderdiff-command?view=azure-devops |
| Use TFVC get command to download versions | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/get-command?view=azure-devops |
| Manage Azure Repos Git permissions with tf git permission | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/git-permission-command?view=azure-devops |
| View Azure Repos Git files using tf git view | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/git-view-command?view=azure-devops |
| Use TFVC help command for CLI syntax | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/help-command-team-foundation-version-control?view=azure-devops |
| Use TFVC history command to view revisions | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/history-command?view=azure-devops |
| Use TFVC label command to manage labels | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/label-command-team-foundation-version-control?view=azure-devops |
| Use TFVC labels command to list labels | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/labels-command?view=azure-devops |
| Use TFVC localversions command in workspaces | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/localversions-command?view=azure-devops |
| Use TFVC lock command to control edits | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/lock-command?view=azure-devops |
| Use TFVC merge command to integrate branches | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/merge-command?view=azure-devops |
| Use TFVC merges command to inspect merge history | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/merges-command?view=azure-devops |
| Use TFVC msdn command to open docs | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/msdn-command?view=azure-devops |
| Use TFVC info command to inspect items | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/properties-or-info-command?view=azure-devops |
| Use TFVC reconcile command to sync workspace | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/reconcile-command?view=azure-devops |
| Use TFVC rename command to move items | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/rename-command-team-foundation-version-control?view=azure-devops |
| Use TFVC resolve command to handle conflicts | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/resolve-command?view=azure-devops |
| Use TFVC rollback command to revert changesets | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/rollback-command-team-foundation-version-control?view=azure-devops |
| Use TFVC shelve command to store changes | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/shelve-command?view=azure-devops |
| Use TFVC shelvesets command to list shelves | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/shelvesets-command?view=azure-devops |
| Use TFVC status command to view pending changes | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/status-command?view=azure-devops |
| Use TFVC undelete command to restore items | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/undelete-command?view=azure-devops |
| Use TFVC undo command to discard changes | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/undo-command?view=azure-devops |
| Use TFVC unlabel command to remove labels | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/unlabel-command?view=azure-devops |
| Use TFVC unshelve command to restore shelvesets | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/unshelve-command?view=azure-devops |
| Use TFVC command-line (tf.exe) for version control automation | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/use-team-foundation-version-control-commands?view=azure-devops |
| Use TFVC view command to retrieve file versions | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/view-command?view=azure-devops |
| Use TFVC workfold command to map folders | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/workfold-command?view=azure-devops |
| Use TFVC workspace command to manage workspaces | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/workspace-command?view=azure-devops |
| Use TFVC workspaces command to list workspaces | https://learn.microsoft.com/en-us/azure/devops/repos/tfvc/workspaces-command?view=azure-devops |