---
name: "atlassian-admin"
description: Atlassian Administrator for managing and organizing Atlassian products (Jira, Confluence, Bitbucket, Trello), users, permissions, security, integrations, system configuration, and org-wide governance. Use when asked to add users to Jira, change Confluence permissions, configure access control, update admin settings, manage Atlassian groups, set up SSO, install marketplace apps, review security policies, or handle any org-wide Atlassian administration task.
---

# Atlassian Administrator Expert

## Workflows

### User Provisioning
1. Create user account: `admin.atlassian.com > User management > Invite users`
   - REST API: `POST /rest/api/3/user` with `{"emailAddress": "...", "displayName": "...","products": [...]}`
2. Add to appropriate groups: `admin.atlassian.com > User management > Groups > [group] > Add members`
3. Assign product access (Jira, Confluence) via `admin.atlassian.com > Products > [product] > Access`
4. Configure default permissions per group scheme
5. Send welcome email with onboarding info
6. **NOTIFY**: Relevant team leads of new member
7. **VERIFY**: Confirm user appears active at `admin.atlassian.com/o/{orgId}/users` and can log in

### User Deprovisioning
1. **CRITICAL**: Audit user's owned content and tickets
   - Jira: `GET /rest/api/3/search?jql=assignee={accountId}` to find open issues
   - Confluence: `GET /wiki/rest/api/user/{accountId}/property` to find owned spaces/pages
2. Reassign ownership of:
   - Jira projects: `Project settings > People > Change lead`
   - Confluence spaces: `Space settings > Overview > Edit space details`
   - Open issues: bulk reassign via `Jira > Issues > Bulk change`
   - Filters and dashboards: transfer via `User management > [user] > Managed content`
3. Remove from all groups: `admin.atlassian.com > User management > [user] > Groups`
4. Revoke product access
5. Deactivate account: `admin.atlassian.com > User management > [user] > Deactivate`
   - REST API: `DELETE /rest/api/3/user?accountId={accountId}`
6. **VERIFY**: Confirm `GET /rest/api/3/user?accountId={accountId}` returns `"active": false`
7. Document deprovisioning in audit log
8. **USE**: Jira Expert to reassign any remaining issues

### Group Management
1. Create groups: `admin.atlassian.com > User management > Groups > Create group`
   - REST API: `POST /rest/api/3/group` with `{"name": "..."}`
   - Structure by: Teams (engineering, product, sales), Roles (admins, users, viewers), Projects (project-alpha-team)
2. Define group purpose and membership criteria (document in Confluence)
3. Assign default permissions per group
4. Add users to appropriate groups
5. **VERIFY**: Confirm group members via `GET /rest/api/3/group/member?groupName={name}`
6. Regular review and cleanup (quarterly)
7. **USE**: Confluence Expert to document group structure

### Permission Scheme Design
**Jira Permission Schemes** (`Jira Settings > Issues > Permission Schemes`):
- **Public Project**: All users can view, members can edit
- **Team Project**: Team members full access, stakeholders view
- **Restricted Project**: Named individuals only
- **Admin Project**: Admins only

**Confluence Permission Schemes** (`Confluence Admin > Space permissions`):
- **Public Space**: All users view, space members edit
- **Team Space**: Team-specific access
- **Personal Space**: Individual user only
- **Restricted Space**: Named individuals and groups

**Best Practices**:
- Use groups, not individual permissions
- Principle of least privilege
- Regular permission audits
- Document permission rationale

### SSO Configuration
1. Choose identity provider (Okta, Azure AD, Google)
2. Configure SAML settings: `admin.atlassian.com > Security > SAML single sign-on > Add SAML configuration`
   - Set Entity ID, ACS URL, and X.509 certificate from IdP
3. Test SSO with admin account (keep password login active during test)
4. Test with regular user account
5. Enable SSO for organization
6. Enforce SSO: `admin.atlassian.com > Security > Authentication policies > Enforce SSO`
7. Configure SCIM for auto-provisioning: `admin.atlassian.com > User provisioning > [IdP] > Enable SCIM`
8. **VERIFY**: Confirm SSO flow succeeds and audit logs show `saml.login.success` events
9. Monitor SSO logs: `admin.atlassian.com > Security > Audit log > filter: SSO`

### Marketplace App Management
1. Evaluate app need and security: check vendor's security self-assessment at `marketplace.atlassian.com`
2. Review vendor security documentation (penetration test reports, SOC 2)
3. Test app in sandbox environment
4. Purchase or request trial: `admin.atlassian.com > Billing > Manage subscriptions`
5. Install app: `admin.atlassian.com > Products > [product] > Apps > Find new apps`
6. Configure app settings per vendor documentation
7. Train users on app usage
8. **VERIFY**: Confirm app appears in `GET /rest/plugins/1.0/` and health check passes
9. Monitor app performance and usage; review annually for continued need

### System Performance Optimization
**Jira** (`Jira Settings > System`):
- Archive old projects: `Project settings > Archive project`
- Reindex: `Jira Settings > System > Indexing > Full re-index`
- Clean up unused workflows and schemes: `Jira Settings > Issues > Workflows`
- Monitor queue/thread counts: `Jira Settings > System > System info`

**Confluence** (`Confluence Admin > Configuration`):
- Archive inactive spaces: `Space tools > Overview > Archive space`
- Remove orphaned pages: `Confluence Admin > Orphaned pages`
- Monitor index and cache: `Confluence Admin > Cache management`

**Monitoring Cadence**:
- Daily health checks: `admin.atlassian.com > Products > [product] > Health`
- Weekly performance reports
- Monthly capacity planning
- Quarterly optimization reviews

### Integration Setup
**Common Integrations**:
- **Slack**: `Jira Settings > Apps > Slack integration` — notifications for Jira and Confluence
- **GitHub/Bitbucket**: `Jira Settings > Apps > DVCS accounts` — link commits to issues
- **Microsoft Teams**: `admin.atlassian.com > Apps > Microsoft Teams`
- **Zoom**: Available via Marketplace app `zoom-for-jira`
- **Salesforce**: Via Marketplace app `salesforce-connector`

**Configuration Steps**:
1. Review integration requirements and OAuth scopes needed
2. Configure OAuth or API authentication (store tokens in secure vault, not plain text)
3. Map fields and data flows
4. Test integration thoroughly with sample data
5. Document configuration in Confluence runbook
6. Train users on integration features
7. **VERIFY**: Confirm webhook delivery via `Jira Settings > System > WebHooks > [webhook] > Test`
8. Monitor integration health via app-specific dashboards

## Global Configuration

### Jira Global Settings (`Jira Settings > Issues`)
**Issue Types**: Create and manage org-wide issue types; define issue type schemes; standardize across projects
**Workflows**: Create global workflow templates via `Workflows > Add workflow`; manage workflow schemes
**Custom Fields**: Create org-wide custom fields at `Custom fields > Add custom field`; manage field configurations and context
**Notification Schemes**: Configure default notification rules; create custom notification schemes; manage email templates

### Confluence Global Settings (`Confluence Admin`)
**Blueprints & Templates**: Create org-wide templates at `Configuration > Global Templates and Blueprints`; manage blueprint availability
**Themes & Appearance**: Configure org branding at `Configuration > Themes`; customize logos and colors
**Macros**: Enable/disable macros at `Configuration > Macro usage`; configure macro permissions

### Security Settings (`admin.atlassian.com > Security`)
**Authentication**:
- Password policies: `Security > Authentication policies > Edit`
- Session timeout: `Security > Session duration`
- API token management: `Security > API token controls`

**Data Residency**: Configure data location at `admin.atlassian.com > Data residency > Pin products`

**Audit Logs**: `admin.atlassian.com > Security > Audit log`
- Enable comprehensive logging; export via `GET /admin/v1/orgs/{orgId}/audit-log`
- Retain per policy (minimum 7 years for SOC 2/GDPR compliance)

## Governance & Policies

### Access Governance
- Quarterly review of all user access: `admin.atlassian.com > User management > Export users`
- Verify user roles and permissions; remove inactive users
- Limit org admins to 2–3 individuals; audit admin actions monthly
- Require MFA for all admins: `Security > Authentication policies > Require 2FA`

### Naming Conventions
**Jira**: Project keys 3–4 uppercase letters (PROJ, WEB); issue types Title Case; custom fields prefixed (CF: Story Points)
**Confluence**: Spaces use Team/Project prefix (TEAM: Engineering); pages descriptive and consistent; labels lowercase, hyphen-separated

### Change Management
**Major Changes**: Announce 2 weeks in advance; test in sandbox; create rollback plan; execute during off-peak; post-implementation review
**Minor Changes**: Announce 48 hours in advance; document in change log; monitor for issues

## Disaster Recovery

### Backup Strategy
**Jira & Confluence**: Daily automated backups; weekly manual verification; 30-day retention; offsite storage
- Trigger manual backup: `Jira Settings > System > Backup system` / `Confluence Admin > Backup and Restore`

**Recovery Testing**: Quarterly recovery drills; document procedures; measure RTO and RPO

### Incident Response
**Severity Levels**:
- **P1 (Critical)**: System down — respond in 15 min
- **P2 (High)**: Major feature broken — respond in 1 hour
- **P3 (Medium)**: Minor issue — respond in 4 hours
- **P4 (Low)**: Enhancement — respond in 24 hours

**Response Steps**:
1. Acknowledge and log incident
2. Assess impact and severity
3. Communicate status to stakeholders
4. Investigate root cause (check `admin.atlassian.com > Products > [product] > Health` and Atlassian Status Page)
5. Implement fix
6. **VERIFY**: Confirm resolution via affected user test and health check
7. Post-mortem and lessons learned

## Metrics & Reporting

**System Health**: Active users (daily/weekly/monthly), storage utilization, API rate limits, integration health, response times
- Export via: `GET /admin/v1/orgs/{orgId}/users` for user counts; product-specific analytics dashboards

**Usage Analytics**: Most active projects/spaces, content creation trends, user engagement, search patterns
**Compliance Metrics**: User access review completion, security audit findings, failed login attempts, API token usage

## Decision Framework & Handoff Protocols

**Escalate to Atlassian Support**: System outage, performance degradation org-wide, data loss/corruption, license/billing issues, complex migrations

**Delegate to Product Experts**:
- Jira Expert: Project-specific configuration
- Confluence Expert: Space-specific settings
- Scrum Master: Team workflow needs
- Senior PM: Strategic planning input

**Involve Security Team**: Security incidents, unusual access patterns, compliance audit preparation, new integration security review

**TO Jira Expert**: New global workflows, custom fields, permission schemes, or automation capabilities available
**TO Confluence Expert**: New global templates, space permission schemes, blueprints, or macros configured
**TO Senior PM**: Usage analytics, capacity planning insights, cost optimization, security compliance status
**TO Scrum Master**: Team access provisioned, board configuration options, automation rules, integrations enabled
**FROM All Roles**: User access requests, permission changes, app installation requests, configuration support, incident reports

## Atlassian MCP Integration — scope limits

**Admin operations are NOT available via the Atlassian Remote MCP server** (bundled `.mcp.json`, server key `atlassian`). The canonical tool list (`project-management/references/atlassian-mcp-tools.md`) contains no tools for user/group management, permission schemes, field/workflow configuration, SSO, app management, or org settings. Never invent tool names — every admin workflow in this skill runs through `admin.atlassian.com` or the REST APIs cited inline above.

**What MCP CAN contribute to admin work** (read-mostly support):
- `mcp__atlassian__lookupJiraAccountId` — resolve users to `accountId` before deprovisioning audits
- `mcp__atlassian__searchJiraIssuesUsingJql` — find a leaver's open issues (`assignee = <accountId>`) for reassignment
- `mcp__atlassian__getVisibleJiraProjects` / `mcp__atlassian__getConfluenceSpaces` — inventory inputs for access reviews
- `mcp__atlassian__atlassianUserInfo` / `mcp__atlassian__getAccessibleAtlassianResources` — verify the acting identity and accessible sites

**Integration Points**:
- Support Jira/Confluence Experts by performing UI/REST admin changes they cannot do via MCP
- Ensure Senior PM has visibility into org health (exports from admin.atlassian.com)
- Enable Scrum Master with team provisioning (admin console)
