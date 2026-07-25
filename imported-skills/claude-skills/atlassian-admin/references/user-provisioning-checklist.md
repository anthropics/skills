# User Provisioning & Lifecycle Management Checklist

## Overview

This checklist covers the complete user lifecycle in Atlassian Cloud products, from onboarding through offboarding. Consistent provisioning ensures security, compliance, and a smooth user experience.

## Onboarding Steps

### Pre-Provisioning
- [ ] Receive approved access request (ticket or HR system trigger)
- [ ] Verify employee record in HR system
- [ ] Determine role-based access level (see Role Templates below)
- [ ] Identify required Atlassian products (Jira, Confluence, Bitbucket)
- [ ] Identify required project/space access

### Account Creation
- [ ] User account auto-provisioned via SCIM (preferred) or manually created
- [ ] Email domain matches verified organization domain
- [ ] SSO authentication verified (user can log in via IdP)
- [ ] 2FA enrollment confirmed
- [ ] Correct product access assigned (Jira, Confluence, Bitbucket)

### Group Membership
- [ ] Add to organization-level groups (e.g., `all-employees`)
- [ ] Add to department group (e.g., `engineering`, `product`, `marketing`)
- [ ] Add to team-specific groups (e.g., `team-platform`, `team-mobile`)
- [ ] Add to project groups as needed (e.g., `project-alpha-members`)
- [ ] Verify group membership grants correct permissions

### Product Configuration
- [ ] **Jira:** Add to correct project roles (Developer, User, Admin)
- [ ] **Jira:** Assign to correct board(s)
- [ ] **Jira:** Set default dashboard if applicable
- [ ] **Confluence:** Grant access to relevant spaces
- [ ] **Confluence:** Add to space groups with appropriate permission level
- [ ] **Bitbucket:** Grant repository access per team
- [ ] **Bitbucket:** Configure branch permissions

### Welcome & Training
- [ ] Send welcome email with access details and key links
- [ ] Share Confluence onboarding page (getting started guide)
- [ ] Assign onboarding buddy for Atlassian tool questions
- [ ] Schedule optional training session for new users
- [ ] Provide link to internal Atlassian usage guidelines

## Role-Based Access Templates

### Developer
- **Jira:** Project Developer role (create, edit, transition issues)
- **Confluence:** Team space editor, documentation spaces viewer
- **Bitbucket:** Repository write access for team repos

### Product Manager
- **Jira:** Project Admin role (manage boards, workflows, components)
- **Confluence:** Product spaces editor, all team spaces viewer
- **Bitbucket:** Repository read access (optional)

### Designer
- **Jira:** Project User role (view, comment, transition)
- **Confluence:** Design space editor, product spaces editor
- **Bitbucket:** No access (unless needed)

### Engineering Manager
- **Jira:** Project Admin for managed projects, viewer for others
- **Confluence:** Team space admin, all spaces viewer
- **Bitbucket:** Repository admin for team repos

### Executive / Stakeholder
- **Jira:** Viewer role on strategic projects, dashboard access
- **Confluence:** Viewer on relevant spaces
- **Bitbucket:** No access

### Contractor / External
- **Jira:** Project User role, limited to specific projects
- **Confluence:** Viewer on specific spaces only (no edit)
- **Bitbucket:** Repository read access, specific repos only
- **Additional:** Set account expiration date, restrict IP access

## Group Membership Standards

### Naming Convention
```
org-{company}          # Organization-wide groups
dept-{department}      # Department groups
team-{team-name}       # Team-specific groups
project-{project}      # Project-scoped groups
role-{role}            # Role-based groups (role-admin, role-viewer)
```

### Standard Groups
| Group | Purpose | Products |
|-------|---------|----------|
| `org-all-employees` | All full-time employees | Jira, Confluence |
| `dept-engineering` | All engineers | Jira, Confluence, Bitbucket |
| `dept-product` | All product team | Jira, Confluence |
| `dept-marketing` | All marketing team | Confluence |
| `role-jira-admins` | Jira administrators | Jira |
| `role-confluence-admins` | Confluence administrators | Confluence |
| `role-org-admins` | Organization administrators | All |

## Offboarding Procedure

### Immediate Actions (Day of Departure)
- [ ] Deactivate user account in Atlassian (or via IdP/SCIM)
- [ ] Revoke all API tokens associated with the user
- [ ] Revoke all OAuth app authorizations
- [ ] Transfer ownership of critical Confluence pages
- [ ] Reassign Jira issues (open/in-progress items)
- [ ] Remove from all groups
- [ ] Document access removal in offboarding ticket

### Within 24 Hours
- [ ] Verify account is fully deactivated (cannot log in)
- [ ] Check for shared credentials or service accounts
- [ ] Review audit log for recent activity
- [ ] Transfer Confluence space ownership if applicable
- [ ] Update Jira project leads/component leads if applicable
- [ ] Remove from any Atlassian Marketplace vendor accounts

### Within 7 Days
- [ ] Verify no lingering sessions or cached access
- [ ] Review integrations the user may have set up
- [ ] Check for automation rules owned by the user
- [ ] Update team dashboards and filters
- [ ] Confirm with manager that all transfers are complete

### Data Retention
- [ ] User content (pages, issues, comments) retained per policy
- [ ] Personal spaces archived or transferred
- [ ] Account marked as deactivated (not deleted) for audit trail
- [ ] Data deletion request processed if required (GDPR)

## Quarterly Access Reviews

### Review Process
1. Generate user access report from Atlassian Admin
2. Distribute to managers for team verification
3. Managers confirm or flag each user's access level
4. IT Admin processes approved changes
5. Document review completion for compliance

### Review Checklist
- [ ] All active accounts match current employee list
- [ ] No accounts for departed employees
- [ ] Group memberships align with current roles
- [ ] Admin access limited to approved administrators
- [ ] External/contractor accounts have valid expiration dates
- [ ] Service accounts documented with current owners
- [ ] Unused accounts (no login in 90 days) flagged for review

### Compliance Documentation
- [ ] Access review completion date recorded
- [ ] Manager sign-off captured (email or ticket)
- [ ] Changes made during review documented
- [ ] Exceptions documented with justification and approval
- [ ] Report filed for audit purposes
- [ ] Next review date scheduled

## Automation Opportunities

### SCIM Provisioning
- Automatically create/deactivate accounts based on IdP changes
- Sync group membership from IdP groups
- Reduce manual provisioning errors
- Ensure immediate deactivation on termination

### Workflow Automation
- Trigger onboarding checklist from HR system event
- Auto-assign to groups based on department/role attributes
- Send welcome messages via Confluence automation
- Schedule access reviews via Jira recurring tickets

### Monitoring
- Alert on accounts without 2FA after 7 days
- Alert on admin group changes
- Weekly report of new and deactivated accounts
- Monthly stale account report (no login in 90 days)
