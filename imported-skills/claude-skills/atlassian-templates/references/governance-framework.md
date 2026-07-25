# Template Governance Framework

## Overview

Operational framework for managing template lifecycle — creation, updates, deprecation, and quality enforcement with concrete thresholds and decision criteria.

## Ownership Model

### Roles

**Template Owner** (1 per template):
- Reviews usage dashboard on the 1st of each quarter
- Archives templates with <5 uses in the past 90 days
- Responds to change requests within 14 calendar days
- Runs quarterly accuracy check: open 3 random pages created from the template, verify content matches current process
- Escalates to committee if change affects >50 users

**Template Steward** (1 per team/domain):
- Runs monthly usage pull: `CQL: type = page AND label = "template-{name}" AND created >= "now-30d"`
- Flags templates where >30% of users delete or heavily modify a section (indicates friction)
- Collects and triages feedback — tags Jira tickets with `template-change` and links to template page

**Template Committee** (3-5 people, for orgs with 20+ templates):
- Meets quarterly (45 min max): reviews new proposals, resolves conflicts, flags duplicates
- Decision rule: approve if template serves >1 team and doesn't duplicate existing template by >60% content overlap
- Publishes quarterly "Template Health" Confluence page with adoption rates and actions taken

### Assignment Matrix

| Template Category | Owner Role | Steward Role |
|------------------|-----------|-------------|
| Engineering templates | Engineering Manager | Senior Engineer |
| Product templates | Head of Product | Senior PM |
| Meeting templates | Operations Lead | EA/Admin |
| Project templates | PMO Lead | Senior PM |
| HR/People templates | HR Director | HR Coordinator |
| Company-wide templates | Operations Lead | Template Committee |

## Approval Workflow

### New Template Proposal

1. **Request** - Submitter creates proposal with:
   - Template name and purpose
   - Target audience
   - Justification (why existing templates are insufficient)
   - Draft content
   - Proposed owner

2. **Review** - Template owner/committee evaluates:
   - Does this duplicate an existing template?
   - Is the scope appropriate (not too broad or narrow)?
   - Does it follow design standards?
   - Is it needed by more than one team?

3. **Pilot** - If approved:
   - Deploy to a small group for 2-4 weeks
   - Collect feedback on usability and completeness
   - Iterate based on feedback

4. **Launch** - After successful pilot:
   - Publish to template library
   - Announce to relevant teams
   - Add to Template Index page
   - Train users if needed

5. **Monitor** - Post-launch:
   - Track adoption rate (first 30 days)
   - Collect initial feedback
   - Make quick adjustments if needed

### Template Update Process

1. **Change Request** - Anyone can suggest changes via:
   - Comment on the template page
   - Jira ticket tagged `template-change`
   - Direct message to template owner

2. **Assessment** - Owner evaluates:
   - Impact on existing documents using this template
   - Alignment with organizational standards
   - Effort required for update

3. **Implementation** - Owner or steward:
   - Makes changes in a draft version
   - Reviews with 1-2 frequent users
   - Updates version number and changelog
   - Publishes updated template

4. **Communication** - Notify users:
   - Post update in relevant Slack/Teams channel
   - Update Template Index page
   - Send email for major changes

## Change Management

### Impact Categories

**Low Impact (Owner decides):**
- Typo fixes and formatting improvements
- Clarifying existing instructions
- Adding optional sections

**Medium Impact (Owner + 1 reviewer):**
- Adding new required sections
- Changing variable names or structure
- Updating macro usage

**High Impact (Committee review):**
- Removing sections from widely-used templates
- Merging or splitting templates
- Changing organizational template standards

### Communication Plan

| Change Type | Communication | Timeline |
|------------|---------------|----------|
| Low impact | Changelog update | Same day |
| Medium impact | Team channel announcement | 1 week notice |
| High impact | Email + meeting + migration guide | 2-4 weeks notice |

## Deprecation Process

### When to Deprecate
- Template replaced by a better alternative
- Process the template supports has been retired
- Template has zero usage in the past 6 months
- Template is redundant with another active template

### Deprecation Steps

1. **Decision** - Owner proposes deprecation with justification
2. **Announcement** - Notify users 30 days before deprecation:
   - Mark template with "DEPRECATED" status
   - Add deprecation notice at top of template
   - Point to replacement template (if applicable)
3. **Transition Period** - 30 days:
   - Template still available but marked deprecated
   - New documents should use replacement
   - Existing documents do not need to change
4. **Archive** - After transition:
   - Move template to Archive section
   - Remove from active template list
   - Keep accessible for historical reference
5. **Review** - 90 days after archive:
   - Confirm no active usage
   - Add to annual cleanup list if truly unused

## Usage Tracking

### Metrics & Thresholds

| Metric | Healthy | Flagged | Deprecate |
|--------|---------|---------|-----------|
| Pages created/month | >10 | 3-10 | <3 for 2 consecutive quarters |
| Unique users/month | >5 | 2-5 | 0-1 for 90 days |
| Section deletion rate | <10% | 10-30% | >30% (users removing sections = template mismatch) |
| Time to first use (new templates) | <7 days | 7-30 days | >30 days (failed launch, re-announce or rethink) |

### Tracking via CQL

```
-- Monthly usage for a specific template
type = page AND label = "template-sprint-retro" AND created >= "now-30d"

-- Stale templates (no usage in 90 days)
type = page AND label IN ("template-sprint-retro", "template-decision-log") AND created < "now-90d" AND created >= "now-91d"

-- All template-created pages for audit
type = page AND label = "template-*" ORDER BY created DESC
```

### Reporting
- **Monthly:** Top 10 templates by usage → auto-generated Confluence table
- **Quarterly:** Flag templates below thresholds → owner action required within 14 days
- **Annually:** Full catalog review — archive anything with 0 uses in 6 months

## Quality Standards

### Content Checklist (pass/fail per template)
- [ ] Every section has placeholder text showing expected content (not just a heading)
- [ ] No section references a process, tool, or team that no longer exists
- [ ] All Jira macro JQL filters return results (test quarterly)
- [ ] Links to other Confluence pages resolve (no 404s)
- [ ] Template renders correctly in both desktop and mobile preview

**FAIL examples:** Template says "Update the JIRA board" but team uses Linear. Template has a "QA Sign-Off" section but team has no QA role. Placeholder text says "TODO: add content here" with no guidance on what content.

### Structural Checklist
- [ ] Metadata header: owner name, version (semver), status (`active`/`deprecated`/`draft`), last-reviewed date
- [ ] Table of Contents macro if template has 4+ sections
- [ ] Change History table at bottom (date, author, change description)
- [ ] Placeholder text uses `{placeholder}` syntax or ac:placeholder macro — visually distinct from real content

### Maintenance Triggers
- Template not reviewed in 90+ days → owner gets Jira ticket auto-created via automation
- 3+ unresolved feedback items → escalate to committee
- Broken macro detected → owner notified same day via Slack/email automation

## Review Cadence

### Quarterly Review (Template Owner)
- Review usage metrics
- Address pending feedback
- Update content for accuracy
- Verify all links and macros work
- Update version number if changed

### Semi-Annual Review (Template Committee)
- Review full template catalog
- Identify gaps (missing templates)
- Identify overlaps (duplicate templates)
- Evaluate template standards compliance
- Plan improvements for next half

### Annual Review (Leadership — 60 min meeting)

**Agenda:**
1. (10 min) Catalog stats: total templates, usage trend YoY, templates added/deprecated
2. (15 min) Top 5 templates by adoption — what makes them work
3. (15 min) Bottom 5 templates — deprecate, rework, or retrain?
4. (10 min) Gaps identified by teams — templates requested but not yet built
5. (10 min) Governance process retro — is the framework itself working? Adjust thresholds, roles, or cadence as needed

**Deliverable:** Updated Template Health page published within 1 week of meeting

## Getting Started

### For New Organizations
1. Start with 5-10 essential templates (meeting notes, decision record, project plan)
2. Assign owners for each template
3. Establish basic quality standards
4. Review after 90 days and expand
5. Formalize governance as template count grows beyond 20
