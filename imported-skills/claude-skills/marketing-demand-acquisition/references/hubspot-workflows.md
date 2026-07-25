# HubSpot Workflow Templates

Pre-built workflow configurations for lead scoring, nurturing, and assignment.

---

## Table of Contents

- [Campaign Tracking Setup](#campaign-tracking-setup)
- [Lead Scoring Configuration](#lead-scoring-configuration)
- [MQL to SQL Workflow](#mql-to-sql-workflow)
- [Partner Lead Tracking](#partner-lead-tracking)
- [Nurture Sequences](#nurture-sequences)

---

## Campaign Tracking Setup

### Create Campaign in HubSpot

1. Navigate to Marketing → Campaigns → Create Campaign
2. Name using convention: `Q[N]-[YEAR]-[CHANNEL]-[CAMPAIGN-TYPE]`
   - Example: `Q2-2025-LinkedIn-ABM-Enterprise`
3. Tag all assets (landing pages, emails, ads) with campaign ID

### UTM Parameter Structure

```
utm_source={channel}       // linkedin, google, facebook
utm_medium={type}          // cpc, display, email, organic
utm_campaign={campaign-id} // q2-2025-linkedin-abm-enterprise
utm_content={variant}      // ad-variant-a, email-1
utm_term={keyword}         // [for paid search only]
```

**Validation:** Verify UTM parameters appear in HubSpot contact records after test submission.

---

## Lead Scoring Configuration

### Navigate to Configuration

Settings → Marketing → Lead Scoring

### Scoring Rules

| Action | Points | Rationale |
|--------|--------|-----------|
| Content download | +10 to +20 | Based on content depth |
| Demo request | +30 | High intent signal |
| Pricing page visit | +15 | Commercial intent |
| Webinar attendance | +20 | Engaged prospect |
| Email open | +2 | Basic engagement |
| Email click | +5 | Active interest |

### Channel Quality Modifiers

| Source | Points | Rationale |
|--------|--------|-----------|
| LinkedIn | +5 | Professional context |
| Google Search | +10 | Active search intent |
| Organic | +15 | Self-discovery |
| Referral | +20 | Pre-qualified |

**Validation:** Test lead scoring by creating a test contact and triggering each action.

---

## MQL to SQL Workflow

### SQL Definition Criteria

```
Required (all must be true):
✅ Job title: Director+ (or Budget Authority confirmed)
✅ Company size: 50-5000 employees
✅ Budget: $10k+ annual
✅ Timeline: Buying within 90 days
✅ Engagement: Demo requested OR High intent action
```

### Workflow Configuration

1. **Trigger:** Lead score reaches MQL threshold (>75 points)
2. **Action 1:** Send automated email to SDR with lead details
3. **Action 2:** Create task for SDR qualification call
4. **Branch Logic:**
   - If qualified → Update lifecycle stage to SQL, assign to AE
   - If not qualified → Move to nurture list, reduce lead score by 30

### SLA Configuration

| Handoff | Target | Escalation |
|---------|--------|------------|
| SDR responds to MQL | 4 hours | Manager notification |
| AE books demo with SQL | 24 hours | Director notification |
| First demo scheduled | 3 business days | VP notification |

**Validation:** Test workflow with a sample lead. Verify notifications trigger correctly.

---

## Partner Lead Tracking

### Create Partner Property

1. Settings → Properties → Create Property
2. Property name: `Partner Source`
3. Type: Dropdown select
4. Values: Partner A, Partner B, Affiliate Network, Direct

### Partner UTM Configuration

```
Partner links: ?utm_source=partner-name&utm_medium=referral
```

### Lead Assignment Workflow

1. **Trigger:** Contact property `Partner Source` is set
2. **Action:** Assign to Partner Manager
3. **Notification:** Slack alert when partner lead arrives

### Partner Reporting Dashboard

Create custom report: Marketing → Reports → Create Report
- Metrics: Leads, Pipeline, Revenue by Partner Source
- Dimensions: Partner Name, Time Period

**Validation:** Submit test lead with partner UTM. Verify property populates and routing works.

---

## Nurture Sequences

### Lost Opportunity Recycle

**Trigger:** Deal stage = Closed Lost

**Sequence:**
1. Day 0: Add to nurture list, remove from active campaigns
2. Day 30: Educational content email
3. Day 60: Industry insights email
4. Day 90: Re-engagement offer email
5. Month 6: SDR re-qualification task

### TOFU to MOFU Progression

**Trigger:** Contact downloads 2+ content pieces

**Sequence:**
1. Day 0: Thank you email with related content
2. Day 3: Case study email
3. Day 7: Webinar invitation
4. Day 14: Demo offer (soft CTA)

### Closed Lost Reason Tracking

Configure deal properties to capture:
- Price too high
- Missing features
- Chose competitor
- No budget
- Bad timing
- Champion left company

**Use data to inform:** Product roadmap, pricing adjustments, competitive positioning.
