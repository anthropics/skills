# Stakeholder Communication Templates

## Introduction

Effective communication about technical debt is crucial for securing resources, setting expectations, and maintaining stakeholder trust. This document provides templates and guidelines for communicating technical debt status, impact, and recommendations to different stakeholder groups.

## Executive Summary Templates

### Monthly Executive Report

**Subject**: Technical Health Report - [Month] [Year]

---

**EXECUTIVE SUMMARY**

**Overall Status**: [EXCELLENT/GOOD/FAIR/POOR] - Health Score: [X]/100

**Key Message**: [One sentence summary of current state and trend]

**Immediate Actions Required**: [Yes/No] - [Brief explanation if yes]

---

**BUSINESS IMPACT**

• **Development Velocity**: [X]% impact on feature delivery speed
• **Quality Risk**: [LOW/MEDIUM/HIGH] - [Brief explanation]
• **Security Posture**: [X] critical issues, [X] high-priority issues
• **Customer Impact**: [Direct customer-facing implications]

**FINANCIAL IMPLICATIONS**

• **Current Cost**: $[X]K monthly in reduced velocity
• **Investment Needed**: $[X]K for critical issues (next quarter)
• **ROI Projection**: [X]% velocity improvement, $[X]K annual savings
• **Risk Cost**: Up to $[X]K if critical issues materialize

**STRATEGIC RECOMMENDATIONS**

1. **[Priority 1]**: [Action] - [Business justification] - [Timeline]
2. **[Priority 2]**: [Action] - [Business justification] - [Timeline]  
3. **[Priority 3]**: [Action] - [Business justification] - [Timeline]

**TREND ANALYSIS**

• Health Score: [Previous] → [Current] ([Improving/Declining/Stable])
• Debt Items: [Previous] → [Current] ([Net change])
• High-Priority Issues: [Previous] → [Current]

---

**NEXT STEPS**

• **This Quarter**: [Key initiatives and expected outcomes]
• **Resource Request**: [Additional resources needed, if any]
• **Dependencies**: [External dependencies or blockers]

---

### Quarterly Board-Level Report

**Subject**: Technical Debt & Engineering Health - Q[X] [Year]

---

**KEY METRICS**

| Metric | Current | Target | Trend |
|--------|---------|--------|--------|
| Health Score | [X]/100 | [X]/100 | [↑/↓/→] |
| Velocity Impact | [X]% | <[X]% | [↑/↓/→] |
| Critical Issues | [X] | 0 | [↑/↓/→] |
| Security Risk | [LOW/MED/HIGH] | LOW | [↑/↓/→] |

**STRATEGIC CONTEXT**

Technical debt represents deferred investment in our technology platform. Our current debt portfolio has [positive/negative/neutral] implications for:

• **Growth Capacity**: [Impact on ability to scale]
• **Competitive Position**: [Impact on market responsiveness]  
• **Risk Profile**: [Impact on operational risk]
• **Team Retention**: [Impact on engineering talent]

**INVESTMENT ANALYSIS**

• **Current Annual Cost**: $[X]M in reduced productivity
• **Proposed Investment**: $[X]M over [timeframe]
• **Expected ROI**: [X]% productivity improvement, $[X]M NPV
• **Risk Mitigation**: $[X]M in avoided incident costs

**RECOMMENDATIONS**

1. **[Immediate]**: [Strategic action with business rationale]
2. **[This Year]**: [Medium-term initiative with expected outcomes]
3. **[Ongoing]**: [Process or cultural change needed]

---

## Product Management Templates

### Sprint Planning Discussion

**Subject**: Tech Debt Impact on Sprint [X] Planning

---

**SPRINT CAPACITY IMPACT**

**Affected User Stories**:
• [Story 1]: [X] point increase due to [debt issue]
• [Story 2]: [X]% risk of scope reduction due to [debt issue]
• [Story 3]: Blocked by [debt issue] - requires [X] points of debt work first

**Recommended Debt Work This Sprint**:
• **[Debt Item 1]** ([X] points): Unblocks [Story Y], reduces future story complexity
• **[Debt Item 2]** ([X] points): Prevents [specific risk] in upcoming features

**Trade-off Analysis**:
• **If we fix debt**: [X] points for features, [benefits for future sprints]
• **If we don't fix debt**: [X] points for features, [accumulated costs and risks]

**Recommendation**: [Specific allocation suggestion with rationale]

---

### Feature Impact Assessment

**Subject**: Technical Debt Impact Assessment - [Feature Name]

---

**DEBT AFFECTING THIS FEATURE**

| Debt Item | Impact | Effort to Fix | Recommendation |
|-----------|--------|---------------|----------------|
| [Item 1] | [Description] | [X] points | Fix before/Work around/Accept |
| [Item 2] | [Description] | [X] points | Fix before/Work around/Accept |

**DELIVERY IMPACT**

• **Timeline Risk**: [LOW/MEDIUM/HIGH]
  - Base estimate: [X] points
  - Debt-adjusted estimate: [X] points ([X]% increase)
  - Risk factors: [Specific risks and probabilities]

• **Quality Risk**: [LOW/MEDIUM/HIGH]
  - [Specific quality concerns from debt]
  - Mitigation strategies: [Options for reducing risk]

• **Future Feature Impact**:  
  - This feature will [add to/reduce/not affect] debt burden
  - Related future features will be [easier/harder/unaffected]

**RECOMMENDATIONS**

1. **[Option 1]**: [Approach with pros/cons]
2. **[Option 2]**: [Alternative approach with trade-offs]
3. **Recommended**: [Chosen approach with justification]

---

## Engineering Team Templates

### Team Health Check

**Subject**: Weekly Team Health Check - [Date]

---

**DEBT BURDEN THIS WEEK**

• **New Debt Identified**: [X] items ([categories])
• **Debt Resolved**: [X] items ([X] hours saved)  
• **Net Change**: [Positive/Negative] [X] items
• **Top Pain Points**: [Developer-reported friction areas]

**VELOCITY IMPACT**

• **Stories Affected by Debt**: [X] of [Y] planned stories
• **Estimated Overhead**: [X] hours of extra work due to debt
• **Blocked Work**: [Any stories waiting on debt resolution]

**TEAM SENTIMENT**

• **Frustration Level**: [1-5 scale] ([trend])
• **Confidence in Codebase**: [1-5 scale] ([trend])  
• **Top Complaints**: [Most common developer concerns]

**ACTIONS THIS WEEK**

• **Debt Work Planned**: [Specific items and assignees]
• **Prevention Measures**: [Process improvements or reviews]
• **Escalations**: [Issues needing management attention]

---

### Architecture Decision Record (ADR) Template

**Subject**: ADR-[XXX]: [Decision Title] - Technical Debt Consideration

---

**Status**: [Proposed/Accepted/Deprecated]
**Date**: [YYYY-MM-DD]
**Decision Makers**: [Names]

**CONTEXT**

[Background and current situation]

**TECHNICAL DEBT ANALYSIS**

• **Debt Created by This Decision**:
  - [Specific debt that will be introduced]
  - [Estimated effort to resolve later: X points]
  - [Interest rate: impact over time]

• **Debt Resolved by This Decision**:
  - [Existing debt this addresses]
  - [Estimated effort saved: X points]
  - [Risk reduction achieved]

• **Net Debt Impact**: [Positive/Negative/Neutral]

**DECISION**

[What we decided to do]

**RATIONALE**

[Why we made this decision, including debt trade-offs]

**DEBT MANAGEMENT PLAN**

• **Monitoring**: [How we'll track the debt introduced]
• **Timeline**: [When we plan to address the debt]
• **Success Criteria**: [How we'll know it's time to pay down the debt]

**CONSEQUENCES**

[Expected outcomes, including debt implications]

---

## Customer-Facing Templates

### Release Notes - Quality Improvements

**Subject**: Platform Stability and Performance Improvements - Release [X.Y]

---

**QUALITY IMPROVEMENTS**

We've invested significant effort in improving the reliability and performance of our platform. While these changes aren't feature additions, they provide important benefits:

**RELIABILITY ENHANCEMENTS**

• **Reduced Error Rates**: [X]% fewer errors in [specific area]
• **Improved Uptime**: [X]% improvement in system availability
• **Faster Recovery**: [X]% faster recovery from service interruptions

**PERFORMANCE IMPROVEMENTS**

• **Page Load Speed**: [X]% faster loading for [specific features]
• **API Response Time**: [X]% improvement in response times
• **Resource Usage**: [X]% reduction in memory/CPU usage

**SECURITY STRENGTHENING**

• **Vulnerability Resolution**: Addressed [X] security findings
• **Authentication Improvements**: Enhanced login security and reliability
• **Data Protection**: Improved data encryption and access controls

**WHAT THIS MEANS FOR YOU**

• **Better User Experience**: Fewer interruptions, faster responses
• **Increased Reliability**: Less downtime, more predictable performance
• **Enhanced Security**: Your data is better protected

We continue to balance new feature development with platform investments to ensure a reliable, secure, and performant experience.

---

### Service Incident Communication

**Subject**: Service Update - [Brief Description] - [Status]

---

**INCIDENT SUMMARY**

• **Impact**: [Description of customer impact]
• **Duration**: [Start time] - [End time / Ongoing]
• **Root Cause**: [High-level, customer-appropriate explanation]
• **Resolution**: [What was done to fix it]

**TECHNICAL DEBT CONNECTION**

This incident was [directly caused by / contributed to by / unrelated to] technical debt in our system. Specifically:

• **Contributing Factors**: [How debt played a role, if any]
• **Prevention Measures**: [Debt work planned to prevent recurrence]
• **Timeline**: [When preventive measures will be completed]

**IMMEDIATE ACTIONS**

1. [Action 1 with timeline]
2. [Action 2 with timeline]  
3. [Action 3 with timeline]

**LONG-TERM IMPROVEMENTS**

We're investing in [specific technical improvements] to prevent similar issues:

• **Infrastructure**: [Relevant infrastructure debt work]
• **Monitoring**: [Observability improvements planned]
• **Process**: [Development process improvements]

We apologize for the inconvenience and appreciate your patience as we continue to strengthen our platform.

---

## Internal Communication Templates

### Engineering All-Hands Presentation

**Slide Template: Technical Debt State of the Union**

---

**SLIDE 1: Current State**
- Health Score: [X]/100 [Trend arrow]
- Total Debt Items: [X] ([X]% of codebase)
- High Priority: [X] items requiring immediate attention
- Team Impact: [X]% velocity reduction

**SLIDE 2: What We've Accomplished**  
- Resolved [X] debt items ([X] hours of future work saved)
- Improved health score by [X] points
- Key wins: [2-3 specific examples with business impact]

**SLIDE 3: Current Focus Areas**
- [Category 1]: [X] items, [business impact]
- [Category 2]: [X] items, [business impact]  
- [Category 3]: [X] items, [business impact]

**SLIDE 4: Success Stories**
- [Specific example]: [Problem] → [Solution] → [Outcome]
- Metrics: [Before/after comparison]
- Team feedback: [Developer quotes]

**SLIDE 5: Looking Forward**
- Q[X] Goals: [Specific targets]
- Major Initiatives: [2-3 big-picture improvements]
- How You Can Help: [Specific asks of the team]

---

### Retrospective Templates

**Sprint Retrospective - Debt Focus**

**What Went Well**:
• Debt work completed: [Specific items and impact]
• Process improvements: [What worked for debt management]
• Team collaboration: [Cross-functional debt work successes]

**What Didn't Go Well**:
• Debt work challenges: [Obstacles encountered]
• Scope creep: [Debt work that expanded beyond estimates]
• Communication gaps: [Information that wasn't shared effectively]

**Action Items**:
• **Process**: [Changes to how we handle debt work]
• **Planning**: [Improvements to debt estimation/prioritization]  
• **Prevention**: [Changes to prevent new debt creation]
• **Tools**: [Tooling improvements needed]

---

## Communication Best Practices

### Do's and Don'ts

**DO**:
• Use business language, not technical jargon
• Quantify impact with specific metrics
• Provide clear timelines and expectations
• Acknowledge trade-offs and constraints
• Connect debt work to business outcomes
• Be proactive in communication

**DON'T**:
• Blame previous decisions or developers
• Use fear-based messaging exclusively
• Overwhelm stakeholders with technical details
• Make promises without clear plans
• Ignore the business context
• Assume stakeholders understand technical implications

### Tailoring Messages

**For Executives**: Focus on business impact, ROI, and strategic implications
**For Product**: Focus on feature impact, timeline risks, and user experience
**For Engineering**: Focus on technical details, process improvements, and developer experience
**For Customers**: Focus on reliability, performance, and security benefits

### Frequency Guidelines

**Real-time**: Critical security issues, production incidents
**Weekly**: Team health checks, sprint impacts  
**Monthly**: Stakeholder updates, trend analysis
**Quarterly**: Strategic reviews, investment planning
**As-needed**: Major decisions, significant changes

These templates should be customized for your organization's communication style, stakeholder preferences, and business context.