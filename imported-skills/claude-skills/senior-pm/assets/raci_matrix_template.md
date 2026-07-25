# RACI Matrix Template

**Project:** [Project Name]  
**Version:** [Version Number]  
**Date:** [Creation/Update Date]  
**Owner:** [Project Manager Name]

---

## RACI Matrix Legend

| Code | Role | Description |
|------|------|-------------|
| **R** | **Responsible** | The person(s) who actually performs the work to complete the task |
| **A** | **Accountable** | The person who is ultimately answerable for the correct completion |
| **C** | **Consulted** | The person(s) whose opinions are sought and with whom there is two-way communication |
| **I** | **Informed** | The person(s) who are kept up-to-date on progress, often only one-way communication |

### RACI Best Practices
- ✅ **One A per activity** - Only one person can be accountable for each task
- ✅ **At least one R per activity** - Someone must be responsible for doing the work
- ✅ **Minimize C's** - Too many consulted stakeholders can slow decision-making
- ✅ **Strategic I's only** - Inform only those who truly need to know

---

## Stakeholder Roster

### Core Project Team
| Name | Role | Department | Contact | Availability |
|------|------|------------|---------|--------------|
| [Name] | Project Manager | PMO | [email] | 100% |
| [Name] | Product Owner | Product | [email] | 75% |
| [Name] | Technical Lead | Engineering | [email] | 90% |
| [Name] | UX Designer | Design | [email] | 50% |
| [Name] | QA Lead | Quality | [email] | 60% |

### Executive Stakeholders
| Name | Role | Department | Contact | Decision Authority |
|------|------|------------|---------|-------------------|
| [Name] | Executive Sponsor | [Department] | [email] | Budget & Strategic Direction |
| [Name] | Business Owner | [Department] | [email] | Requirements & Acceptance |
| [Name] | Technical Owner | [Department] | [email] | Architecture & Standards |

### Extended Stakeholders
| Name | Role | Department | Contact | Interest Level |
|------|------|------------|---------|----------------|
| [Name] | [Role] | [Department] | [email] | High/Medium/Low |
| [Name] | [Role] | [Department] | [email] | High/Medium/Low |

---

## Project Phase RACI Matrices

### Phase 1: Project Initiation & Planning

| Activity | Project Manager | Executive Sponsor | Business Owner | Product Owner | Technical Lead |
|----------|-----------------|-------------------|----------------|---------------|----------------|
| **Business Case Development** | R | A | R | C | C |
| **Project Charter Creation** | A, R | A | C | C | C |
| **Stakeholder Analysis** | A, R | C | R | C | I |
| **Initial Requirements Gathering** | A | I | R | R | C |
| **High-Level Architecture** | A | I | C | C | R |
| **Resource Planning** | A, R | A | C | C | C |
| **Budget Approval** | R | A | C | I | I |
| **Risk Assessment** | A, R | C | C | C | R |
| **Project Charter Sign-off** | R | A | A | C | C |

### Phase 2: Design & Development Setup

| Activity | Project Manager | Product Owner | Technical Lead | UX Designer | QA Lead |
|----------|-----------------|---------------|----------------|-------------|---------|
| **Requirements Documentation** | A | R | C | C | C |
| **Technical Architecture** | A | C | R | I | C |
| **System Design Documentation** | A | C | R | C | C |
| **UI/UX Design** | A | R | C | R | I |
| **Database Design** | A | I | R | I | C |
| **API Specifications** | A | C | R | I | C |
| **Test Strategy** | A | C | C | I | R |
| **Development Environment Setup** | A | I | R | I | C |
| **CI/CD Pipeline Setup** | A | I | R | I | R |

### Phase 3: Development & Implementation

| Activity | Project Manager | Product Owner | Technical Lead | Dev Team | QA Lead |
|----------|-----------------|---------------|----------------|----------|---------|
| **Sprint Planning** | R | A | R | R | C |
| **User Story Development** | A | R | C | C | C |
| **Code Development** | A | C | R | R | I |
| **Code Reviews** | I | I | A | R | I |
| **Unit Testing** | I | I | R | R | C |
| **Integration Testing** | A | C | R | R | R |
| **Feature Testing** | A | R | C | I | R |
| **Bug Triage** | R | A | R | R | R |
| **Sprint Reviews** | A, R | R | R | R | R |

### Phase 4: Testing & Quality Assurance

| Activity | Project Manager | Product Owner | Technical Lead | QA Lead | Business Owner |
|----------|-----------------|---------------|----------------|---------|----------------|
| **Test Plan Creation** | A | C | C | R | C |
| **System Testing** | A | C | C | R | I |
| **Performance Testing** | A | C | R | R | I |
| **Security Testing** | A | I | R | R | I |
| **User Acceptance Testing** | A | R | C | C | R |
| **Bug Resolution** | A | C | R | R | I |
| **Go-Live Readiness** | A | R | R | R | R |
| **Sign-off Documentation** | R | R | C | R | A |

### Phase 5: Deployment & Launch

| Activity | Project Manager | Technical Lead | DevOps | Business Owner | Support Team |
|----------|-----------------|----------------|--------|----------------|--------------|
| **Deployment Planning** | A | R | R | C | C |
| **Production Deployment** | A | R | R | I | I |
| **Smoke Testing** | A | R | C | C | R |
| **Go-Live Communication** | R | C | I | A | I |
| **User Training** | A | C | I | R | C |
| **Support Documentation** | A | C | C | C | R |
| **Monitoring Setup** | A | R | R | I | R |
| **Launch Retrospective** | A, R | R | C | R | C |

---

## Decision-Making RACI

### Strategic Decisions
| Decision Type | Project Manager | Executive Sponsor | Business Owner | Technical Owner |
|---------------|-----------------|-------------------|----------------|-----------------|
| **Budget Changes >10%** | R | A | C | C |
| **Scope Changes (Major)** | R | A | R | C |
| **Timeline Changes >2 weeks** | R | A | R | C |
| **Technology Platform Changes** | R | C | C | A |
| **Resource Reallocation** | A, R | A | C | C |
| **Go/No-Go Decisions** | R | A | R | R |

### Operational Decisions
| Decision Type | Project Manager | Product Owner | Technical Lead | Team Members |
|---------------|-----------------|---------------|----------------|--------------|
| **Sprint Scope** | C | A | R | R |
| **Technical Implementation** | C | C | A, R | R |
| **Bug Priority** | A | R | C | C |
| **Code Standards** | C | C | A, R | R |
| **Testing Approach** | A | C | R | R |
| **Daily Task Assignment** | I | C | A | R |

---

## Escalation Paths & Conflict Resolution

### Escalation Matrix
| Issue Level | Primary Resolver | Escalation To | Timeline | Authority |
|-------------|------------------|---------------|----------|-----------|
| **Level 1: Task/Technical** | Team Member → Technical Lead | Product Owner | 24 hours | Technical decisions |
| **Level 2: Sprint/Feature** | Technical Lead → Product Owner | Project Manager | 48 hours | Feature scope/priority |
| **Level 3: Project Impact** | Project Manager → Business Owner | Executive Sponsor | 72 hours | Budget/timeline changes |
| **Level 4: Strategic** | Executive Sponsor → Steering Committee | CEO/Board | 1 week | Strategic direction |

### Conflict Resolution Process
1. **Direct Resolution** (Level 1)
   - **Who:** Conflicting parties attempt direct resolution
   - **Timeline:** 24 hours
   - **Documentation:** Brief note in project log

2. **Mediated Resolution** (Level 2)  
   - **Who:** Project Manager facilitates discussion
   - **Timeline:** 48 hours from escalation
   - **Documentation:** Decision recorded with rationale

3. **Executive Resolution** (Level 3)
   - **Who:** Executive Sponsor makes binding decision
   - **Timeline:** 72 hours from escalation  
   - **Documentation:** Formal decision memo to all stakeholders

4. **Steering Committee** (Level 4)
   - **Who:** Full steering committee vote
   - **Timeline:** Next scheduled meeting (max 1 week)
   - **Documentation:** Board resolution or meeting minutes

### Communication Protocols
- **Escalation Notification:** All RACI stakeholders informed within 4 hours
- **Decision Communication:** Decision communicated to all affected parties within 24 hours
- **Documentation:** All escalations and resolutions logged in project management system

---

## Communication & Meeting RACI

### Regular Meetings
| Meeting Type | Frequency | Project Manager | Team | Stakeholders | Sponsor |
|-------------|-----------|-----------------|------|--------------|---------|
| **Daily Standup** | Daily | A | R | I | I |
| **Sprint Planning** | Bi-weekly | A | R | C | I |
| **Sprint Review** | Bi-weekly | R | R | A | C |
| **Stakeholder Updates** | Weekly | A, R | C | R | A |
| **Steering Committee** | Monthly | R | I | C | A |

### Communication Artifacts
| Artifact | Creator (R) | Approver (A) | Reviewers (C) | Recipients (I) |
|----------|-------------|-------------|---------------|----------------|
| **Status Reports** | Project Manager | Business Owner | Team Leads | All Stakeholders |
| **Risk Register** | Project Manager | Executive Sponsor | Risk Owners | Steering Committee |
| **Change Requests** | Requestor | Business Owner | Project Manager | Affected Teams |
| **Decision Log** | Project Manager | Decision Maker | Consulted Parties | All Stakeholders |

---

## Risk & Issue Management RACI

### Risk Management
| Activity | Project Manager | Risk Owner | Executive Sponsor | Team |
|----------|-----------------|------------|-------------------|------|
| **Risk Identification** | A | R | C | R |
| **Risk Assessment** | A | R | C | C |
| **Mitigation Planning** | A | R | C | R |
| **Risk Monitoring** | A | R | I | C |
| **Risk Escalation** | R | R | A | I |

### Issue Resolution
| Issue Severity | Reporter (R) | Owner (A) | Resolver (R) | Informed (I) |
|----------------|-------------|-----------|-------------|-------------|
| **Critical** | Anyone | Project Manager | Technical Lead | Executive Sponsor |
| **High** | Team/Stakeholder | Technical Lead | Team Member | Project Manager |
| **Medium** | Team Member | Team Lead | Team Member | Project Manager |
| **Low** | Team Member | Team Member | Team Member | Team Lead |

---

## RACI Validation & Maintenance

### Validation Checklist
- [ ] Every activity has exactly one "A" (Accountable)
- [ ] Every activity has at least one "R" (Responsible) 
- [ ] "C" (Consulted) roles are minimized to essential stakeholders
- [ ] "I" (Informed) includes only those who truly need updates
- [ ] No person is assigned "A" for more tasks than they can handle
- [ ] Escalation paths are clear and realistic
- [ ] Decision rights match organizational authority

### Review & Update Process
- **Review Frequency:** Every project phase or monthly
- **Update Triggers:** Team changes, scope changes, organizational changes
- **Approval Process:** Changes require Project Manager and Executive Sponsor approval
- **Communication:** RACI updates communicated to all stakeholders within 48 hours

### RACI Health Metrics
| Metric | Target | Current | Notes |
|--------|---------|---------|-------|
| **Decision Speed** | <48 hours | [X] hours | Average time for routine decisions |
| **Escalation Rate** | <10% | [X]% | Percentage of issues requiring escalation |
| **Role Clarity** | >90% | [X]% | Stakeholder survey on role understanding |
| **Conflict Resolution** | <72 hours | [X] hours | Average resolution time |

---

**Document Control:**
- **Version:** [Version Number]
- **Last Updated:** [Date]
- **Next Review:** [Date]  
- **Approved By:** [Executive Sponsor Name]

**Distribution List:**
- All Project Stakeholders (as identified in roster)
- PMO (for template compliance)
- HR (for role clarity and performance management)