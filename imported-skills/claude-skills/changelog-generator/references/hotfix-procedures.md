# Hotfix Procedures

## Overview

Hotfixes are emergency releases designed to address critical production issues that cannot wait for the regular release cycle. This document outlines classification, procedures, and best practices for managing hotfixes across different development workflows.

## Severity Classification

### P0 - Critical (Production Down)
**Definition:** Complete system outage, data corruption, or security breach affecting all users.

**Examples:**
- Server crashes preventing any user access
- Database corruption causing data loss
- Security vulnerability being actively exploited
- Payment system completely non-functional
- Authentication system failure preventing all logins

**Response Requirements:**
- **Timeline:** Fix deployed within 2 hours
- **Approval:** Engineering Lead + On-call Manager (verbal approval acceptable)
- **Process:** Emergency deployment bypassing normal gates
- **Communication:** Immediate notification to all stakeholders
- **Documentation:** Post-incident review required within 24 hours

**Escalation:**
- Page on-call engineer immediately
- Escalate to Engineering Lead within 15 minutes
- Notify CEO/CTO if resolution exceeds 4 hours

### P1 - High (Major Feature Broken)
**Definition:** Critical functionality broken affecting significant portion of users.

**Examples:**
- Core user workflow completely broken
- Payment processing failures affecting >50% of transactions  
- Search functionality returning no results
- Mobile app crashes on startup
- API returning 500 errors for main endpoints

**Response Requirements:**
- **Timeline:** Fix deployed within 24 hours
- **Approval:** Engineering Lead + Product Manager
- **Process:** Expedited review and testing
- **Communication:** Stakeholder notification within 1 hour
- **Documentation:** Root cause analysis within 48 hours

**Escalation:**
- Notify on-call engineer within 30 minutes
- Escalate to Engineering Lead within 2 hours
- Daily updates to Product/Business stakeholders

### P2 - Medium (Minor Feature Issues)
**Definition:** Non-critical functionality issues with limited user impact.

**Examples:**
- Cosmetic UI issues affecting user experience
- Non-essential features not working properly
- Performance degradation not affecting core workflows
- Minor API inconsistencies
- Reporting/analytics data inaccuracies

**Response Requirements:**
- **Timeline:** Include in next regular release
- **Approval:** Standard pull request review process
- **Process:** Normal development and testing cycle
- **Communication:** Include in regular release notes
- **Documentation:** Standard issue tracking

**Escalation:**
- Create ticket in normal backlog
- No special escalation required
- Include in release planning discussions

## Hotfix Workflows by Development Model

### Git Flow Hotfix Process

#### Branch Structure
```
main (v1.2.3) ← hotfix/security-patch → main (v1.2.4)
                                    → develop
```

#### Step-by-Step Process
1. **Create Hotfix Branch**
   ```bash
   git checkout main
   git pull origin main
   git checkout -b hotfix/security-patch
   ```

2. **Implement Fix**
   - Make minimal changes addressing only the specific issue
   - Include tests to prevent regression
   - Update version number (patch increment)
   ```bash
   # Fix the issue
   git add .
   git commit -m "fix: resolve SQL injection vulnerability"
   
   # Version bump
   echo "1.2.4" > VERSION
   git add VERSION
   git commit -m "chore: bump version to 1.2.4"
   ```

3. **Test Fix**
   - Run automated test suite
   - Manual testing of affected functionality
   - Security review if applicable
   ```bash
   # Run tests
   npm test
   python -m pytest
   
   # Security scan
   npm audit
   bandit -r src/
   ```

4. **Deploy to Staging**
   ```bash
   # Deploy hotfix branch to staging
   git push origin hotfix/security-patch
   # Trigger staging deployment via CI/CD
   ```

5. **Merge to Production**
   ```bash
   # Merge to main
   git checkout main
   git merge --no-ff hotfix/security-patch
   git tag -a v1.2.4 -m "Hotfix: Security vulnerability patch"
   git push origin main --tags
   
   # Merge back to develop
   git checkout develop
   git merge --no-ff hotfix/security-patch
   git push origin develop
   
   # Clean up
   git branch -d hotfix/security-patch
   git push origin --delete hotfix/security-patch
   ```

### GitHub Flow Hotfix Process

#### Branch Structure
```
main ← hotfix/critical-fix → main (immediate deploy)
```

#### Step-by-Step Process
1. **Create Fix Branch**
   ```bash
   git checkout main
   git pull origin main
   git checkout -b hotfix/payment-gateway-fix
   ```

2. **Implement and Test**
   ```bash
   # Make the fix
   git add .
   git commit -m "fix(payment): resolve gateway timeout issue"
   git push origin hotfix/payment-gateway-fix
   ```

3. **Create Emergency PR**
   ```bash
   # Use GitHub CLI or web interface
   gh pr create --title "HOTFIX: Payment gateway timeout" \
                --body "Critical fix for payment processing failures" \
                --reviewer engineering-team \
                --label hotfix
   ```

4. **Deploy Branch for Testing**
   ```bash
   # Deploy branch to staging for validation
   ./deploy.sh hotfix/payment-gateway-fix staging
   # Quick smoke tests
   ```

5. **Emergency Merge and Deploy**
   ```bash
   # After approval, merge and deploy
   gh pr merge --squash
   # Automatic deployment to production via CI/CD
   ```

### Trunk-based Hotfix Process

#### Direct Commit Approach
```bash
# For small fixes, commit directly to main
git checkout main
git pull origin main
# Make fix
git add .
git commit -m "fix: resolve memory leak in user session handling"
git push origin main
# Automatic deployment triggers
```

#### Feature Flag Rollback
```bash
# For feature-related issues, disable via feature flag
curl -X POST api/feature-flags/new-search/disable
# Verify issue resolved
# Plan proper fix for next deployment
```

## Emergency Response Procedures

### Incident Declaration Process

1. **Detection and Assessment** (0-5 minutes)
   - Monitor alerts or user reports identify issue
   - Assess severity using classification matrix
   - Determine if hotfix is required

2. **Team Assembly** (5-10 minutes)
   - Page appropriate on-call engineer
   - Assemble incident response team
   - Establish communication channel (Slack, Teams)

3. **Initial Response** (10-30 minutes)
   - Create incident ticket/document
   - Begin investigating root cause
   - Implement immediate mitigations if possible

4. **Hotfix Development** (30 minutes - 2 hours)
   - Create hotfix branch
   - Implement minimal fix
   - Test fix in isolation

5. **Deployment** (15-30 minutes)
   - Deploy to staging for validation
   - Deploy to production
   - Monitor for successful resolution

6. **Verification** (15-30 minutes)
   - Confirm issue is resolved
   - Monitor system stability
   - Update stakeholders

### Communication Templates

#### P0 Initial Alert
```
🚨 CRITICAL INCIDENT - Production Down

Status: Investigating
Impact: Complete service outage
Affected Users: All users
Started: 2024-01-15 14:30 UTC
Incident Commander: @john.doe

Current Actions:
- Investigating root cause
- Preparing emergency fix
- Will update every 15 minutes

Status Page: https://status.ourapp.com
Incident Channel: #incident-2024-001
```

#### P0 Resolution Notice
```
✅ RESOLVED - Production Restored

Status: Resolved
Resolution Time: 1h 23m
Root Cause: Database connection pool exhaustion
Fix: Increased connection limits and restarted services

Timeline:
14:30 UTC - Issue detected
14:45 UTC - Root cause identified
15:20 UTC - Fix deployed
15:35 UTC - Full functionality restored

Post-incident review scheduled for tomorrow 10:00 AM.
Thank you for your patience.
```

#### P1 Status Update
```
⚠️ Issue Update - Payment Processing

Status: Fix deployed, monitoring
Impact: Payment failures reduced from 45% to <2%
ETA: Complete resolution within 2 hours

Actions taken:
- Deployed hotfix to address timeout issues
- Increased monitoring on payment gateway
- Contacting affected customers

Next update in 30 minutes or when resolved.
```

### Rollback Procedures

#### When to Rollback
- Fix doesn't resolve the issue
- Fix introduces new problems
- System stability is compromised
- Data corruption is detected

#### Rollback Process
1. **Immediate Assessment** (2-5 minutes)
   ```bash
   # Check system health
   curl -f https://api.ourapp.com/health
   # Review error logs
   kubectl logs deployment/app --tail=100
   # Check key metrics
   ```

2. **Rollback Execution** (5-15 minutes)
   ```bash
   # Git-based rollback
   git checkout main
   git revert HEAD
   git push origin main
   
   # Or container-based rollback
   kubectl rollout undo deployment/app
   
   # Or load balancer switch
   aws elbv2 modify-target-group --target-group-arn arn:aws:elasticloadbalancing:us-east-1:123456789012:targetgroup/previous-version
   ```

3. **Verification** (5-10 minutes)
   ```bash
   # Confirm rollback successful
   # Check system health endpoints
   # Verify core functionality working
   # Monitor error rates and performance
   ```

4. **Communication**
   ```
   🔄 ROLLBACK COMPLETE
   
   The hotfix has been rolled back due to [reason].
   System is now stable on previous version.
   We are investigating the issue and will provide updates.
   ```

## Testing Strategies for Hotfixes

### Pre-deployment Testing

#### Automated Testing
```bash
# Run full test suite
npm test
pytest tests/
go test ./...

# Security scanning
npm audit --audit-level high
bandit -r src/
gosec ./...

# Integration tests
./run_integration_tests.sh

# Load testing (if performance-related)
artillery quick --count 100 --num 10 https://staging.ourapp.com
```

#### Manual Testing Checklist
- [ ] Core user workflow functions correctly
- [ ] Authentication and authorization working
- [ ] Payment processing (if applicable)
- [ ] Data integrity maintained
- [ ] No new error logs or exceptions
- [ ] Performance within acceptable range
- [ ] Mobile app functionality (if applicable)
- [ ] Third-party integrations working

#### Staging Validation
```bash
# Deploy to staging
./deploy.sh hotfix/critical-fix staging

# Run smoke tests
curl -f https://staging.ourapp.com/api/health
./smoke_tests.sh

# Manual verification of specific issue
# Document test results
```

### Post-deployment Monitoring

#### Immediate Monitoring (First 30 minutes)
- Error rate and count
- Response time and latency  
- CPU and memory usage
- Database connection counts
- Key business metrics

#### Extended Monitoring (First 24 hours)
- User activity patterns
- Feature usage statistics
- Customer support tickets
- Performance trends
- Security log analysis

#### Monitoring Scripts
```bash
#!/bin/bash
# monitor_hotfix.sh - Post-deployment monitoring

echo "=== Hotfix Deployment Monitoring ==="
echo "Deployment time: $(date)"
echo

# Check application health
echo "--- Application Health ---"
curl -s https://api.ourapp.com/health | jq '.'

# Check error rates
echo "--- Error Rates (last 30min) ---"
curl -s "https://api.datadog.com/api/v1/query?query=sum:application.errors{*}" \
  -H "DD-API-KEY: $DATADOG_API_KEY" | jq '.series[0].pointlist[-1][1]'

# Check response times
echo "--- Response Times ---" 
curl -s "https://api.datadog.com/api/v1/query?query=avg:application.response_time{*}" \
  -H "DD-API-KEY: $DATADOG_API_KEY" | jq '.series[0].pointlist[-1][1]'

# Check database connections
echo "--- Database Status ---"
psql -h db.ourapp.com -U readonly -c "SELECT count(*) as active_connections FROM pg_stat_activity;"

echo "=== Monitoring Complete ==="
```

## Documentation and Learning

### Incident Documentation Template

```markdown
# Incident Report: [Brief Description]

## Summary
- **Incident ID:** INC-2024-001
- **Severity:** P0/P1/P2
- **Start Time:** 2024-01-15 14:30 UTC
- **End Time:** 2024-01-15 15:45 UTC
- **Duration:** 1h 15m
- **Impact:** [Description of user/business impact]

## Root Cause
[Detailed explanation of what went wrong and why]

## Timeline
| Time | Event |
|------|-------|
| 14:30 | Issue detected via monitoring alert |
| 14:35 | Incident team assembled |
| 14:45 | Root cause identified |
| 15:00 | Fix developed and tested |
| 15:20 | Fix deployed to production |
| 15:45 | Issue confirmed resolved |

## Resolution
[What was done to fix the issue]

## Lessons Learned
### What went well
- Quick detection through monitoring
- Effective team coordination
- Minimal user impact

### What could be improved
- Earlier detection possible with better alerting
- Testing could have caught this issue
- Communication could be more proactive

## Action Items
- [ ] Improve monitoring for [specific area]
- [ ] Add automated test for [specific scenario] 
- [ ] Update documentation for [specific process]
- [ ] Training on [specific topic] for team

## Prevention Measures
[How we'll prevent this from happening again]
```

### Post-Incident Review Process

1. **Schedule Review** (within 24-48 hours)
   - Involve all key participants
   - Book 60-90 minute session
   - Prepare incident timeline

2. **Blameless Analysis**
   - Focus on systems and processes, not individuals
   - Understand contributing factors
   - Identify improvement opportunities

3. **Action Plan**
   - Concrete, assignable tasks
   - Realistic timelines
   - Clear success criteria

4. **Follow-up**
   - Track action item completion
   - Share learnings with broader team
   - Update procedures based on insights

### Knowledge Sharing

#### Runbook Updates
After each hotfix, update relevant runbooks:
- Add new troubleshooting steps
- Update contact information
- Refine escalation procedures
- Document new tools or processes

#### Team Training
- Share incident learnings in team meetings
- Conduct tabletop exercises for common scenarios
- Update onboarding materials with hotfix procedures
- Create decision trees for severity classification

#### Automation Improvements
- Add alerts for new failure modes
- Automate manual steps where possible
- Improve deployment and rollback processes
- Enhance monitoring and observability

## Common Pitfalls and Best Practices

### Common Pitfalls

❌ **Over-engineering the fix**
- Making broad changes instead of minimal targeted fix
- Adding features while fixing bugs
- Refactoring unrelated code

❌ **Insufficient testing**
- Skipping automated tests due to time pressure
- Not testing the exact scenario that caused the issue
- Deploying without staging validation

❌ **Poor communication**
- Not notifying stakeholders promptly
- Unclear or infrequent status updates
- Forgetting to announce resolution

❌ **Inadequate monitoring**
- Not watching system health after deployment
- Missing secondary effects of the fix
- Failing to verify the issue is actually resolved

### Best Practices

✅ **Keep fixes minimal and focused**
- Address only the specific issue
- Avoid scope creep or improvements
- Save refactoring for regular releases

✅ **Maintain clear communication**
- Set up dedicated incident channel
- Provide regular status updates
- Use clear, non-technical language for business stakeholders

✅ **Test thoroughly but efficiently**
- Focus testing on affected functionality
- Use automated tests where possible
- Validate in staging before production

✅ **Document everything**
- Maintain timeline of events
- Record decisions and rationale
- Share lessons learned with team

✅ **Plan for rollback**
- Always have a rollback plan ready
- Test rollback procedure in advance
- Monitor closely after deployment

By following these procedures and continuously improving based on experience, teams can handle production emergencies effectively while minimizing impact and learning from each incident.