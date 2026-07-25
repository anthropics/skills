# Runbook Templates

## Deployment Runbook Template

- Pre-deployment checks
- Deploy steps with expected output
- Smoke tests
- Rollback plan with explicit triggers
- Escalation and communication notes

## Incident Response Template

- Triage phase (first 5 minutes)
- Diagnosis phase (logs, metrics, recent deploys)
- Mitigation phase (containment and restoration)
- Resolution and postmortem actions

## Database Maintenance Template

- Backup and restore verification
- Migration sequencing and lock-risk notes
- Vacuum/reindex routines
- Verification queries and performance checks

## Staleness Detection Template

Track referenced config files and update runbooks whenever these change:

- deployment config (`vercel.json`, Helm charts, Terraform)
- CI pipelines (`.github/workflows/*`, `.gitlab-ci.yml`)
- data schema/migration definitions
- service runtime/env configuration

## Quarterly Validation Checklist

1. Execute commands in staging.
2. Validate expected outputs.
3. Test rollback paths.
4. Confirm contact/escalation ownership.
5. Update `Last verified` date.
