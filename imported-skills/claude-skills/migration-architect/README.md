# Migration Architect

**Tier:** POWERFUL  
**Category:** Engineering - Migration Strategy  
**Purpose:** Zero-downtime migration planning, compatibility validation, and rollback strategy generation

## Overview

The Migration Architect skill provides comprehensive tools and methodologies for planning, executing, and validating complex system migrations with minimal business impact. This skill combines proven migration patterns with automated planning tools to ensure successful transitions between systems, databases, and infrastructure.

## Components

### Core Scripts

1. **migration_planner.py** - Automated migration plan generation
2. **compatibility_checker.py** - Schema and API compatibility analysis  
3. **rollback_generator.py** - Comprehensive rollback procedure generation

### Reference Documentation

- **migration_patterns_catalog.md** - Detailed catalog of proven migration patterns
- **zero_downtime_techniques.md** - Comprehensive zero-downtime migration techniques
- **data_reconciliation_strategies.md** - Advanced data consistency and reconciliation strategies

### Sample Assets

- **sample_database_migration.json** - Example database migration specification
- **sample_service_migration.json** - Example service migration specification
- **database_schema_before.json** - Sample "before" database schema
- **database_schema_after.json** - Sample "after" database schema

## Quick Start

### 1. Generate a Migration Plan

```bash
python3 scripts/migration_planner.py \
  --input assets/sample_database_migration.json \
  --output migration_plan.json \
  --format both
```

**Input:** Migration specification with source, target, constraints, and requirements
**Output:** Detailed phased migration plan with risk assessment, timeline, and validation gates

### 2. Check Compatibility

```bash
python3 scripts/compatibility_checker.py \
  --before assets/database_schema_before.json \
  --after assets/database_schema_after.json \
  --type database \
  --output compatibility_report.json \
  --format both
```

**Input:** Before and after schema definitions
**Output:** Compatibility report with breaking changes, migration scripts, and recommendations

### 3. Generate Rollback Procedures

```bash
python3 scripts/rollback_generator.py \
  --input migration_plan.json \
  --output rollback_runbook.json \
  --format both
```

**Input:** Migration plan from step 1
**Output:** Comprehensive rollback runbook with procedures, triggers, and communication templates

## Script Details

### Migration Planner (`migration_planner.py`)

Generates comprehensive migration plans with:

- **Phased approach** with dependencies and validation gates
- **Risk assessment** with mitigation strategies
- **Timeline estimation** based on complexity and constraints
- **Rollback triggers** and success criteria
- **Stakeholder communication** templates

**Usage:**
```bash
python3 scripts/migration_planner.py [OPTIONS]

Options:
  --input, -i     Input migration specification file (JSON) [required]
  --output, -o    Output file for migration plan (JSON)
  --format, -f    Output format: json, text, both (default: both)
  --validate      Validate migration specification only
```

**Input Format:**
```json
{
  "type": "database|service|infrastructure",
  "pattern": "schema_change|strangler_fig|blue_green",
  "source": "Source system description",
  "target": "Target system description", 
  "constraints": {
    "max_downtime_minutes": 30,
    "data_volume_gb": 2500,
    "dependencies": ["service1", "service2"],
    "compliance_requirements": ["GDPR", "SOX"]
  }
}
```

### Compatibility Checker (`compatibility_checker.py`)

Analyzes compatibility between schema versions:

- **Breaking change detection** (removed fields, type changes, constraint additions)
- **Data migration requirements** identification
- **Suggested migration scripts** generation
- **Risk assessment** for each change

**Usage:**
```bash
python3 scripts/compatibility_checker.py [OPTIONS]

Options:
  --before        Before schema file (JSON) [required]
  --after         After schema file (JSON) [required]
  --type          Schema type: database, api (default: database)
  --output, -o    Output file for compatibility report (JSON)
  --format, -f    Output format: json, text, both (default: both)
```

**Exit Codes:**
- `0`: No compatibility issues
- `1`: Potentially breaking changes found
- `2`: Breaking changes found

### Rollback Generator (`rollback_generator.py`)

Creates comprehensive rollback procedures:

- **Phase-by-phase rollback** steps
- **Automated trigger conditions** for rollback
- **Data recovery procedures** 
- **Communication templates** for different audiences
- **Validation checklists** for rollback success

**Usage:**
```bash
python3 scripts/rollback_generator.py [OPTIONS]

Options:
  --input, -i     Input migration plan file (JSON) [required]
  --output, -o    Output file for rollback runbook (JSON)
  --format, -f    Output format: json, text, both (default: both)
```

## Migration Patterns Supported

### Database Migrations

- **Expand-Contract Pattern** - Zero-downtime schema evolution
- **Parallel Schema Pattern** - Side-by-side schema migration
- **Event Sourcing Migration** - Event-driven data migration

### Service Migrations

- **Strangler Fig Pattern** - Gradual legacy system replacement
- **Parallel Run Pattern** - Risk mitigation through dual execution
- **Blue-Green Deployment** - Zero-downtime service updates

### Infrastructure Migrations

- **Lift and Shift** - Quick cloud migration with minimal changes
- **Hybrid Cloud Migration** - Gradual cloud adoption
- **Multi-Cloud Migration** - Distribution across multiple providers

## Sample Workflow

### 1. Database Schema Migration

```bash
# Generate migration plan
python3 scripts/migration_planner.py \
  --input assets/sample_database_migration.json \
  --output db_migration_plan.json

# Check schema compatibility
python3 scripts/compatibility_checker.py \
  --before assets/database_schema_before.json \
  --after assets/database_schema_after.json \
  --type database \
  --output schema_compatibility.json

# Generate rollback procedures
python3 scripts/rollback_generator.py \
  --input db_migration_plan.json \
  --output db_rollback_runbook.json
```

### 2. Service Migration

```bash
# Generate service migration plan
python3 scripts/migration_planner.py \
  --input assets/sample_service_migration.json \
  --output service_migration_plan.json

# Generate rollback procedures
python3 scripts/rollback_generator.py \
  --input service_migration_plan.json \
  --output service_rollback_runbook.json
```

## Output Examples

### Migration Plan Structure

```json
{
  "migration_id": "abc123def456",
  "source_system": "Legacy User Service",
  "target_system": "New User Service",
  "migration_type": "service",
  "complexity": "medium",
  "estimated_duration_hours": 72,
  "phases": [
    {
      "name": "preparation",
      "description": "Prepare systems and teams for migration",
      "duration_hours": 8,
      "validation_criteria": ["All backups completed successfully"],
      "rollback_triggers": ["Critical system failure"],
      "risk_level": "medium"
    }
  ],
  "risks": [
    {
      "category": "technical",
      "description": "Service compatibility issues",
      "severity": "high",
      "mitigation": "Comprehensive integration testing"
    }
  ]
}
```

### Compatibility Report Structure

```json
{
  "overall_compatibility": "potentially_incompatible",
  "breaking_changes_count": 2,
  "potentially_breaking_count": 3,
  "issues": [
    {
      "type": "required_column_added", 
      "severity": "breaking",
      "description": "Required column 'email_verified_at' added",
      "suggested_migration": "Add default value initially"
    }
  ],
  "migration_scripts": [
    {
      "script_type": "sql",
      "description": "Add email verification columns",
      "script_content": "ALTER TABLE users ADD COLUMN email_verified_at TIMESTAMP;",
      "rollback_script": "ALTER TABLE users DROP COLUMN email_verified_at;"
    }
  ]
}
```

## Best Practices

### Planning Phase
1. **Start with risk assessment** - Identify failure modes before planning
2. **Design for rollback** - Every step should have a tested rollback procedure
3. **Validate in staging** - Execute full migration in production-like environment
4. **Plan gradual rollout** - Use feature flags and traffic routing

### Execution Phase
1. **Monitor continuously** - Track technical and business metrics
2. **Communicate proactively** - Keep stakeholders informed
3. **Document everything** - Maintain detailed logs for analysis
4. **Stay flexible** - Be prepared to adjust based on real-world performance

### Validation Phase
1. **Automate validation** - Use automated consistency and performance checks
2. **Test business logic** - Validate critical business processes end-to-end
3. **Load test** - Verify performance under expected production load
4. **Security validation** - Ensure security controls function properly

## Integration

### CI/CD Pipeline Integration

```yaml
# Example GitHub Actions workflow
name: Migration Validation
on: [push, pull_request]

jobs:
  validate-migration:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Validate Migration Plan
        run: |
          python3 scripts/migration_planner.py \
            --input migration_spec.json \
            --validate
      - name: Check Compatibility
        run: |
          python3 scripts/compatibility_checker.py \
            --before schema_before.json \
            --after schema_after.json \
            --type database
```

### Monitoring Integration

The tools generate metrics and alerts that can be integrated with:
- **Prometheus** - For metrics collection
- **Grafana** - For visualization and dashboards
- **PagerDuty** - For incident management
- **Slack** - For team notifications

## Advanced Features

### Machine Learning Integration
- Anomaly detection for data consistency issues
- Predictive analysis for migration success probability
- Automated pattern recognition for migration optimization

### Performance Optimization
- Parallel processing for large-scale migrations
- Incremental reconciliation strategies
- Statistical sampling for validation

### Compliance Support
- GDPR compliance tracking
- SOX audit trail generation
- HIPAA security validation

## Troubleshooting

### Common Issues

**"Migration plan validation failed"**
- Check JSON syntax in migration specification
- Ensure all required fields are present
- Validate constraint values are realistic

**"Compatibility checker reports false positives"**
- Review excluded fields configuration
- Check data type mapping compatibility
- Adjust tolerance settings for numerical comparisons

**"Rollback procedures seem incomplete"**
- Ensure migration plan includes all phases
- Verify database backup locations are specified
- Check that all dependencies are documented

### Getting Help

1. **Review documentation** - Check reference docs for patterns and techniques
2. **Examine sample files** - Use provided assets as templates
3. **Check expected outputs** - Compare your results with sample outputs
4. **Validate inputs** - Ensure input files match expected format

## Contributing

To extend or modify the Migration Architect skill:

1. **Add new patterns** - Extend pattern templates in migration_planner.py
2. **Enhance compatibility checks** - Add new validation rules in compatibility_checker.py
3. **Improve rollback procedures** - Add specialized rollback steps in rollback_generator.py
4. **Update documentation** - Keep reference docs current with new patterns

## License

This skill is part of the claude-skills repository and follows the same license terms.