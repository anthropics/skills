# Incident Commander Skill

A comprehensive incident response framework providing structured tools for managing technology incidents from detection through resolution and post-incident review.

## Overview

This skill implements battle-tested practices from SRE and DevOps teams at scale, providing:

- **Automated Severity Classification** - Intelligent incident triage
- **Timeline Reconstruction** - Transform scattered events into coherent narratives
- **Post-Incident Review Generation** - Structured PIRs with RCA frameworks
- **Communication Templates** - Pre-built stakeholder communication
- **Comprehensive Documentation** - Reference guides for incident response

## Quick Start

### Classify an Incident

```bash
# From JSON file
python scripts/incident_classifier.py --input incident.json --format text

# From stdin text
echo "Database is down affecting all users" | python scripts/incident_classifier.py --format text

# Interactive mode
python scripts/incident_classifier.py --interactive
```

### Reconstruct Timeline

```bash
# Analyze event timeline
python scripts/timeline_reconstructor.py --input events.json --format text

# With gap analysis
python scripts/timeline_reconstructor.py --input events.json --gap-analysis --format markdown
```

### Generate PIR Document

```bash
# Basic PIR
python scripts/pir_generator.py --incident incident.json --format markdown

# Comprehensive PIR with timeline
python scripts/pir_generator.py --incident incident.json --timeline timeline.json --rca-method fishbone
```

## Scripts

### incident_classifier.py

**Purpose:** Analyzes incident descriptions and provides severity classification, team recommendations, and response templates.

**Input:** JSON object with incident details or plain text description
**Output:** JSON + human-readable classification report

**Example Input:**
```json
{
  "description": "Database connection timeouts causing 500 errors",
  "service": "payment-api",
  "affected_users": "80%",
  "business_impact": "high"
}
```

**Key Features:**
- SEV1-4 severity classification
- Recommended response teams
- Initial action prioritization
- Communication templates
- Response timelines

### timeline_reconstructor.py

**Purpose:** Reconstructs incident timelines from timestamped events, identifies phases, and performs gap analysis.

**Input:** JSON array of timestamped events
**Output:** Formatted timeline with phase analysis and metrics

**Example Input:**
```json
[
  {
    "timestamp": "2024-01-01T12:00:00Z",
    "source": "monitoring",
    "message": "High error rate detected",
    "severity": "critical",
    "actor": "system"
  }
]
```

**Key Features:**
- Phase detection (detection → triage → mitigation → resolution)
- Duration analysis
- Gap identification
- Communication effectiveness analysis
- Response metrics

### pir_generator.py

**Purpose:** Generates comprehensive Post-Incident Review documents with multiple RCA frameworks.

**Input:** Incident data JSON, optional timeline data
**Output:** Structured PIR document with RCA analysis

**Key Features:**
- Multiple RCA methods (5 Whys, Fishbone, Timeline, Bow Tie)
- Automated action item generation
- Lessons learned categorization
- Follow-up planning
- Completeness assessment

## Sample Data

The `assets/` directory contains sample data files for testing:

- `sample_incident_classification.json` - Database connection pool exhaustion incident
- `sample_timeline_events.json` - Complete timeline with 21 events across phases
- `sample_incident_pir_data.json` - Comprehensive incident data for PIR generation
- `simple_incident.json` - Minimal incident for basic testing
- `simple_timeline_events.json` - Simple 4-event timeline

## Expected Outputs

The `expected_outputs/` directory contains reference outputs showing what each script produces:

- `incident_classification_text_output.txt` - Detailed classification report
- `timeline_reconstruction_text_output.txt` - Complete timeline analysis
- `pir_markdown_output.md` - Full PIR document
- `simple_incident_classification.txt` - Basic classification example

## Reference Documentation

### references/incident_severity_matrix.md
Complete severity classification system with:
- SEV1-4 definitions and criteria
- Response requirements and timelines
- Escalation paths
- Communication requirements
- Decision trees and examples

### references/rca_frameworks_guide.md  
Detailed guide for root cause analysis:
- 5 Whys methodology
- Fishbone (Ishikawa) diagram analysis
- Timeline analysis techniques
- Bow Tie analysis for high-risk incidents
- Framework selection guidelines

### references/communication_templates.md
Standardized communication templates:
- Severity-specific notification templates
- Stakeholder-specific messaging
- Escalation communications
- Resolution notifications
- Customer communication guidelines

## Usage Patterns

### End-to-End Incident Workflow

1. **Initial Classification**
```bash
echo "Payment API returning 500 errors for 70% of requests" | \
  python scripts/incident_classifier.py --format text
```

2. **Timeline Reconstruction** (after collecting events)
```bash
python scripts/timeline_reconstructor.py \
  --input events.json \
  --gap-analysis \
  --format markdown \
  --output timeline.md
```

3. **PIR Generation** (after incident resolution)
```bash
python scripts/pir_generator.py \
  --incident incident.json \
  --timeline timeline.md \
  --rca-method fishbone \
  --output pir.md
```

### Integration Examples

**CI/CD Pipeline Integration:**
```bash
# Classify deployment issues
cat deployment_error.log | python scripts/incident_classifier.py --format json
```

**Monitoring Integration:**
```bash
# Process alert events
curl -s "monitoring-api/events" | python scripts/timeline_reconstructor.py --format text
```

**Runbook Generation:**
Use classification output to automatically select appropriate runbooks and escalation procedures.

## Quality Standards

- **Zero External Dependencies** - All scripts use only Python standard library
- **Dual Output Format** - Both JSON (machine-readable) and text (human-readable)
- **Robust Input Handling** - Graceful handling of missing or malformed data
- **Professional Defaults** - Opinionated, battle-tested configurations
- **Comprehensive Testing** - Sample data and expected outputs included

## Technical Requirements

- Python 3.6+
- No external dependencies required
- Works with standard Unix tools (pipes, redirection)
- Cross-platform compatible

## Severity Classification Reference

| Severity | Description | Response Time | Update Frequency |
|----------|-------------|---------------|------------------|
| **SEV1** | Complete outage | 5 minutes | Every 15 minutes |
| **SEV2** | Major degradation | 15 minutes | Every 30 minutes |
| **SEV3** | Minor impact | 2 hours | At milestones |
| **SEV4** | Low impact | 1-2 days | Weekly |

## Getting Help

Each script includes comprehensive help:
```bash
python scripts/incident_classifier.py --help
python scripts/timeline_reconstructor.py --help  
python scripts/pir_generator.py --help
```

For methodology questions, refer to the reference documentation in the `references/` directory.

## Contributing

When adding new features:
1. Maintain zero external dependencies
2. Add comprehensive examples to `assets/`
3. Update expected outputs in `expected_outputs/`
4. Follow the established patterns for argument parsing and output formatting

## License

This skill is part of the claude-skills repository. See the main repository LICENSE for details.