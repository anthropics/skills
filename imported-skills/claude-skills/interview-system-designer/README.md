# Interview System Designer

A comprehensive toolkit for designing, optimizing, and calibrating interview processes. This skill provides tools to create role-specific interview loops, generate competency-based question banks, and analyze hiring data for bias and calibration issues.

## Overview

The Interview System Designer skill includes three powerful Python tools and comprehensive reference materials to help you build fair, effective, and scalable hiring processes:

1. **Interview Loop Designer** - Generate calibrated interview loops for any role and level
2. **Question Bank Generator** - Create competency-based interview questions with scoring rubrics
3. **Hiring Calibrator** - Analyze interview data to detect bias and calibration issues

## Tools

### 1. Interview Loop Designer (`loop_designer.py`)

Generates complete interview loops tailored to specific roles, levels, and teams.

**Features:**
- Role-specific competency mapping (SWE, PM, Designer, Data, DevOps, Leadership)
- Level-appropriate interview rounds (junior through principal)
- Optimized scheduling and time allocation
- Interviewer skill requirements
- Standardized scorecard templates

**Usage:**
```bash
# Basic usage
python3 loop_designer.py --role "Senior Software Engineer" --level senior

# With team and custom competencies  
python3 loop_designer.py --role "Product Manager" --level mid --team growth --competencies leadership,strategy,analytics

# Using JSON input file
python3 loop_designer.py --input assets/sample_role_definitions.json --output loops/

# Specify output format
python3 loop_designer.py --role "Staff Data Scientist" --level staff --format json --output data_scientist_loop.json
```

**Input Options:**
- `--role`: Job role title (e.g., "Senior Software Engineer", "Product Manager")
- `--level`: Experience level (junior, mid, senior, staff, principal)
- `--team`: Team or department (optional)
- `--competencies`: Comma-separated list of specific competencies to focus on
- `--input`: JSON file with role definition
- `--output`: Output directory or file path
- `--format`: Output format (json, text, both) - default: both

**Example Output:**
```
Interview Loop Design for Senior Software Engineer (Senior Level)
============================================================
Total Duration: 300 minutes (5h 0m)
Total Rounds: 5

INTERVIEW ROUNDS
----------------------------------------
Round 1: Technical Phone Screen
Duration: 45 minutes
Format: Virtual
Focus Areas: Coding Fundamentals, Problem Solving

Round 2: System Design  
Duration: 75 minutes
Format: Collaborative Whitboard
Focus Areas: System Thinking, Architectural Reasoning
...
```

### 2. Question Bank Generator (`question_bank_generator.py`)

Creates comprehensive interview question banks organized by competency area.

**Features:**
- Competency-based question organization
- Level-appropriate difficulty progression  
- Multiple question types (technical, behavioral, situational)
- Detailed scoring rubrics with calibration examples
- Follow-up probes and conversation guides

**Usage:**
```bash
# Generate questions for specific competencies
python3 question_bank_generator.py --role "Frontend Engineer" --competencies react,typescript,system-design

# Create behavioral question bank
python3 question_bank_generator.py --role "Product Manager" --question-types behavioral,leadership --num-questions 15

# Generate questions for multiple levels
python3 question_bank_generator.py --role "DevOps Engineer" --levels junior,mid,senior --output questions/
```

**Input Options:**
- `--role`: Job role title
- `--level`: Experience level (default: senior)
- `--competencies`: Comma-separated list of competencies to focus on
- `--question-types`: Types to include (technical, behavioral, situational)
- `--num-questions`: Number of questions to generate (default: 20)
- `--input`: JSON file with role requirements
- `--output`: Output directory or file path
- `--format`: Output format (json, text, both) - default: both

**Question Types:**
- **Technical**: Coding problems, system design, domain-specific challenges
- **Behavioral**: STAR method questions focusing on past experiences  
- **Situational**: Hypothetical scenarios testing decision-making

### 3. Hiring Calibrator (`hiring_calibrator.py`)

Analyzes interview scores to detect bias, calibration issues, and provides recommendations.

**Features:**
- Statistical bias detection across demographics
- Interviewer calibration analysis
- Score distribution and trending analysis
- Specific coaching recommendations
- Comprehensive reporting with actionable insights

**Usage:**
```bash
# Comprehensive analysis
python3 hiring_calibrator.py --input assets/sample_interview_results.json --analysis-type comprehensive

# Focus on specific areas
python3 hiring_calibrator.py --input interview_data.json --analysis-type bias --competencies technical,leadership

# Trend analysis over time
python3 hiring_calibrator.py --input historical_data.json --trend-analysis --period quarterly
```

**Input Options:**
- `--input`: JSON file with interview results data (required)
- `--analysis-type`: Type of analysis (comprehensive, bias, calibration, interviewer, scoring)
- `--competencies`: Comma-separated list of competencies to focus on
- `--trend-analysis`: Enable trend analysis over time
- `--period`: Time period for trends (daily, weekly, monthly, quarterly)
- `--output`: Output file path
- `--format`: Output format (json, text, both) - default: both

**Analysis Types:**
- **Comprehensive**: Full analysis including bias, calibration, and recommendations
- **Bias**: Focus on demographic and interviewer bias patterns
- **Calibration**: Interviewer consistency and agreement analysis
- **Interviewer**: Individual interviewer performance and coaching needs
- **Scoring**: Score distribution and pattern analysis

## Data Formats

### Role Definition Input (JSON)
```json
{
  "role": "Senior Software Engineer",
  "level": "senior", 
  "team": "platform",
  "competencies": ["system_design", "technical_leadership", "mentoring"],
  "requirements": {
    "years_experience": "5-8",
    "technical_skills": ["Python", "AWS", "Kubernetes"],
    "leadership_experience": true
  }
}
```

### Interview Results Input (JSON)
```json
[
  {
    "candidate_id": "candidate_001",
    "role": "Senior Software Engineer",
    "interviewer_id": "interviewer_alice", 
    "date": "2024-01-15T09:00:00Z",
    "scores": {
      "coding_fundamentals": 3.5,
      "system_design": 4.0,
      "technical_leadership": 3.0,
      "communication": 3.5
    },
    "overall_recommendation": "Hire",
    "gender": "male",
    "ethnicity": "asian",
    "years_experience": 6
  }
]
```

## Reference Materials

### Competency Matrix Templates (`references/competency_matrix_templates.md`)
- Comprehensive competency matrices for all engineering roles
- Level-specific expectations (junior through principal)
- Assessment criteria and growth paths
- Customization guidelines for different company stages and industries

### Bias Mitigation Checklist (`references/bias_mitigation_checklist.md`)
- Pre-interview preparation checklist
- Interview process bias prevention strategies
- Real-time bias interruption techniques
- Legal compliance reminders
- Emergency response protocols

### Debrief Facilitation Guide (`references/debrief_facilitation_guide.md`)
- Structured debrief meeting frameworks
- Evidence-based discussion techniques
- Bias interruption strategies
- Decision documentation standards
- Common challenges and solutions

## Sample Data

The `assets/` directory contains sample data for testing:

- `sample_role_definitions.json`: Example role definitions for various positions
- `sample_interview_results.json`: Sample interview data with multiple candidates and interviewers

## Expected Outputs

The `expected_outputs/` directory contains examples of tool outputs:

- Interview loop designs in both JSON and human-readable formats
- Question banks with scoring rubrics and calibration examples
- Calibration analysis reports with bias detection and recommendations

## Best Practices

### Interview Loop Design
1. **Competency Focus**: Align interview rounds with role-critical competencies
2. **Level Calibration**: Adjust expectations and question difficulty based on experience level
3. **Time Optimization**: Balance thoroughness with candidate experience
4. **Interviewer Training**: Ensure interviewers are qualified and calibrated

### Question Bank Development  
1. **Evidence-Based**: Focus on observable behaviors and concrete examples
2. **Bias Mitigation**: Use structured questions that minimize subjective interpretation
3. **Calibration**: Include examples of different quality responses for consistency
4. **Continuous Improvement**: Regularly update questions based on predictive validity

### Calibration Analysis
1. **Regular Monitoring**: Analyze hiring data quarterly for bias patterns
2. **Prompt Action**: Address calibration issues immediately with targeted coaching
3. **Data Quality**: Ensure complete and consistent data collection
4. **Legal Compliance**: Monitor for discriminatory patterns and document corrections

## Installation & Setup

No external dependencies required - uses Python 3 standard library only.

```bash
# Clone or download the skill directory
cd interview-system-designer/

# Make scripts executable (optional)
chmod +x *.py

# Test with sample data
python3 loop_designer.py --role "Senior Software Engineer" --level senior
python3 question_bank_generator.py --role "Product Manager" --level mid  
python3 hiring_calibrator.py --input assets/sample_interview_results.json
```

## Integration

### With Existing Systems
- **ATS Integration**: Export interview loops as structured data for applicant tracking systems
- **Calendar Systems**: Use scheduling outputs to auto-create interview blocks
- **HR Analytics**: Import calibration reports into broader diversity and inclusion dashboards

### Custom Workflows
- **Batch Processing**: Process multiple roles or historical data sets
- **Automated Reporting**: Schedule regular calibration analysis
- **Custom Competencies**: Extend frameworks with company-specific competencies

## Troubleshooting

### Common Issues

**"Role not found" errors:**
- The tool will map common variations (engineer → software_engineer)
- For custom roles, use the closest standard role and specify custom competencies

**"Insufficient data" errors:**
- Minimum 5 interviews required for statistical analysis
- Ensure interview data includes required fields (candidate_id, interviewer_id, scores, date)

**Missing output files:**
- Check file permissions in output directory
- Ensure adequate disk space
- Verify JSON input file format is valid

### Performance Considerations

- Interview loop generation: < 1 second
- Question bank generation: 1-3 seconds for 20 questions  
- Calibration analysis: 1-5 seconds for 50 interviews, scales linearly

## Contributing

To extend this skill:

1. **New Roles**: Add competency frameworks in `_init_competency_frameworks()`
2. **New Question Types**: Extend question templates in respective generators
3. **New Analysis Types**: Add analysis methods to hiring calibrator
4. **Custom Outputs**: Modify formatting functions for different output needs

## License & Usage

This skill is designed for internal company use in hiring process optimization. All bias detection and mitigation features should be reviewed with legal counsel to ensure compliance with local employment laws.

For questions or support, refer to the comprehensive documentation in each script's docstring and the reference materials provided.