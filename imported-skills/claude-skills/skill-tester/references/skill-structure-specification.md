# Skill Structure Specification

**Version**: 1.0.0  
**Last Updated**: 2026-02-16  
**Authority**: Claude Skills Engineering Team  

## Overview

This document defines the mandatory and optional components that constitute a well-formed skill within the claude-skills ecosystem. All skills must adhere to these structural requirements to ensure consistency, maintainability, and quality across the repository.

## Directory Structure

### Mandatory Components

```
skill-name/
├── SKILL.md              # Primary skill documentation (REQUIRED)
├── README.md             # Usage instructions and quick start (REQUIRED)
└── scripts/              # Python implementation scripts (REQUIRED)
    └── *.py              # At least one Python script
```

### Recommended Components

```
skill-name/
├── SKILL.md
├── README.md
├── scripts/
│   └── *.py
├── assets/               # Sample data and input files (RECOMMENDED)
│   ├── samples/
│   ├── examples/
│   └── data/
├── references/           # Reference documentation (RECOMMENDED)
│   ├── api-reference.md
│   ├── specifications.md
│   └── external-links.md
└── expected_outputs/     # Expected results for testing (RECOMMENDED)
    ├── sample_output.json
    ├── example_results.txt
    └── test_cases/
```

### Optional Components

```
skill-name/
├── [mandatory and recommended components]
├── tests/                # Unit tests and validation scripts
├── examples/             # Extended examples and tutorials  
├── docs/                 # Additional documentation
├── config/               # Configuration files
└── templates/            # Template files for code generation
```

## File Requirements

### SKILL.md Requirements

The `SKILL.md` file serves as the primary documentation for the skill and must contain:

#### Mandatory YAML Frontmatter
```yaml
---
Name: skill-name
Tier: [BASIC|STANDARD|POWERFUL]
Category: [Category Name]
Dependencies: [None|List of dependencies]
Author: [Author Name]
Version: [Semantic Version]
Last Updated: [YYYY-MM-DD]
---
```

#### Required Sections
- **Description**: Comprehensive overview of the skill's purpose and capabilities
- **Features**: Detailed list of key features and functionality
- **Usage**: Instructions for using the skill and its components
- **Examples**: Practical usage examples with expected outcomes

#### Recommended Sections
- **Architecture**: Technical architecture and design decisions
- **Installation**: Setup and installation instructions
- **Configuration**: Configuration options and parameters
- **Troubleshooting**: Common issues and solutions
- **Contributing**: Guidelines for contributors
- **Changelog**: Version history and changes

#### Content Requirements by Tier
- **BASIC**: Minimum 100 lines of substantial content
- **STANDARD**: Minimum 200 lines of substantial content  
- **POWERFUL**: Minimum 300 lines of substantial content

### README.md Requirements

The `README.md` file provides quick start instructions and must include:

#### Mandatory Content
- Brief description of the skill
- Quick start instructions
- Basic usage examples
- Link to full SKILL.md documentation

#### Recommended Content
- Installation instructions
- Prerequisites and dependencies
- Command-line usage examples
- Troubleshooting section
- Contributing guidelines

#### Length Requirements
- Minimum 200 characters of substantial content
- Recommended 500+ characters for comprehensive coverage

### Scripts Directory Requirements

The `scripts/` directory contains all Python implementation files:

#### Mandatory Requirements
- At least one Python (.py) file
- All scripts must be executable Python 3.7+
- No external dependencies outside Python standard library
- Proper file naming conventions (lowercase, hyphens for separation)

#### Script Content Requirements
- **Shebang line**: `#!/usr/bin/env python3`
- **Module docstring**: Comprehensive description of script purpose
- **Argparse implementation**: Command-line argument parsing
- **Main guard**: `if __name__ == "__main__":` protection
- **Error handling**: Appropriate exception handling and user feedback
- **Dual output**: Support for both JSON and human-readable output formats

#### Script Size Requirements by Tier
- **BASIC**: 100-300 lines of code per script
- **STANDARD**: 300-500 lines of code per script
- **POWERFUL**: 500-800 lines of code per script

### Assets Directory Structure

The `assets/` directory contains sample data and supporting files:

```
assets/
├── samples/              # Sample input data
│   ├── simple_example.json
│   ├── complex_dataset.csv
│   └── test_configuration.yaml
├── examples/             # Example files demonstrating usage
│   ├── basic_workflow.py
│   ├── advanced_usage.sh
│   └── integration_example.md
└── data/                 # Static data files
    ├── reference_data.json
    ├── lookup_tables.csv
    └── configuration_templates/
```

#### Content Requirements
- At least 2 sample files demonstrating different use cases
- Files should represent realistic usage scenarios
- Include both simple and complex examples where applicable
- Provide diverse file formats (JSON, CSV, YAML, etc.)

### References Directory Structure

The `references/` directory contains detailed reference documentation:

```
references/
├── api-reference.md      # Complete API documentation
├── specifications.md     # Technical specifications and requirements
├── external-links.md     # Links to related resources
├── algorithms.md         # Algorithm descriptions and implementations
└── best-practices.md     # Usage best practices and patterns
```

#### Content Requirements
- Each file should contain substantial technical content (500+ words)
- Include code examples and technical specifications
- Provide external references and links where appropriate
- Maintain consistent documentation format and style

### Expected Outputs Directory Structure

The `expected_outputs/` directory contains reference outputs for testing:

```
expected_outputs/
├── basic_example_output.json
├── complex_scenario_result.txt
├── error_cases/
│   ├── invalid_input_error.json
│   └── timeout_error.txt
└── test_cases/
    ├── unit_test_outputs/
    └── integration_test_results/
```

#### Content Requirements
- Outputs correspond to sample inputs in assets/ directory
- Include both successful and error case examples
- Provide outputs in multiple formats (JSON, text, CSV)
- Ensure outputs are reproducible and verifiable

## Naming Conventions

### Directory Names
- Use lowercase letters only
- Use hyphens (-) to separate words
- Keep names concise but descriptive
- Avoid special characters and spaces

Examples: `data-processor`, `api-client`, `ml-trainer`

### File Names
- Use lowercase letters for Python scripts
- Use hyphens (-) to separate words in script names
- Use underscores (_) only when required by Python conventions
- Use descriptive names that indicate purpose

Examples: `data-processor.py`, `api-client.py`, `quality_scorer.py`

### Script Internal Naming
- Use PascalCase for class names
- Use snake_case for function and variable names
- Use UPPER_CASE for constants
- Use descriptive names that indicate purpose

## Quality Standards

### Documentation Standards
- All documentation must be written in clear, professional English
- Use proper Markdown formatting and structure
- Include code examples with syntax highlighting
- Provide comprehensive coverage of all features
- Maintain consistent terminology throughout

### Code Standards
- Follow PEP 8 Python style guidelines
- Include comprehensive docstrings for all functions and classes
- Implement proper error handling with meaningful error messages
- Use type hints where appropriate
- Maintain reasonable code complexity and readability

### Testing Standards
- Provide sample data that exercises all major functionality
- Include expected outputs for verification
- Cover both successful and error scenarios
- Ensure reproducible results across different environments

## Validation Criteria

Skills are validated against the following criteria:

### Structural Validation
- All mandatory files and directories present
- Proper file naming conventions followed
- Directory structure matches specification
- File permissions and accessibility correct

### Content Validation
- SKILL.md meets minimum length and section requirements
- README.md provides adequate quick start information
- Scripts contain required components (argparse, main guard, etc.)
- Sample data and expected outputs are complete and realistic

### Quality Validation
- Documentation is comprehensive and accurate
- Code follows established style and quality guidelines
- Examples are practical and demonstrate real usage
- Error handling is appropriate and user-friendly

## Compliance Levels

### Full Compliance
- All mandatory components present and complete
- All recommended components present with substantial content
- Exceeds minimum quality thresholds for tier
- Demonstrates best practices throughout

### Partial Compliance
- All mandatory components present
- Most recommended components present
- Meets minimum quality thresholds for tier
- Generally follows established patterns

### Non-Compliance
- Missing mandatory components
- Inadequate content quality or length
- Does not meet minimum tier requirements
- Significant deviations from established standards

## Migration and Updates

### Existing Skills
Skills created before this specification should be updated to comply within:
- **POWERFUL tier**: 30 days
- **STANDARD tier**: 60 days  
- **BASIC tier**: 90 days

### Specification Updates
- Changes to this specification require team consensus
- Breaking changes must provide 90-day migration period
- All changes must be documented with rationale and examples
- Automated validation tools must be updated accordingly

## Tools and Automation

### Validation Tools
- `skill_validator.py` - Validates structure and content compliance
- `script_tester.py` - Tests script functionality and quality  
- `quality_scorer.py` - Provides comprehensive quality assessment

### Integration Points
- Pre-commit hooks for basic validation
- CI/CD pipeline integration for pull request validation
- Automated quality reporting and tracking
- Integration with code review processes

## Examples and Templates

### Minimal BASIC Tier Example
```
basic-skill/
├── SKILL.md              # 100+ lines
├── README.md             # Basic usage instructions
└── scripts/              
    └── main.py           # 100-300 lines with argparse
```

### Complete POWERFUL Tier Example
```
powerful-skill/
├── SKILL.md              # 300+ lines with comprehensive sections
├── README.md             # Detailed usage and setup
├── scripts/              # Multiple sophisticated scripts
│   ├── main_processor.py # 500-800 lines
│   ├── data_analyzer.py  # 500-800 lines
│   └── report_generator.py # 500-800 lines
├── assets/               # Diverse sample data
│   ├── samples/
│   ├── examples/
│   └── data/
├── references/           # Comprehensive documentation
│   ├── api-reference.md
│   ├── specifications.md
│   └── best-practices.md
└── expected_outputs/     # Complete test outputs
    ├── json_outputs/
    ├── text_reports/
    └── error_cases/
```

This specification serves as the authoritative guide for skill structure within the claude-skills ecosystem. Adherence to these standards ensures consistency, quality, and maintainability across all skills in the repository.