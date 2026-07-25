# Tier Requirements Matrix

**Version**: 2.0.0  
**Last Updated**: 2026-03-27  
**Authority**: Claude Skills Engineering Team  

## Overview

This document provides a comprehensive matrix of requirements for each skill tier within the claude-skills ecosystem. Skills are classified into three tiers based on complexity, functionality, and comprehensiveness: BASIC, STANDARD, and POWERFUL.

**Note**: Security dimension requirements are optional and only apply when `--include-security` flag is used. By default, tier recommendations are based on 4 core dimensions (Documentation, Code Quality, Completeness, Usability) at 25% weight each.

## Tier Classification Philosophy

### BASIC Tier
Entry-level skills that provide fundamental functionality with minimal complexity. Suitable for simple automation tasks, basic data processing, or straightforward utilities.

### STANDARD Tier  
Intermediate skills that offer enhanced functionality with moderate complexity. Suitable for business processes, advanced data manipulation, or multi-step workflows.

### POWERFUL Tier
Advanced skills that provide comprehensive functionality with sophisticated implementation. Suitable for complex systems, enterprise-grade tools, or mission-critical applications.

## Requirements Matrix

| Component | BASIC | STANDARD | POWERFUL |
|-----------|-------|----------|----------|
| **SKILL.md Lines** | ≥100 | ≥200 | ≥300 |
| **Scripts Count** | ≥1 | ≥1 | ≥2 |
| **Script Size (LOC)** | 100-300 | 300-500 | 500-800 |
| **Required Directories** | scripts | scripts, assets, references | scripts, assets, references, expected_outputs |
| **Argparse Implementation** | Basic | Advanced | Complex with subcommands |
| **Output Formats** | Human-readable | JSON + Human-readable | JSON + Human-readable + Custom |
| **Error Handling** | Basic | Comprehensive | Advanced with recovery |
| **Documentation Depth** | Functional | Comprehensive | Expert-level |
| **Examples Provided** | ≥1 | ≥3 | ≥5 |
| **Test Coverage** | Basic validation | Sample data testing | Comprehensive test suite |
| **Security Score** *(opt-in)* | ≥40 | ≥50 | ≥70 |
| **Hardcoded Secrets** *(opt-in)* | None | None | None |
| **Input Validation** *(opt-in)* | Basic | Comprehensive | Advanced with sanitization |

## Detailed Requirements by Tier

### BASIC Tier Requirements

#### Documentation Requirements
- **SKILL.md**: Minimum 100 lines of substantial content
- **Required Sections**: Name, Description, Features, Usage, Examples
- **README.md**: Basic usage instructions (200+ characters)
- **Content Quality**: Clear and functional documentation
- **Examples**: At least 1 practical usage example

#### Code Requirements
- **Scripts**: Minimum 1 Python script (100-300 LOC)
- **Argparse**: Basic command-line argument parsing
- **Main Guard**: `if __name__ == "__main__":` protection
- **Dependencies**: Python standard library only
- **Output**: Human-readable format with clear messaging
- **Error Handling**: Basic exception handling with user-friendly messages

#### Structure Requirements
- **Mandatory Directories**: `scripts/`
- **Recommended Directories**: `assets/`, `references/`
- **File Organization**: Logical file naming and structure
- **Assets**: Optional sample data files

#### Quality Standards
- **Code Style**: Follows basic Python conventions
- **Documentation**: Adequate coverage of functionality
- **Usability**: Clear usage instructions and examples
- **Completeness**: All essential components present

#### Security Requirements *(opt-in with --include-security)*
**Note**: These requirements only apply when the Security dimension is enabled via `--include-security` flag.

- **Security Score**: Minimum 40/100
- **Hardcoded Secrets**: No hardcoded passwords, API keys, or tokens
- **Input Validation**: Basic validation for user inputs
- **Error Handling**: User-friendly error messages without exposing sensitive info
- **Safe Patterns**: Avoid obvious security anti-patterns

### STANDARD Tier Requirements

#### Documentation Requirements
- **SKILL.md**: Minimum 200 lines with comprehensive coverage
- **Required Sections**: All BASIC sections plus Architecture, Installation
- **README.md**: Detailed usage instructions (500+ characters)
- **References**: Technical documentation in `references/` directory
- **Content Quality**: Professional-grade documentation with technical depth
- **Examples**: At least 3 diverse usage examples

#### Code Requirements
- **Scripts**: 1-2 Python scripts (300-500 LOC each)
- **Argparse**: Advanced argument parsing with subcommands and validation
- **Output Formats**: Both JSON and human-readable output support
- **Error Handling**: Comprehensive exception handling with specific error types
- **Code Structure**: Well-organized classes and functions
- **Documentation**: Comprehensive docstrings for all functions

#### Structure Requirements
- **Mandatory Directories**: `scripts/`, `assets/`, `references/`
- **Recommended Directories**: `expected_outputs/`
- **Assets**: Multiple sample files demonstrating different use cases
- **References**: Technical specifications and API documentation
- **Expected Outputs**: Sample results for validation

#### Quality Standards
- **Code Quality**: Advanced Python patterns and best practices
- **Documentation**: Expert-level technical documentation
- **Testing**: Sample data processing with validation
- **Integration**: Consideration for CI/CD and automation use

#### Security Requirements *(opt-in with --include-security)*
**Note**: These requirements only apply when the Security dimension is enabled via `--include-security` flag.

- **Security Score**: Minimum 50/100
- **Hardcoded Secrets**: No hardcoded credentials (zero tolerance)
- **Input Validation**: Comprehensive validation with error messages
- **File Operations**: Safe path handling, no path traversal vulnerabilities
- **Command Execution**: No shell injection risks, safe subprocess usage
- **Security Patterns**: Use of environment variables for secrets

### POWERFUL Tier Requirements

#### Documentation Requirements
- **SKILL.md**: Minimum 300 lines with expert-level comprehensiveness
- **Required Sections**: All STANDARD sections plus Troubleshooting, Contributing, Advanced Usage
- **README.md**: Comprehensive guide with installation and setup (1000+ characters)
- **References**: Multiple technical documents with specifications
- **Content Quality**: Publication-ready documentation with architectural details
- **Examples**: At least 5 examples covering simple to complex scenarios

#### Code Requirements
- **Scripts**: 2-3 Python scripts (500-800 LOC each)
- **Argparse**: Complex argument parsing with multiple modes and configurations
- **Output Formats**: JSON, human-readable, and custom format support
- **Error Handling**: Advanced error handling with recovery mechanisms
- **Code Architecture**: Sophisticated design patterns and modular structure
- **Performance**: Optimized for efficiency and scalability

#### Structure Requirements
- **Mandatory Directories**: `scripts/`, `assets/`, `references/`, `expected_outputs/`
- **Optional Directories**: `tests/`, `examples/`, `docs/`
- **Assets**: Comprehensive sample data covering edge cases
- **References**: Complete technical specification suite
- **Expected Outputs**: Full test result coverage including error cases
- **Testing**: Comprehensive validation and test coverage

#### Quality Standards
- **Enterprise Grade**: Production-ready code with enterprise patterns
- **Documentation**: Comprehensive technical documentation suitable for technical teams
- **Integration**: Full CI/CD integration capabilities
- **Maintainability**: Designed for long-term maintenance and extension

#### Security Requirements *(opt-in with --include-security)*
**Note**: These requirements only apply when the Security dimension is enabled via `--include-security` flag.

- **Security Score**: Minimum 70/100
- **Hardcoded Secrets**: Zero tolerance for hardcoded credentials
- **Input Validation**: Advanced validation with sanitization and type checking
- **File Operations**: All file operations use safe patterns (pathlib, validation)
- **Command Execution**: All subprocess calls use safe patterns (no shell=True)
- **Security Patterns**: Comprehensive security practices including:
  - Environment variables for all secrets
  - Input sanitization for all user inputs
  - Safe deserialization practices
  - Secure error handling without info leakage
- **Security Documentation**: Security considerations documented in code and docs

## Tier Assessment Criteria

### Automatic Tier Classification
Skills are automatically classified based on quantitative metrics:

```python
def classify_tier(skill_metrics):
    if (skill_metrics['skill_md_lines'] >= 300 and
        skill_metrics['script_count'] >= 2 and
        skill_metrics['min_script_size'] >= 500 and
        all_required_dirs_present(['scripts', 'assets', 'references', 'expected_outputs'])):
        return 'POWERFUL'
    
    elif (skill_metrics['skill_md_lines'] >= 200 and
          skill_metrics['script_count'] >= 1 and
          skill_metrics['min_script_size'] >= 300 and
          all_required_dirs_present(['scripts', 'assets', 'references'])):
        return 'STANDARD'
    
    else:
        return 'BASIC'
```

### Manual Tier Override
Manual tier assignment may be considered when:
- Skill provides exceptional value despite not meeting all quantitative requirements
- Skill addresses critical infrastructure or security needs
- Skill demonstrates innovative approaches or cutting-edge techniques
- Skill provides essential integration or compatibility functions

### Tier Promotion Criteria
Skills may be promoted to higher tiers when:
- All quantitative requirements for higher tier are met
- Quality assessment scores exceed tier thresholds
- Community usage and feedback indicate higher value
- Continuous integration and maintenance demonstrate reliability

### Tier Demotion Criteria
Skills may be demoted to lower tiers when:
- Quality degradation below tier standards
- Lack of maintenance or updates
- Compatibility issues or security vulnerabilities
- Community feedback indicates reduced value

## Implementation Guidelines by Tier

### BASIC Tier Implementation
```python
# Example argparse implementation for BASIC tier
parser = argparse.ArgumentParser(description="Basic skill functionality")
parser.add_argument("input", help="Input file or parameter")
parser.add_argument("--output", help="Output destination")
parser.add_argument("--verbose", action="store_true", help="Verbose output")

# Basic error handling
try:
    result = process_input(args.input)
    print(f"Processing completed: {result}")
except FileNotFoundError:
    print("Error: Input file not found")
    sys.exit(1)
except Exception as e:
    print(f"Error: {str(e)}")
    sys.exit(1)
```

### STANDARD Tier Implementation
```python
# Example argparse implementation for STANDARD tier
parser = argparse.ArgumentParser(
    description="Standard skill with advanced functionality",
    formatter_class=argparse.RawDescriptionHelpFormatter,
    epilog="Examples:\n  python script.py input.json --format json\n  python script.py data/ --batch --output results/"
)
parser.add_argument("input", help="Input file or directory")
parser.add_argument("--format", choices=["json", "text"], default="json", help="Output format")
parser.add_argument("--batch", action="store_true", help="Process multiple files")
parser.add_argument("--output", help="Output destination")

# Advanced error handling with specific exception types
try:
    if args.batch:
        results = batch_process(args.input)
    else:
        results = single_process(args.input)
    
    if args.format == "json":
        print(json.dumps(results, indent=2))
    else:
        print_human_readable(results)
        
except FileNotFoundError as e:
    logging.error(f"File not found: {e}")
    sys.exit(1)
except ValueError as e:
    logging.error(f"Invalid input: {e}")
    sys.exit(2)
except Exception as e:
    logging.error(f"Unexpected error: {e}")
    sys.exit(1)
```

### POWERFUL Tier Implementation
```python
# Example argparse implementation for POWERFUL tier
parser = argparse.ArgumentParser(
    description="Powerful skill with comprehensive functionality",
    formatter_class=argparse.RawDescriptionHelpFormatter,
    epilog="""
Examples:
  Basic usage:
    python script.py process input.json --output results/
  
  Advanced batch processing:
    python script.py batch data/ --format json --parallel 4 --filter "*.csv"
  
  Custom configuration:
    python script.py process input.json --config custom.yaml --dry-run
"""
)

subparsers = parser.add_subparsers(dest="command", help="Available commands")

# Process subcommand
process_parser = subparsers.add_parser("process", help="Process single file")
process_parser.add_argument("input", help="Input file path")
process_parser.add_argument("--config", help="Configuration file")
process_parser.add_argument("--dry-run", action="store_true", help="Show what would be done")

# Batch subcommand
batch_parser = subparsers.add_parser("batch", help="Process multiple files")
batch_parser.add_argument("directory", help="Input directory")
batch_parser.add_argument("--parallel", type=int, default=1, help="Number of parallel processes")
batch_parser.add_argument("--filter", help="File filter pattern")

# Comprehensive error handling with recovery
try:
    if args.command == "process":
        result = process_with_recovery(args.input, args.config, args.dry_run)
    elif args.command == "batch":
        result = batch_process_with_monitoring(args.directory, args.parallel, args.filter)
    else:
        parser.print_help()
        sys.exit(1)
    
    # Multiple output format support
    output_formatter = OutputFormatter(args.format)
    output_formatter.write(result, args.output)
    
except KeyboardInterrupt:
    logging.info("Processing interrupted by user")
    sys.exit(130)
except ProcessingError as e:
    logging.error(f"Processing failed: {e}")
    if e.recoverable:
        logging.info("Attempting recovery...")
        # Recovery logic here
    sys.exit(1)
except ValidationError as e:
    logging.error(f"Validation failed: {e}")
    logging.info("Check input format and try again")
    sys.exit(2)
except Exception as e:
    logging.critical(f"Critical error: {e}")
    logging.info("Please report this issue")
    sys.exit(1)
```

## Quality Scoring by Tier

### Scoring Thresholds
- **POWERFUL Tier**: Overall score ≥80, all dimensions ≥75, Security ≥70
- **STANDARD Tier**: Overall score ≥70, 4+ dimensions ≥65, Security ≥50
- **BASIC Tier**: Overall score ≥60, meets minimum requirements, Security ≥40

### Dimension Weights (All Tiers)
- **Documentation**: 20%
- **Code Quality**: 20%  
- **Completeness**: 20%
- **Security**: 20%
- **Usability**: 20%

### Tier-Specific Quality Expectations

#### BASIC Tier Quality Profile
- Documentation: Functional and clear (60+ points expected)
- Code Quality: Clean and maintainable (60+ points expected)
- Completeness: Essential components present (60+ points expected)
- Security: Basic security practices (40+ points expected)
- Usability: Easy to understand and use (60+ points expected)

#### STANDARD Tier Quality Profile
- Documentation: Professional and comprehensive (70+ points expected)
- Code Quality: Advanced patterns and best practices (70+ points expected)
- Completeness: All recommended components (70+ points expected)
- Security: Good security practices, no hardcoded secrets (50+ points expected)
- Usability: Well-designed user experience (70+ points expected)

#### POWERFUL Tier Quality Profile
- Documentation: Expert-level and publication-ready (80+ points expected)
- Code Quality: Enterprise-grade implementation (80+ points expected)
- Completeness: Comprehensive test and validation coverage (80+ points expected)
- Security: Advanced security practices, comprehensive validation (70+ points expected)
- Usability: Exceptional user experience with extensive help (80+ points expected)

## Tier Migration Process

### Promotion Process
1. **Assessment**: Quality scorer evaluates skill against higher tier requirements
2. **Review**: Engineering team reviews assessment and implementation
3. **Testing**: Comprehensive testing against higher tier standards
4. **Approval**: Team consensus on tier promotion
5. **Update**: Skill metadata and documentation updated to reflect new tier

### Demotion Process
1. **Issue Identification**: Quality degradation or standards violation identified
2. **Assessment**: Current quality evaluated against tier requirements
3. **Notice**: Skill maintainer notified of potential demotion
4. **Grace Period**: 30-day period for remediation
5. **Final Review**: Re-assessment after grace period
6. **Action**: Tier adjustment or removal if standards not met

### Tier Change Communication
- All tier changes logged in skill CHANGELOG.md
- Repository-level tier change notifications
- Integration with CI/CD systems for automated handling
- Community notifications for significant changes

## Compliance Monitoring

### Automated Monitoring
- Daily quality assessment scans
- Tier compliance validation in CI/CD
- Automated reporting of tier violations
- Integration with code review processes

### Manual Review Process
- Quarterly tier review cycles
- Community feedback integration
- Expert panel reviews for complex cases
- Appeals process for tier disputes

### Enforcement Actions
- **Warning**: First violation or minor issues
- **Probation**: Repeated violations or moderate issues
- **Demotion**: Serious violations or quality degradation
- **Removal**: Critical violations or abandonment

This tier requirements matrix serves as the definitive guide for skill classification and quality standards within the claude-skills ecosystem. Regular updates ensure alignment with evolving best practices and community needs.