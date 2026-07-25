# Technical Debt Classification Taxonomy

## Overview

This document provides a comprehensive taxonomy for classifying technical debt across different dimensions. Consistent classification is essential for tracking, prioritizing, and managing technical debt effectively across teams and projects.

## Primary Categories

### 1. Code Debt

**Definition**: Issues at the code level that make software harder to understand, modify, or maintain.

**Subcategories**:
- **Structural Issues**
  - `large_function`: Functions exceeding recommended size limits
  - `high_complexity`: High cyclomatic complexity (>10)
  - `deep_nesting`: Excessive indentation levels (>4)
  - `long_parameter_list`: Too many function parameters (>5)
  - `data_clumps`: Related data that should be grouped together
  
- **Naming and Documentation**
  - `poor_naming`: Unclear or misleading variable/function names
  - `missing_docstring`: Functions/classes without documentation
  - `magic_numbers`: Hardcoded numeric values without explanation
  - `commented_code`: Dead code left in comments
  
- **Duplication and Patterns**
  - `duplicate_code`: Identical or similar code blocks
  - `copy_paste_programming`: Evidence of code duplication
  - `inconsistent_patterns`: Mixed coding styles within codebase
  
- **Error Handling**
  - `empty_catch_blocks`: Exception handling without proper action
  - `generic_exceptions`: Catching overly broad exception types
  - `missing_error_handling`: No error handling for failure scenarios

**Severity Indicators**:
- **Critical**: Security vulnerabilities, syntax errors
- **High**: Functions >100 lines, complexity >20
- **Medium**: Functions 50-100 lines, complexity 10-20  
- **Low**: Minor style issues, short functions with minor problems

### 2. Architecture Debt

**Definition**: High-level design decisions that limit system flexibility, scalability, or maintainability.

**Subcategories**:
- **Structural Issues**
  - `monolithic_design`: Components that should be separated
  - `circular_dependencies`: Modules depending on each other cyclically
  - `god_object`: Classes/modules with too many responsibilities
  - `inappropriate_intimacy`: Excessive coupling between modules
  
- **Layer Violations**
  - `abstraction_inversion`: Lower-level modules depending on higher-level ones
  - `leaky_abstractions`: Implementation details exposed through interfaces
  - `broken_hierarchy`: Inheritance relationships that don't make sense
  
- **Scalability Issues**  
  - `performance_bottlenecks`: Known architectural performance limitations
  - `resource_contention`: Shared resources creating bottlenecks
  - `single_point_failure`: Critical components without redundancy

**Impact Assessment**:
- **High Impact**: Affects system scalability, blocks major features
- **Medium Impact**: Makes changes more difficult, affects team productivity
- **Low Impact**: Minor architectural inconsistencies

### 3. Test Debt

**Definition**: Inadequate testing infrastructure, coverage, or quality that increases risk and slows development.

**Subcategories**:
- **Coverage Issues**
  - `low_coverage`: Test coverage below team standards (<80%)
  - `missing_unit_tests`: No tests for critical business logic
  - `missing_integration_tests`: No tests for component interactions
  - `missing_end_to_end_tests`: No full system workflow validation
  
- **Test Quality**
  - `flaky_tests`: Tests that pass/fail inconsistently  
  - `slow_tests`: Test suite taking too long to execute
  - `brittle_tests`: Tests that break with minor code changes
  - `unclear_test_intent`: Tests without clear purpose or documentation
  
- **Infrastructure**
  - `manual_testing_only`: No automated testing processes
  - `missing_test_data`: No proper test data management
  - `environment_dependencies`: Tests requiring specific environments

**Priority Matrix**:
- **Critical Path Coverage**: High priority for business-critical features
- **Regression Risk**: High priority for frequently changed code
- **Development Velocity**: Medium priority for developer productivity
- **Documentation Value**: Low priority for test clarity improvements

### 4. Documentation Debt

**Definition**: Missing, outdated, or poor-quality documentation that hinders understanding and maintenance.

**Subcategories**:
- **API Documentation**
  - `missing_api_docs`: No documentation for public APIs
  - `outdated_api_docs`: Documentation doesn't match implementation
  - `incomplete_examples`: No usage examples for complex APIs
  
- **Code Documentation**
  - `missing_comments`: Complex algorithms without explanation
  - `outdated_comments`: Comments contradicting current implementation
  - `redundant_comments`: Comments that just restate the code
  
- **System Documentation**
  - `missing_architecture_docs`: No high-level system design documentation
  - `missing_deployment_docs`: No deployment or operations guide
  - `missing_onboarding_docs`: No guide for new team members

**Freshness Assessment**:
- **Stale**: Documentation >6 months out of date
- **Outdated**: Documentation 3-6 months out of date
- **Current**: Documentation <3 months out of date

### 5. Dependency Debt

**Definition**: Issues with external libraries, frameworks, and system dependencies.

**Subcategories**:
- **Version Management**
  - `outdated_dependencies`: Libraries with available updates
  - `vulnerable_dependencies`: Dependencies with known security issues
  - `deprecated_dependencies`: Dependencies no longer maintained
  - `version_conflicts`: Incompatible dependency versions
  
- **License and Compliance**
  - `license_violations`: Dependencies with incompatible licenses  
  - `license_unknown`: Dependencies without clear licensing
  - `compliance_risk`: Dependencies creating legal/regulatory risks
  
- **Usage Optimization**
  - `unused_dependencies`: Dependencies included but not used
  - `oversized_dependencies`: Heavy libraries for simple functionality
  - `redundant_dependencies`: Multiple libraries solving same problem

**Risk Assessment**:
- **Security Risk**: Known vulnerabilities, unmaintained dependencies
- **Legal Risk**: License conflicts, compliance issues
- **Technical Risk**: Breaking changes, deprecation notices
- **Maintenance Risk**: Outdated versions, unsupported libraries

### 6. Infrastructure Debt

**Definition**: Operations, deployment, and infrastructure-related technical debt.

**Subcategories**:
- **Deployment and CI/CD**
  - `manual_deployment`: No automated deployment processes
  - `missing_pipeline`: No CI/CD pipeline automation
  - `brittle_deployments`: Deployment process prone to failure
  - `environment_drift`: Inconsistencies between environments
  
- **Monitoring and Observability**
  - `missing_monitoring`: No application/system monitoring
  - `inadequate_logging`: Insufficient logging for troubleshooting
  - `missing_alerting`: No alerts for critical system conditions
  - `poor_observability`: Can't understand system behavior in production
  
- **Configuration Management**
  - `hardcoded_config`: Configuration embedded in code
  - `manual_configuration`: No automated configuration management
  - `secrets_in_code`: Sensitive information stored in code
  - `inconsistent_environments`: Dev/staging/prod differences

**Operational Impact**:
- **Availability**: Affects system uptime and reliability
- **Debuggability**: Affects ability to troubleshoot issues
- **Scalability**: Affects ability to handle load increases
- **Security**: Affects system security posture

## Severity Classification

### Critical (Score: 9-10)
- Security vulnerabilities
- Production-breaking issues
- Legal/compliance violations
- Blocking issues for team productivity

### High (Score: 7-8)  
- Significant technical risk
- Major productivity impact
- Customer-visible quality issues
- Architecture limitations

### Medium (Score: 4-6)
- Moderate productivity impact
- Code quality concerns
- Maintenance difficulties
- Minor security concerns

### Low (Score: 1-3)
- Style and convention issues
- Documentation gaps
- Minor optimizations
- Cosmetic improvements

## Impact Dimensions

### Business Impact
- **Customer Experience**: User-facing quality and performance
- **Revenue**: Direct impact on business metrics
- **Compliance**: Regulatory and legal requirements
- **Market Position**: Competitive advantage considerations

### Technical Impact  
- **Development Velocity**: Speed of feature development
- **Code Quality**: Maintainability and reliability
- **System Reliability**: Uptime and performance
- **Security Posture**: Vulnerability and risk exposure

### Team Impact
- **Developer Productivity**: Individual efficiency
- **Team Morale**: Job satisfaction and engagement  
- **Knowledge Sharing**: Team collaboration and learning
- **Onboarding Speed**: New team member integration

## Effort Estimation Guidelines

### T-Shirt Sizing
- **XS (1-4 hours)**: Simple fixes, documentation updates
- **S (1-2 days)**: Minor refactoring, simple feature additions
- **M (3-5 days)**: Moderate refactoring, component changes
- **L (1-2 weeks)**: Major refactoring, architectural changes
- **XL (3+ weeks)**: System-wide changes, major migrations

### Complexity Factors
- **Technical Complexity**: How difficult is the change technically?
- **Business Risk**: What's the risk if something goes wrong?
- **Testing Requirements**: How much testing is needed?
- **Team Knowledge**: Does the team understand this area well?
- **Dependencies**: How many other systems/teams are involved?

## Usage Guidelines

### When Classifying Debt
1. Start with primary category (code, architecture, test, etc.)
2. Identify specific subcategory for precise tracking
3. Assess severity based on business and technical impact
4. Estimate effort using t-shirt sizing
5. Tag with relevant impact dimensions

### Consistency Rules
- Use consistent terminology across teams
- Document custom categories for domain-specific debt
- Regular reviews to ensure classification accuracy
- Training for team members on taxonomy usage

### Review and Updates
- Quarterly review of taxonomy relevance
- Add new categories as patterns emerge
- Remove unused categories to keep taxonomy lean
- Update severity and impact criteria based on experience

This taxonomy should be adapted to your organization's specific context, technology stack, and business priorities. The key is consistency in application across teams and over time.