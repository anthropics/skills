# Versioning and Support Policy

## Overview

The Strands SDK is an open-source project that follows semantic versioning to provide predictable, stable releases while enabling rapid innovation. This document explains the versioning approach, experimental features, and deprecation policies that guide SDK development.

## Semantic Versioning

The SDK adheres to [Semantic Versioning 2.0.0](https://semver.org/) with the following version format: `MAJOR.MINOR.PATCH`

* **Major (X.0.0)**: Breaking changes, feature removals, or API changes that affect existing code
* **Minor (1.Y.0)**: New features, deprecation warnings, and backward-compatible additions
* **Patch (1.1.Z)**: Bug fixes, security patches, and documentation updates

### Stability Guarantee

When upgrading to a new minor or patch version, existing code should continue to work without modification. Breaking changes are reserved for major version releases and are always accompanied by clear migration guides.

## Exceptions to Strict Versioning

### Rapidly Evolving AI Standards

The AI ecosystem is evolving rapidly with new standards and protocols emerging regularly. To provide cutting-edge capabilities, the SDK integrates with evolving standards such as:

* OpenTelemetry GenAI Semantic Conventions
* Model Context Protocol (MCP)
* Agent-to-Agent (A2A) protocols

**Best Practice**: When using features that depend on rapidly evolving standards, pinning to a specific minor version in production applications ensures stability.

### Opt-In Breaking Changes

Small breaking changes that follow the "pay for play" principle may be included in minor versions. This principle states: programs can call new APIs to access new features, but programs that choose not to do so are unaffected — old code continues to work as it did before.

**When This Applies:**

* The breaking change is gated behind new functionality that must be explicitly adopted
* Existing code paths remain completely unaffected
* The change is only encountered when actively using the new feature
* The change is obvious and directly tied to newly added functionality

**Example**: Adding optional fields to a configuration object that only affects users who adopt a new tool or feature.

See also: [Raymond Chen on "pay for play" in API design](https://devblogs.microsoft.com/oldnewthing/20260127-00/?p=112018)

## Experimental Features

### What Are Experimental Features?

Experimental features are new capabilities released in the `strands.experimental` module (Python) or under experimental namespaces (TypeScript). These features enable:

* Testing innovative ideas with real-world feedback
* Rapid iteration based on community input
* Feature design validation before committing to long-term support

### Using Experimental Features

!!! warning "Production Use"
    Experimental features are designed for testing, prototyping, and providing feedback. They are **not covered by semantic versioning guarantees** and may change between minor versions.
    
    If you choose to use experimental features in production:
    
    * Pin to a specific minor version (e.g., `strands-agents==1.5.0`)
    * Test thoroughly before upgrading
    * Monitor release notes for changes

### Graduation Process

Experimental features graduate to the main SDK when they meet stability criteria:

* API is stable with no breaking changes expected
* Comprehensive test coverage and documentation
* Validated by real-world use cases
* Positive community feedback

**Timeline:**

* **Version X.Y-1**: Feature exists only in experimental module
* **Version X.Y**: Feature graduates to main SDK; experimental version deprecated with migration guide
* **Version X.Y+1**: Experimental version removed

## Deprecation Policy

Features are deprecated responsibly to provide adequate time for migration to newer alternatives.

### Process

1. **Introduce Alternative**: A new, improved way to accomplish the same goal is released
2. **Deprecate Old Way**: The old feature emits deprecation warnings with clear migration guidance
3. **Remove in Major Version**: The deprecated feature is removed in the next major version

### Timeline Example

* **Version 1.Y**: New feature introduced; old feature marked deprecated with warnings
* **Version 1.Y+1**: (Optional) Enhanced warnings with migration examples
* **Version 2.0**: Deprecated feature removed

### Deprecation Warnings

=== "Python"

    ```python
    import warnings
    
    @warnings.deprecated(
        "deprecated_function() is deprecated and will be removed in v2.0.0. "
        "Use new_function() instead. See: https://strandsagents.com/...",
        category=DeprecationWarning,
        stacklevel=2
    )
    def deprecated_function():
        pass
    ```

=== "TypeScript"

    ```typescript
    /**
     * @deprecated deprecated_function() is deprecated and will be removed in v2.0.0. 
     * Use new_function() instead. See: https://strandsagents.com/...
     */
    export const deprecated_function = () => {}
    ```

## Guiding Principles

### Predictability

* Clear version transitions between deprecation and removal
* Features are never removed in minor or patch versions
* Migration tools and clear error messages when feasible

### Transparency

* Deprecation timelines specified in all warnings
* Comprehensive migration documentation
* Regular communication through release notes and changelogs

### Stability

* Backward compatibility within major versions
* Advance notice for breaking changes
* Multiple minor versions between deprecation and removal

### Community-Driven

* Open discussions for significant changes
* Feedback incorporated into feature design
* Collaborative approach to SDK evolution

## Release Cadence

* **Patch releases**: As needed for critical bug fixes and security patches
* **Minor releases**: Regular cadence for new features and deprecation warnings
* **Major releases**: With advance notice and comprehensive migration guides

## Staying Informed

Stay up-to-date with SDK changes through these channels:

* **Release Notes**: Check GitHub Releases for detailed changelogs
    * [Python SDK](https://github.com/strands-agents/sdk-python/releases)
    * [TypeScript SDK](https://github.com/strands-agents/sdk-typescript/releases)
    * [Evals SDK](https://github.com/strands-agents/evals/releases)
* **Deprecation Warnings**: Monitor warnings in application logs
* **GitHub Discussions**: Join conversations about proposed changes
    * [Python Discussions](https://github.com/strands-agents/sdk-python/discussions)
    * [TypeScript Discussions](https://github.com/strands-agents/sdk-typescript/discussions)
    * [Evals Discussions](https://github.com/strands-agents/evals/discussions)
* **Documentation**: Migration guides are published with each major release

## Get Involved

The Strands SDK is an open-source project that welcomes community contributions. Here's how to participate:

* **Ask Questions**: Open a GitHub Discussion in the relevant repository
* **Report Issues**: Submit bug reports or feature requests via GitHub Issues
    * [Python Issues](https://github.com/strands-agents/sdk-python/issues)
    * [TypeScript Issues](https://github.com/strands-agents/sdk-typescript/issues)
    * [Evals Issues](https://github.com/strands-agents/evals/issues)
* **Contribute Code**: Review the [Contributing Guide](https://github.com/strands-agents/sdk-python/blob/main/CONTRIBUTING.md) to get started
* **Share Feedback**: Your input on versioning and support policies helps shape the SDK's future
