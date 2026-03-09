# FAF Format Specification

**Version:** 2.0
**IANA Media Type:** `application/vnd.faf+yaml`
**File Extension:** `.faf`

## Required Fields

```yaml
faf_version: "2.0"        # Format version
project:
  name: string            # Project name
  description: string     # One-line purpose
```

## Recommended Fields

```yaml
project:
  stack: [string]         # Languages/frameworks
  repository: url         # Git remote

context:
  architecture: string    # System overview
  key_files:              # Important paths
    - path: description
  conventions: [string]   # Coding standards

ai_guidance:
  priorities: [string]    # Optimize for
  avoid: [string]         # Anti-patterns
  testing: string         # Test approach
```

## Optional Sections

```yaml
deployment:
  platform: string
  environments: [string]

integrations:
  apis: [string]
  services: [string]
```

## Validation Rules

1. Must be valid YAML
2. `faf_version` required
3. `project.name` required
4. No secrets or credentials
5. Under 500 lines recommended

## File Placement

```
project-root/
├── project.faf     # Core DNA (root)
├── .taf            # Testing context (optional)
└── FAF/            # Extended context (optional)
    └── *.faf
```

## Cross-Platform

Works with: Claude, Cursor, Gemini CLI, WARP, Windsurf, any AI tool reading YAML.
