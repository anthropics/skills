# TOGAF ADM Skill for Claude Code

Expert Enterprise Architect skill specialized in applying TOGAF Architecture Development Method (ADM) for defining, designing, and planning Enterprise Architecture.

## Overview

This Claude Code skill provides comprehensive guidance through all TOGAF ADM phases (Preliminary + A-H + Requirements Management) with practical, business-oriented deliverables optimized for both business and technical stakeholders.

## Features

### Core Capabilities

- **Complete ADM Cycle**: Guides you through all TOGAF phases from Architecture Vision to Implementation Governance
- **Business-Value Driven**: Connects architecture decisions to business objectives with Value Chain and Value Stream analysis
- **ArchiMate Diagrams**: Generate professional architecture diagrams using ArchiMate notation (PlantUML)
- **Capability Mapping**: Create detailed capability maps with maturity gap analysis
- **Context-Specific Patterns**: Pre-built patterns for common scenarios (cloud migration, digital transformation, M&A, etc.)
- **Interactive Approach**: Validates with you at each phase before proceeding

### Visualization Tools

Three powerful diagram generators using ArchiMate (industry standard):

1. **Value Chain Diagrams** - Visualize Porter's Value Chain (primary and support activities)
2. **Value Stream Maps** - Model end-to-end customer journeys with stages, actors, applications, and metrics
3. **Capability Maps** - Hierarchical business capabilities with maturity heat maps

All diagrams available in both ArchiMate/PlantUML (professional) and Mermaid (quick) formats.

### Included Resources

- **Reference Documentation**: Comprehensive guides for all ADM phases, artifacts, and context patterns
- **Templates**: Ready-to-use templates for stakeholders, capabilities, applications, technologies, gap analysis, and migration roadmaps
- **Examples**: JSON examples for all diagram types
- **Scripts**: Python generators for all diagram types

## Installation

### Method 1: Direct Installation from Git (Recommended)

```bash
# Install the plugin
/plugin install https://github.com/xavicrip/togaf-adm-skill
```

### Method 2: Manual Installation

1. Clone the repository:
```bash
cd ~/.claude/plugins
git clone https://github.com/xavicrip/togaf-adm-skill togaf-adm
```

2. Restart Claude Code or run:
```bash
/plugin reload
```

### Verify Installation

```bash
/skills list
```

You should see `togaf-adm` in the available skills list.

## Usage

### Activate the Skill

The skill activates automatically when you request help with:

- "Help me do ADM for [organization/project]"
- "Define enterprise architecture for [context]"
- "Create TOGAF architecture for [scenario]"
- Strategic IT planning
- Digital transformation roadmap
- Cloud migration architecture
- Business-IT alignment

### Example Workflows

#### Example 1: Cloud Migration

```
You: I need to do ADM for migrating our on-premise infrastructure to AWS.

Claude (with togaf-adm): I'll guide you through the TOGAF ADM cycle for your cloud migration...
[Follows ADM phases with specific cloud migration patterns]
```

#### Example 2: Fintech Startup Architecture

```
You: Help me define the enterprise architecture for my fintech startup building a digital lending platform.

Claude (with togaf-adm): I'll help you create a lean, practical architecture using TOGAF ADM...
[Adapts approach for startup context with focus on MVP and compliance]
```

#### Example 3: Generate Capability Map

```
You: Create a capability map for my retail organization with maturity analysis.

Claude (with togaf-adm): Let me gather information about your capabilities...
[Uses scripts/generate_capability_map_archimate.py to create visual diagram]
```

## Project Structure

```
togaf-adm/
├── .claude-plugin/
│   └── plugin.json          # Plugin manifest
├── SKILL.md                 # Main skill instructions
├── README.md                # This file
├── LICENSE                  # MIT License
│
├── assets/
│   └── templates/           # Artifact templates
│       ├── catalog_stakeholders.md
│       ├── catalog_capabilities.md
│       ├── catalog_applications.md
│       ├── catalog_technologies.md
│       ├── matrix_process_application.md
│       ├── gap_analysis.md
│       └── migration_roadmap.md
│
├── scripts/                 # Diagram generators
│   ├── generate_value_chain.py
│   ├── generate_value_chain_archimate.py
│   ├── generate_value_stream.py
│   ├── generate_value_stream_archimate.py
│   ├── generate_capability_map.py
│   └── generate_capability_map_archimate.py
│
├── examples/                # Example JSON inputs
│   ├── README.md
│   ├── value_chain_example.json
│   ├── value_stream_example.json
│   ├── capability_map_example.json
│   └── apple_value_stream_archimate.json
│
└── references/              # Deep dive documentation
    ├── adm_phases.md        # Detailed phase guidance
    ├── artifacts_guide.md   # Artifact structures and examples
    ├── context_patterns.md  # Industry/scenario patterns
    ├── value_concepts.md    # Value Chain, Value Streams, Capability Maps
    └── archimate_guide.md   # ArchiMate modeling guide
```

## TOGAF ADM Phases Covered

- **Preliminary Phase**: Architecture framework setup, principles, stakeholders, governance
- **Phase A**: Architecture Vision - business drivers, AS-IS/TO-BE vision, Value Chain, high-level capabilities
- **Phase B**: Business Architecture - detailed capability mapping, value streams, processes, RACI
- **Phase C**: Information Systems Architecture - data model, applications, integrations
- **Phase D**: Technology Architecture - infrastructure, cloud platforms, technology stack
- **Phase E**: Opportunities and Solutions - gap consolidation, work packages, prioritization
- **Phase F**: Migration Planning - roadmap, timeline, resources, budget
- **Phase G**: Implementation Governance - architecture review board, compliance
- **Phase H**: Architecture Change Management - lifecycle management
- **Requirements Management**: Continuous requirements traceability

## Context-Specific Patterns

Pre-built patterns for common scenarios:

- **Startup Fintech**: MVP, compliance, cloud-native from day 1
- **Cloud Migration**: 6 Rs framework, wave-based migration
- **Digital Transformation**: Customer journey redesign, legacy integration
- **Legacy Modernization**: Strangler fig pattern, incremental approach
- **International Expansion**: Multi-region architecture, data residency
- **M&A Integration**: Portfolio assessment, best-of-breed selection

## Generating Diagrams

### ArchiMate Diagrams (Recommended for Professional Work)

All scripts support interactive mode or JSON input:

```bash
# Interactive mode
python3 scripts/generate_capability_map_archimate.py

# JSON input mode
python3 scripts/generate_capability_map_archimate.py examples/capability_map_example.json
```

Render to PNG/SVG:
```bash
# Install PlantUML first
brew install plantuml  # macOS
# or download from https://plantuml.com/

# Render diagram
plantuml capability_map_archimate.puml
```

Or view online: Upload `.puml` file to https://www.plantuml.com/plantuml/uml/

### Mermaid Diagrams (Quick Visualization)

Use the non-archimate versions for quick Mermaid diagrams that render directly in markdown:

```bash
python3 scripts/generate_capability_map.py
python3 scripts/generate_value_chain.py
python3 scripts/generate_value_stream.py
```

## Requirements

- **Claude Code**: Latest version
- **Python 3.7+**: For diagram generation scripts
- **PlantUML** (optional): For rendering ArchiMate diagrams to PNG/SVG
  - Install: `brew install plantuml` (macOS) or download from https://plantuml.com/

## Core Principles

1. **Practical and Lightweight**: Adapt depth to context, focus on actionable deliverables
2. **Business-Value Driven**: Connect architecture to business objectives
3. **Right Level of Detail**: High-level for strategy, detailed for implementation
4. **Interactive and Iterative**: Validate at each phase, adapt as needed
5. **Visual and Analytical**: Use diagrams and maturity analysis

## Contributing

Contributions are welcome! Please feel free to:

- Report issues or bugs
- Suggest new features or patterns
- Submit pull requests with improvements
- Share your TOGAF ADM success stories

## License

MIT License - see [LICENSE](LICENSE) file for details.

Copyright (c) 2025 Xavier Bustamante

## Support

For issues, questions, or feature requests, please open an issue on the GitHub repository.

## Acknowledgments

- Based on The Open Group's TOGAF framework
- Uses ArchiMate notation (The Open Group standard)
- Inspired by real-world enterprise architecture projects

---

**Author**: Xavier Bustamante
**Keywords**: TOGAF, Enterprise Architecture, ADM, ArchiMate, Capability Mapping, Value Stream, Digital Transformation, Cloud Migration, Business Architecture, Application Architecture, Technology Architecture
