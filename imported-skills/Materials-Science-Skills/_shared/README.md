# Shared Support Directory

This directory contains shared support content used by multiple materials skills. Keep this directory next to the `materials-*` folders when installing skills manually.

## Directory Structure

```
_shared/
├── core/                          # Core principles and contracts
│   ├── terminology-ledger.md      # Recurring terminology definitions
│   ├── ethics.md                  # Research ethics guidelines
│   ├── evidence-contract.md       # Evidence standards
│   ├── source-basis.md           # Source quality requirements
│   ├── stance.md                  # Writing stance and tone
│   └── claim-strength-ladder.md   # Claim strength classification
├── journal-formats/              # Journal-specific formatting rules
│   ├── cbm.md                    # Construction and Building Materials
│   ├── ccc.md                    # Cement and Concrete Composites
│   ├── jbe.md                    # Journal of Building Engineering
│   └── rmpd.md                   # Resources, Conservation and Recycling
└── paper-production/             # Paper production workflow support
    ├── examples/                 # Example artifacts
    ├── weakness-routing.md       # Weakness routing rules
    ├── paper-gate-report-template.md
    └── weakness-routing-template.csv
```

## Usage

Skills reference shared content using relative paths like `../_shared/core/terminology-ledger.md`. When installing skills manually, always copy the `_shared` directory alongside the skill folders.

## Adding New Shared Content

1. Place the file in the appropriate subdirectory
2. Update any skill manifests that need to reference the new file
3. Run release checks to verify mirror sync
