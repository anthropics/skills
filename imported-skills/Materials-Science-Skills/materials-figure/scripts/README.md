# materials-figure/scripts

This directory contains scripts for the `materials-figure` skill.

## Archive Reference Scripts

The following scripts are retained as **archival references** required by the `figure_hard_workflow` release checks:

- `compose_multipanel_figure.py` - Reference implementation for multi-panel figure composition
- `audit_figure_package.py` - Reference implementation for figure package auditing

**Important**: These scripts are NOT part of the active automation pipeline. They are kept for historical reference and to satisfy release validation requirements. For current figure generation and validation workflows, refer to:

- `static/core/workflow.md` - Contract-driven workflow documentation
- `static/core/figure-contract.md` - Figure contract specifications
- `static/core/contract.md` - General contract validation

## Active Scripts

- `check_storyboard.py` - Validates figure storyboard structure
- `validate_materials_claims.py` - Validates materials-related claims in documentation
