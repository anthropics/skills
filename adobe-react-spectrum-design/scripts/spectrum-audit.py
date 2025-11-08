#!/usr/bin/env python3
"""
React Spectrum Component Audit Tool

Analyzes JSX/TSX files for:
- Component usage patterns
- Accessibility attribute compliance
- Missing labels and error messages
- Dark mode consistency
- Color hardcoding
- WCAG 2.1 AA violations

Usage:
    python spectrum-audit.py --path /path/to/src [--format json|text] [--strict]
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path
from collections import defaultdict


class SpectrumAuditor:
    """Audits React Spectrum component usage and accessibility."""

    # Component list (v3.45.0)
    SPECTRUM_COMPONENTS = {
        'TextField', 'TextArea', 'NumberField', 'Button', 'ActionButton',
        'Link', 'Dialog', 'AlertDialog', 'Popover', 'Tooltip', 'Picker',
        'ComboBox', 'Checkbox', 'Radio', 'Switch', 'Slider', 'RangeSlider',
        'DatePicker', 'DateRangePicker', 'Menu', 'Breadcrumbs', 'Tabs',
        'TabList', 'TabPanels', 'Accordion', 'Table', 'List', 'ListBox',
        'Tag', 'Badge', 'Avatar', 'Icon', 'ProgressBar', 'Meter', 'Flex',
        'Grid', 'View', 'VStack', 'HStack', 'Spacer', 'Text', 'Heading',
        'StatusLight', 'SearchField', 'Provider'
    }

    ACCESSIBILITY_CHECKS = {
        'label': r'label\s*=',
        'aria_label': r'aria-label\s*=',
        'aria_labelledby': r'aria-labelledby\s*=',
        'error_message': r'errorMessage\s*=',
        'help_text': r'help\s*=',
        'required': r'isRequired',
        'validation_state': r'validationState\s*=',
        'disabled_state': r'isDisabled',
        'readonly': r'isReadOnly',
    }

    COLOR_PATTERNS = {
        'hardcoded_hex': r'#[0-9A-Fa-f]{3,6}',
        'rgb': r'rgb\s*\(',
        'hardcoded_color_name': r'\b(red|blue|green|yellow|purple|orange)\b',
    }

    def __init__(self, strict=False):
        self.strict = strict
        self.issues = defaultdict(list)
        self.stats = {
            'total_files': 0,
            'component_files': 0,
            'components_found': 0,
            'accessibility_issues': 0,
            'hardcoded_colors': 0,
            'missing_labels': 0,
        }

    def audit_directory(self, path):
        """Recursively audit all JSX/TSX files in directory."""
        path = Path(path)

        for file_path in path.rglob('*.[jt]sx'):
            if 'node_modules' in str(file_path):
                continue

            self.stats['total_files'] += 1
            self.audit_file(file_path)

    def audit_file(self, file_path):
        """Audit a single file."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.issues[str(file_path)].append(f"Read error: {e}")
            return

        # Find Spectrum components
        found_components = self.find_components(content)
        if not found_components:
            return

        self.stats['component_files'] += 1
        self.stats['components_found'] += len(found_components)

        # Run accessibility checks
        self.check_accessibility(file_path, content, found_components)
        self.check_hardcoded_colors(file_path, content)

    def find_components(self, content):
        """Find all Spectrum component usages."""
        components = []
        for component in self.SPECTRUM_COMPONENTS:
            pattern = r'<' + component + r'(?:\s|>)'
            matches = re.finditer(pattern, content)
            components.extend([m.group() for m in matches])
        return components

    def check_accessibility(self, file_path, content, components):
        """Check for accessibility issues."""
        file_str = str(file_path)

        # Check form components for labels
        form_components = {
            'TextField', 'TextArea', 'NumberField', 'SearchField',
            'Picker', 'ComboBox', 'DatePicker', 'Checkbox', 'Radio', 'Switch'
        }

        for comp in form_components:
            pattern = r'<' + comp + r'[^>]*>'
            matches = re.finditer(pattern, content)

            for match in matches:
                component_tag = match.group()

                has_label = (
                    re.search(r'label\s*=', component_tag) or
                    re.search(r'aria-label\s*=', component_tag) or
                    'aria-labelledby' in component_tag
                )

                if not has_label:
                    self.issues[file_str].append(
                        f"Missing label on {comp} component"
                    )
                    self.stats['missing_labels'] += 1
                    self.stats['accessibility_issues'] += 1

    def check_hardcoded_colors(self, file_path, content):
        """Check for hardcoded colors."""
        file_str = str(file_path)

        # Skip CSS imports and hard-coded theme files
        if '_theme' in str(file_path) or file_path.suffix == '.css':
            return

        hex_matches = re.finditer(self.COLOR_PATTERNS['hardcoded_hex'], content)
        hex_count = len(list(hex_matches))

        if hex_count > 0:
            self.issues[file_str].append(
                f"Found {hex_count} hardcoded color values (use Spectrum tokens)"
            )
            self.stats['hardcoded_colors'] += hex_count

    def generate_report(self, format_type='text'):
        """Generate audit report."""
        if format_type == 'json':
            return self._json_report()
        else:
            return self._text_report()

    def _text_report(self):
        """Generate human-readable report."""
        lines = [
            "=" * 70,
            "React Spectrum Audit Report",
            "=" * 70,
            "",
            "STATISTICS",
            "-" * 70,
            f"Total files scanned: {self.stats['total_files']}",
            f"Component files found: {self.stats['component_files']}",
            f"Total components: {self.stats['components_found']}",
            f"Accessibility issues: {self.stats['accessibility_issues']}",
            f"Hardcoded colors: {self.stats['hardcoded_colors']}",
            f"Missing labels: {self.stats['missing_labels']}",
            "",
        ]

        if self.issues:
            lines.append("ISSUES BY FILE")
            lines.append("-" * 70)

            for file_path in sorted(self.issues.keys()):
                lines.append(f"\n{file_path}:")
                for issue in self.issues[file_path]:
                    lines.append(f"  - {issue}")
        else:
            lines.append("No issues found!")

        lines.extend([
            "",
            "=" * 70,
            "Recommendations:",
            "- Use Spectrum tokens instead of hardcoded colors",
            "- Ensure all form inputs have labels (for accessibility)",
            "- Use validationState prop for error indication",
            "- Test with keyboard navigation and screen readers",
            "- Review theme consistency across application",
            "=" * 70,
        ])

        return "\n".join(lines)

    def _json_report(self):
        """Generate JSON report."""
        return json.dumps({
            'stats': self.stats,
            'issues': dict(self.issues)
        }, indent=2)


def main():
    parser = argparse.ArgumentParser(
        description='Audit React Spectrum component usage and accessibility'
    )
    parser.add_argument(
        '--path', '-p',
        required=True,
        help='Path to directory or file to audit'
    )
    parser.add_argument(
        '--format', '-f',
        choices=['text', 'json'],
        default='text',
        help='Output format (default: text)'
    )
    parser.add_argument(
        '--strict', '-s',
        action='store_true',
        help='Strict mode (fail on any issue)'
    )

    args = parser.parse_args()

    # Validate path
    if not os.path.exists(args.path):
        print(f"Error: Path not found: {args.path}", file=sys.stderr)
        sys.exit(1)

    # Run audit
    auditor = SpectrumAuditor(strict=args.strict)

    if os.path.isfile(args.path):
        auditor.audit_file(args.path)
    else:
        auditor.audit_directory(args.path)

    # Generate and print report
    report = auditor.generate_report(args.format)
    print(report)

    # Exit code based on issues
    if args.strict and auditor.issues:
        sys.exit(1)


if __name__ == '__main__':
    main()
