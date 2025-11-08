#!/usr/bin/env python3
"""
Generate TypeScript types from Tauri Rust command definitions.

This script parses Rust source files looking for Tauri #[command] attributes
and generates TypeScript interfaces for type-safe IPC invocations.

Usage:
    python generate-tauri-command-types.py <rust_src_dir> <output_ts_file>

Example:
    python generate-tauri-command-types.py src/commands commands.ts
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional


class RustTypeParser:
    """Parse Rust types and convert to TypeScript equivalents."""

    RUST_TO_TS_MAPPING = {
        'String': 'string',
        'str': 'string',
        'i32': 'number',
        'i64': 'number',
        'u32': 'number',
        'u64': 'number',
        'f32': 'number',
        'f64': 'number',
        'bool': 'boolean',
        '()': 'void',
    }

    @classmethod
    def convert_type(cls, rust_type: str) -> str:
        """Convert Rust type to TypeScript type."""
        rust_type = rust_type.strip()

        # Handle Option<T>
        if rust_type.startswith('Option<'):
            inner = cls.convert_type(rust_type[7:-1])
            return f'{inner} | null'

        # Handle Vec<T>
        if rust_type.startswith('Vec<'):
            inner = cls.convert_type(rust_type[4:-1])
            return f'{inner}[]'

        # Handle Result<T, E> - assume E is error and use T only
        if rust_type.startswith('Result<'):
            inner = rust_type[7:-1]
            parts = inner.split(',', 1)
            return cls.convert_type(parts[0].strip())

        # Direct mapping
        if rust_type in cls.RUST_TO_TS_MAPPING:
            return cls.RUST_TO_TS_MAPPING[rust_type]

        # Custom types - capitalize for interface names
        return rust_type


class CommandExtractor:
    """Extract Tauri command definitions from Rust code."""

    def __init__(self):
        self.commands: Dict[str, Dict] = {}

    def extract_from_file(self, filepath: Path) -> None:
        """Extract command definitions from a Rust file."""
        try:
            content = filepath.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError):
            return

        # Find all #[command] decorated functions
        command_pattern = r'#\[command\]\s+(?:pub\s+)?async\s+fn\s+(\w+)\s*\((.*?)\)\s*->\s*([\w<>,\s]+)'
        matches = re.finditer(command_pattern, content, re.DOTALL)

        for match in matches:
            cmd_name = match.group(1)
            params_str = match.group(2).strip()
            return_type = match.group(3).strip()

            # Parse parameters
            params = self._parse_params(params_str)

            self.commands[cmd_name] = {
                'params': params,
                'result': RustTypeParser.convert_type(return_type),
            }

    def _parse_params(self, params_str: str) -> Dict[str, str]:
        """Parse function parameters from Rust code."""
        params = {}

        if not params_str or params_str == '_' or params_str.startswith('_'):
            return params

        # Remove line breaks and extra spaces
        params_str = re.sub(r'\s+', ' ', params_str)

        # Split by comma, but respect nested brackets
        param_parts = []
        current = ''
        bracket_depth = 0

        for char in params_str:
            if char in '<({[':
                bracket_depth += 1
            elif char in '>)]}':
                bracket_depth -= 1
            elif char == ',' and bracket_depth == 0:
                param_parts.append(current.strip())
                current = ''
                continue

            current += char

        if current.strip():
            param_parts.append(current.strip())

        # Parse each parameter
        for part in param_parts:
            if ':' in part:
                name, type_str = part.split(':', 1)
                name = name.strip()
                # Skip 'state' and other special parameters
                if not name.startswith('_'):
                    params[name] = RustTypeParser.convert_type(type_str)

        return params

    def extract_from_directory(self, directory: Path) -> None:
        """Recursively extract commands from all Rust files in a directory."""
        if not directory.exists():
            print(f'Error: Directory not found: {directory}', file=sys.stderr)
            return

        for rust_file in directory.rglob('*.rs'):
            self.extract_from_file(rust_file)

    def generate_typescript(self) -> str:
        """Generate TypeScript interface definitions."""
        if not self.commands:
            return '// No Tauri commands found\n'

        lines = [
            '/**',
            ' * Auto-generated TypeScript types for Tauri commands.',
            ' * Generated from Rust command definitions.',
            ' * Do not edit manually - regenerate using generate-tauri-command-types.py',
            ' */',
            '',
            'import { invoke as tauriInvoke } from "@tauri-apps/api/core";',
            '',
            '/**',
            ' * Tauri command type definitions',
            ' */',
            'export interface TauriCommands {',
        ]

        for cmd_name in sorted(self.commands.keys()):
            cmd_info = self.commands[cmd_name]
            params = cmd_info['params']
            result = cmd_info['result']

            # Build params interface
            params_interface = self._build_params_interface(params)

            lines.append(f'  {cmd_name}: {{')
            lines.append(f'    params: {params_interface};')
            lines.append(f'    result: {result};')
            lines.append('  };')

        lines.append('}')
        lines.append('')

        # Add type-safe invoke function
        lines.extend([
            '/**',
            ' * Type-safe Tauri invoke function',
            ' */',
            'export async function invoke<K extends keyof TauriCommands>(',
            '  command: K,',
            '  payload?: TauriCommands[K]["params"]',
            '): Promise<TauriCommands[K]["result"]> {',
            '  return tauriInvoke(command, payload);',
            '}',
            '',
            '/**',
            ' * Helper function to check if invoke succeeded',
            ' */',
            'export function isSuccess<T>(result: T | Error): result is T {',
            '  return !(result instanceof Error);',
            '}',
            '',
        ])

        return '\n'.join(lines)

    def _build_params_interface(self, params: Dict[str, str]) -> str:
        """Build TypeScript interface for parameters."""
        if not params:
            return 'void'

        interface_parts = []
        for name, type_str in sorted(params.items()):
            interface_parts.append(f'{name}: {type_str}')

        return '{ ' + '; '.join(interface_parts) + '; }'


def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print('Usage: generate-tauri-command-types.py <rust_src_dir> [output_file]')
        print()
        print('Arguments:')
        print('  rust_src_dir   Directory containing Rust command definitions')
        print('  output_file    (Optional) Output TypeScript file (default: tauri-commands.ts)')
        sys.exit(1)

    src_dir = Path(sys.argv[1])
    output_file = Path(sys.argv[2]) if len(sys.argv) > 2 else Path('tauri-commands.ts')

    # Extract commands
    extractor = CommandExtractor()
    extractor.extract_from_directory(src_dir)

    # Generate TypeScript
    ts_code = extractor.generate_typescript()

    # Write output
    output_file.write_text(ts_code)
    print(f'Generated {len(extractor.commands)} command types to {output_file}')

    # Print summary
    if extractor.commands:
        print('\nCommands:')
        for cmd_name in sorted(extractor.commands.keys()):
            print(f'  - {cmd_name}')


if __name__ == '__main__':
    main()
