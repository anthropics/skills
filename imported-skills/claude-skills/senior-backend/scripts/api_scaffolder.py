#!/usr/bin/env python3
"""
API Scaffolder

Generates Express.js route handlers, validation middleware, and TypeScript types
from OpenAPI specifications (YAML/JSON).

Usage:
    python api_scaffolder.py openapi.yaml --output src/routes/
    python api_scaffolder.py openapi.json --framework fastify --output src/
    python api_scaffolder.py spec.yaml --types-only --output src/types/
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Optional, Any
from datetime import datetime


def load_yaml_as_json(content: str) -> Dict:
    """Parse YAML content without PyYAML dependency (basic subset)."""
    lines = content.split('\n')
    result = {}
    stack = [(result, -1)]
    current_key = None
    in_array = False
    array_indent = -1

    for line in lines:
        stripped = line.lstrip()
        if not stripped or stripped.startswith('#'):
            continue

        indent = len(line) - len(stripped)

        # Pop stack until we find the right level
        while len(stack) > 1 and stack[-1][1] >= indent:
            stack.pop()

        current_obj = stack[-1][0]

        if stripped.startswith('- '):
            # Array item
            value = stripped[2:].strip()
            if isinstance(current_obj, list):
                if ':' in value:
                    # Object in array
                    key, val = value.split(':', 1)
                    new_obj = {key.strip(): val.strip().strip('"').strip("'")}
                    current_obj.append(new_obj)
                    stack.append((new_obj, indent))
                else:
                    current_obj.append(value.strip('"').strip("'"))
        elif ':' in stripped:
            key, value = stripped.split(':', 1)
            key = key.strip()
            value = value.strip()

            if value == '':
                # Check next line for array or object
                new_obj = {}
                current_obj[key] = new_obj
                stack.append((new_obj, indent))
            elif value.startswith('[') and value.endswith(']'):
                # Inline array
                items = value[1:-1].split(',')
                current_obj[key] = [i.strip().strip('"').strip("'") for i in items if i.strip()]
            else:
                # Simple value
                value = value.strip('"').strip("'")
                if value.lower() == 'true':
                    value = True
                elif value.lower() == 'false':
                    value = False
                elif value.isdigit():
                    value = int(value)
                current_obj[key] = value

    return result


def load_spec(spec_path: Path) -> Dict:
    """Load OpenAPI spec from YAML or JSON file."""
    content = spec_path.read_text()

    if spec_path.suffix in ['.yaml', '.yml']:
        try:
            import yaml
            return yaml.safe_load(content)
        except ImportError:
            # Fallback to basic YAML parser
            return load_yaml_as_json(content)
    else:
        return json.loads(content)


def openapi_type_to_ts(schema: Dict) -> str:
    """Convert OpenAPI schema type to TypeScript type."""
    if not schema:
        return 'unknown'

    if '$ref' in schema:
        ref = schema['$ref']
        return ref.split('/')[-1]

    type_map = {
        'string': 'string',
        'integer': 'number',
        'number': 'number',
        'boolean': 'boolean',
        'object': 'Record<string, unknown>',
        'array': 'unknown[]',
    }

    schema_type = schema.get('type', 'unknown')

    if schema_type == 'array':
        items = schema.get('items', {})
        item_type = openapi_type_to_ts(items)
        return f'{item_type}[]'

    if schema_type == 'object':
        properties = schema.get('properties', {})
        if properties:
            props = []
            required = schema.get('required', [])
            for name, prop in properties.items():
                ts_type = openapi_type_to_ts(prop)
                optional = '?' if name not in required else ''
                props.append(f'  {name}{optional}: {ts_type};')
            return '{\n' + '\n'.join(props) + '\n}'
        return 'Record<string, unknown>'

    if 'enum' in schema:
        values = ' | '.join(f"'{v}'" for v in schema['enum'])
        return values

    return type_map.get(schema_type, 'unknown')


def generate_zod_schema(schema: Dict, name: str) -> str:
    """Generate Zod validation schema from OpenAPI schema."""
    if not schema:
        return f'export const {name}Schema = z.unknown();'

    def schema_to_zod(s: Dict) -> str:
        if '$ref' in s:
            ref_name = s['$ref'].split('/')[-1]
            return f'{ref_name}Schema'

        s_type = s.get('type', 'unknown')

        if s_type == 'string':
            zod = 'z.string()'
            if 'minLength' in s:
                zod += f'.min({s["minLength"]})'
            if 'maxLength' in s:
                zod += f'.max({s["maxLength"]})'
            if 'pattern' in s:
                zod += f'.regex(/{s["pattern"]}/)'
            if s.get('format') == 'email':
                zod += '.email()'
            if s.get('format') == 'uuid':
                zod += '.uuid()'
            if 'enum' in s:
                values = ', '.join(f"'{v}'" for v in s['enum'])
                return f'z.enum([{values}])'
            return zod

        if s_type == 'integer':
            zod = 'z.number().int()'
            if 'minimum' in s:
                zod += f'.min({s["minimum"]})'
            if 'maximum' in s:
                zod += f'.max({s["maximum"]})'
            return zod

        if s_type == 'number':
            zod = 'z.number()'
            if 'minimum' in s:
                zod += f'.min({s["minimum"]})'
            if 'maximum' in s:
                zod += f'.max({s["maximum"]})'
            return zod

        if s_type == 'boolean':
            return 'z.boolean()'

        if s_type == 'array':
            items_zod = schema_to_zod(s.get('items', {}))
            return f'z.array({items_zod})'

        if s_type == 'object':
            properties = s.get('properties', {})
            required = s.get('required', [])
            if not properties:
                return 'z.record(z.unknown())'

            props = []
            for prop_name, prop_schema in properties.items():
                prop_zod = schema_to_zod(prop_schema)
                if prop_name not in required:
                    prop_zod += '.optional()'
                props.append(f'  {prop_name}: {prop_zod},')

            return 'z.object({\n' + '\n'.join(props) + '\n})'

        return 'z.unknown()'

    return f'export const {name}Schema = {schema_to_zod(schema)};'


def to_camel_case(s: str) -> str:
    """Convert string to camelCase."""
    s = re.sub(r'[^a-zA-Z0-9]', ' ', s)
    words = s.split()
    if not words:
        return s
    return words[0].lower() + ''.join(w.capitalize() for w in words[1:])


def to_pascal_case(s: str) -> str:
    """Convert string to PascalCase."""
    s = re.sub(r'[^a-zA-Z0-9]', ' ', s)
    return ''.join(w.capitalize() for w in s.split())


def extract_path_params(path: str) -> List[str]:
    """Extract path parameters from OpenAPI path."""
    return re.findall(r'\{(\w+)\}', path)


def openapi_path_to_express(path: str) -> str:
    """Convert OpenAPI path to Express path format."""
    return re.sub(r'\{(\w+)\}', r':\1', path)


class APIScaffolder:
    """Generate Express.js routes from OpenAPI specification."""

    SUPPORTED_FRAMEWORKS = ['express', 'fastify', 'koa']

    def __init__(self, spec_path: str, output_dir: str, framework: str = 'express',
                 types_only: bool = False, verbose: bool = False):
        self.spec_path = Path(spec_path)
        self.output_dir = Path(output_dir)
        self.framework = framework
        self.types_only = types_only
        self.verbose = verbose
        self.spec: Dict = {}
        self.generated_files: List[str] = []

    def run(self) -> Dict:
        """Execute scaffolding process."""
        print(f"API Scaffolder - {self.framework.capitalize()}")
        print(f"Spec: {self.spec_path}")
        print(f"Output: {self.output_dir}")
        print("-" * 50)

        self.validate()
        self.load_spec()
        self.ensure_output_dir()

        if self.types_only:
            self.generate_types()
        else:
            self.generate_types()
            self.generate_validators()
            self.generate_routes()
            self.generate_index()

        return {
            'status': 'success',
            'spec': str(self.spec_path),
            'output': str(self.output_dir),
            'framework': self.framework,
            'generated_files': self.generated_files,
            'routes_count': len(self.get_operations()),
            'types_count': len(self.get_schemas()),
        }

    def validate(self):
        """Validate inputs."""
        if not self.spec_path.exists():
            raise FileNotFoundError(f"Spec file not found: {self.spec_path}")

        if self.framework not in self.SUPPORTED_FRAMEWORKS:
            raise ValueError(f"Unsupported framework: {self.framework}")

    def load_spec(self):
        """Load and parse OpenAPI specification."""
        self.spec = load_spec(self.spec_path)

        if self.verbose:
            title = self.spec.get('info', {}).get('title', 'Unknown')
            version = self.spec.get('info', {}).get('version', '0.0.0')
            print(f"Loaded: {title} v{version}")

    def ensure_output_dir(self):
        """Create output directory if needed."""
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def get_schemas(self) -> Dict:
        """Get component schemas from spec."""
        return self.spec.get('components', {}).get('schemas', {})

    def get_operations(self) -> List[Dict]:
        """Extract all operations from spec."""
        operations = []
        paths = self.spec.get('paths', {})

        for path, methods in paths.items():
            if not isinstance(methods, dict):
                continue

            for method, details in methods.items():
                if method.lower() not in ['get', 'post', 'put', 'patch', 'delete']:
                    continue

                if not isinstance(details, dict):
                    continue

                op_id = details.get('operationId', f'{method}_{path}'.replace('/', '_'))

                operations.append({
                    'path': path,
                    'method': method.lower(),
                    'operation_id': op_id,
                    'summary': details.get('summary', ''),
                    'parameters': details.get('parameters', []),
                    'request_body': details.get('requestBody', {}),
                    'responses': details.get('responses', {}),
                    'tags': details.get('tags', ['default']),
                })

        return operations

    def generate_types(self):
        """Generate TypeScript type definitions."""
        schemas = self.get_schemas()

        lines = [
            '// Auto-generated TypeScript types',
            f'// Generated from: {self.spec_path.name}',
            f'// Date: {datetime.now().isoformat()}',
            '',
        ]

        for name, schema in schemas.items():
            ts_type = openapi_type_to_ts(schema)
            if ts_type.startswith('{'):
                lines.append(f'export interface {name} {ts_type}')
            else:
                lines.append(f'export type {name} = {ts_type};')
            lines.append('')

        # Generate request/response types from operations
        for op in self.get_operations():
            op_name = to_pascal_case(op['operation_id'])

            # Request body type
            req_body = op.get('request_body', {})
            if req_body:
                content = req_body.get('content', {})
                json_content = content.get('application/json', {})
                schema = json_content.get('schema', {})
                if schema and '$ref' not in schema:
                    ts_type = openapi_type_to_ts(schema)
                    lines.append(f'export interface {op_name}Request {ts_type}')
                    lines.append('')

            # Response type (200 response)
            responses = op.get('responses', {})
            success_resp = responses.get('200', responses.get('201', {}))
            if success_resp:
                content = success_resp.get('content', {})
                json_content = content.get('application/json', {})
                schema = json_content.get('schema', {})
                if schema and '$ref' not in schema:
                    ts_type = openapi_type_to_ts(schema)
                    lines.append(f'export interface {op_name}Response {ts_type}')
                    lines.append('')

        types_file = self.output_dir / 'types.ts'
        types_file.write_text('\n'.join(lines))
        self.generated_files.append(str(types_file))
        print(f"  Generated: {types_file}")

    def generate_validators(self):
        """Generate Zod validation schemas."""
        schemas = self.get_schemas()

        lines = [
            "import { z } from 'zod';",
            '',
            '// Auto-generated Zod validation schemas',
            f'// Generated from: {self.spec_path.name}',
            '',
        ]

        for name, schema in schemas.items():
            zod_schema = generate_zod_schema(schema, name)
            lines.append(zod_schema)
            lines.append(f'export type {name} = z.infer<typeof {name}Schema>;')
            lines.append('')

        # Generate validation middleware
        lines.extend([
            '// Validation middleware factory',
            'import { Request, Response, NextFunction } from "express";',
            '',
            'export function validate<T>(schema: z.ZodSchema<T>) {',
            '  return (req: Request, res: Response, next: NextFunction) => {',
            '    const result = schema.safeParse(req.body);',
            '    if (!result.success) {',
            '      return res.status(400).json({',
            '        error: {',
            '          code: "VALIDATION_ERROR",',
            '          message: "Request validation failed",',
            '          details: result.error.errors.map(e => ({',
            '            field: e.path.join("."),',
            '            message: e.message,',
            '          })),',
            '        },',
            '      });',
            '    }',
            '    req.body = result.data;',
            '    next();',
            '  };',
            '}',
        ])

        validators_file = self.output_dir / 'validators.ts'
        validators_file.write_text('\n'.join(lines))
        self.generated_files.append(str(validators_file))
        print(f"  Generated: {validators_file}")

    def generate_routes(self):
        """Generate route handlers."""
        operations = self.get_operations()

        # Group by tag
        routes_by_tag: Dict[str, List[Dict]] = {}
        for op in operations:
            tag = op['tags'][0] if op['tags'] else 'default'
            if tag not in routes_by_tag:
                routes_by_tag[tag] = []
            routes_by_tag[tag].append(op)

        # Generate a route file per tag
        for tag, ops in routes_by_tag.items():
            self.generate_route_file(tag, ops)

    def generate_route_file(self, tag: str, operations: List[Dict]):
        """Generate a single route file."""
        tag_name = to_camel_case(tag)

        lines = [
            "import { Router, Request, Response, NextFunction } from 'express';",
            "import { validate } from './validators';",
            "import * as schemas from './validators';",
            '',
            f'const router = Router();',
            '',
        ]

        for op in operations:
            method = op['method']
            path = openapi_path_to_express(op['path'])
            handler_name = to_camel_case(op['operation_id'])
            summary = op.get('summary', '')

            # Check if has request body
            req_body = op.get('request_body', {})
            has_body = bool(req_body.get('content', {}).get('application/json'))

            # Find schema reference
            schema_ref = None
            if has_body:
                content = req_body.get('content', {}).get('application/json', {})
                schema = content.get('schema', {})
                if '$ref' in schema:
                    schema_ref = schema['$ref'].split('/')[-1]

            lines.append(f'/**')
            if summary:
                lines.append(f' * {summary}')
            lines.append(f' * {method.upper()} {op["path"]}')
            lines.append(f' */')

            middleware = ''
            if schema_ref:
                middleware = f'validate(schemas.{schema_ref}Schema), '

            lines.append(f"router.{method}('{path}', {middleware}async (req: Request, res: Response, next: NextFunction) => {{")
            lines.append('  try {')

            # Extract path params
            path_params = extract_path_params(op['path'])
            if path_params:
                lines.append(f"    const {{ {', '.join(path_params)} }} = req.params;")

            lines.append('')
            lines.append(f'    // TODO: Implement {handler_name}')
            lines.append('')

            # Default response based on method
            if method == 'post':
                lines.append("    res.status(201).json({ message: 'Created' });")
            elif method == 'delete':
                lines.append("    res.status(204).send();")
            else:
                lines.append("    res.json({ message: 'OK' });")

            lines.append('  } catch (err) {')
            lines.append('    next(err);')
            lines.append('  }')
            lines.append('});')
            lines.append('')

        lines.append(f'export default router;')

        route_file = self.output_dir / f'{tag_name}.routes.ts'
        route_file.write_text('\n'.join(lines))
        self.generated_files.append(str(route_file))
        print(f"  Generated: {route_file} ({len(operations)} handlers)")

    def generate_index(self):
        """Generate index file that combines all routes."""
        operations = self.get_operations()

        # Get unique tags
        tags = set()
        for op in operations:
            tag = op['tags'][0] if op['tags'] else 'default'
            tags.add(tag)

        lines = [
            "import { Router } from 'express';",
            '',
        ]

        for tag in sorted(tags):
            tag_name = to_camel_case(tag)
            lines.append(f"import {tag_name}Routes from './{tag_name}.routes';")

        lines.extend([
            '',
            'const router = Router();',
            '',
        ])

        for tag in sorted(tags):
            tag_name = to_camel_case(tag)
            # Use tag as base path
            base_path = '/' + tag.lower().replace(' ', '-')
            lines.append(f"router.use('{base_path}', {tag_name}Routes);")

        lines.extend([
            '',
            'export default router;',
        ])

        index_file = self.output_dir / 'index.ts'
        index_file.write_text('\n'.join(lines))
        self.generated_files.append(str(index_file))
        print(f"  Generated: {index_file}")


def main():
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description='Generate Express.js routes from OpenAPI specification',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  %(prog)s openapi.yaml --output src/routes/
  %(prog)s spec.json --framework fastify --output src/api/
  %(prog)s openapi.yaml --types-only --output src/types/
        '''
    )

    parser.add_argument(
        'spec',
        help='Path to OpenAPI specification (YAML or JSON)'
    )
    parser.add_argument(
        '--output', '-o',
        default='./generated',
        help='Output directory (default: ./generated)'
    )
    parser.add_argument(
        '--framework', '-f',
        choices=['express', 'fastify', 'koa'],
        default='express',
        help='Target framework (default: express)'
    )
    parser.add_argument(
        '--types-only',
        action='store_true',
        help='Generate only TypeScript types'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON'
    )

    args = parser.parse_args()

    try:
        scaffolder = APIScaffolder(
            spec_path=args.spec,
            output_dir=args.output,
            framework=args.framework,
            types_only=args.types_only,
            verbose=args.verbose,
        )

        results = scaffolder.run()

        print("-" * 50)
        print(f"Generated {results['routes_count']} route handlers")
        print(f"Generated {results['types_count']} type definitions")
        print(f"Output: {results['output']}")

        if args.json:
            print(json.dumps(results, indent=2))

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
