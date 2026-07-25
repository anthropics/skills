#!/usr/bin/env python3
"""
React Component Generator

Generates React/Next.js component files with TypeScript, Tailwind CSS,
and optional test files following best practices.

Usage:
    python component_generator.py Button --dir src/components/ui
    python component_generator.py ProductCard --type client --with-test
    python component_generator.py UserProfile --type server --with-story
"""

import argparse
import os
import sys
from pathlib import Path
from datetime import datetime


# Component templates
TEMPLATES = {
    "client": '''\'use client\';

import {{ useState }} from 'react';
import {{ cn }} from '@/lib/utils';

interface {name}Props {{
  className?: string;
  children?: React.ReactNode;
}}

export function {name}({{ className, children }}: {name}Props) {{
  return (
    <div className={{cn('', className)}}>
      {{children}}
    </div>
  );
}}
''',

    "server": '''import {{ cn }} from '@/lib/utils';

interface {name}Props {{
  className?: string;
  children?: React.ReactNode;
}}

export async function {name}({{ className, children }}: {name}Props) {{
  return (
    <div className={{cn('', className)}}>
      {{children}}
    </div>
  );
}}
''',

    "hook": '''import {{ useState, useEffect, useCallback }} from 'react';

interface Use{name}Options {{
  // Add options here
}}

interface Use{name}Return {{
  // Add return type here
  isLoading: boolean;
  error: Error | null;
}}

export function use{name}(options: Use{name}Options = {{}}): Use{name}Return {{
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {{
    // Effect logic here
  }}, []);

  return {{
    isLoading,
    error,
  }};
}}
''',

    "test": '''import {{ render, screen }} from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import {{ {name} }} from './{name}';

describe('{name}', () => {{
  it('renders correctly', () => {{
    render(<{name}>Test content</{name}>);
    expect(screen.getByText('Test content')).toBeInTheDocument();
  }});

  it('applies custom className', () => {{
    render(<{name} className="custom-class">Content</{name}>);
    expect(screen.getByText('Content').parentElement).toHaveClass('custom-class');
  }});

  // Add more tests here
}});
''',

    "story": '''import type {{ Meta, StoryObj }} from '@storybook/react';
import {{ {name} }} from './{name}';

const meta: Meta<typeof {name}> = {{
  title: 'Components/{name}',
  component: {name},
  tags: ['autodocs'],
  argTypes: {{
    className: {{
      control: 'text',
      description: 'Additional CSS classes',
    }},
  }},
}};

export default meta;
type Story = StoryObj<typeof {name}>;

export const Default: Story = {{
  args: {{
    children: 'Default content',
  }},
}};

export const WithCustomClass: Story = {{
  args: {{
    className: 'bg-blue-100 p-4',
    children: 'Styled content',
  }},
}};
''',

    "index": '''export {{ {name} }} from './{name}';
export type {{ {name}Props }} from './{name}';
''',
}


def to_pascal_case(name: str) -> str:
    """Convert string to PascalCase."""
    # Handle kebab-case and snake_case
    words = name.replace('-', '_').split('_')
    return ''.join(word.capitalize() for word in words)


def to_kebab_case(name: str) -> str:
    """Convert PascalCase to kebab-case."""
    result = []
    for i, char in enumerate(name):
        if char.isupper() and i > 0:
            result.append('-')
        result.append(char.lower())
    return ''.join(result)


def generate_component(
    name: str,
    output_dir: Path,
    component_type: str = "client",
    with_test: bool = False,
    with_story: bool = False,
    with_index: bool = True,
    flat: bool = False,
) -> dict:
    """Generate component files."""
    pascal_name = to_pascal_case(name)
    kebab_name = to_kebab_case(pascal_name)

    # Determine output path
    if flat:
        component_dir = output_dir
    else:
        component_dir = output_dir / pascal_name

    files_created = []

    # Create directory
    component_dir.mkdir(parents=True, exist_ok=True)

    # Generate main component file
    if component_type == "hook":
        main_file = component_dir / f"use{pascal_name}.ts"
        template = TEMPLATES["hook"]
    else:
        main_file = component_dir / f"{pascal_name}.tsx"
        template = TEMPLATES[component_type]

    content = template.format(name=pascal_name)
    main_file.write_text(content)
    files_created.append(str(main_file))

    # Generate test file
    if with_test and component_type != "hook":
        test_file = component_dir / f"{pascal_name}.test.tsx"
        test_content = TEMPLATES["test"].format(name=pascal_name)
        test_file.write_text(test_content)
        files_created.append(str(test_file))

    # Generate story file
    if with_story and component_type != "hook":
        story_file = component_dir / f"{pascal_name}.stories.tsx"
        story_content = TEMPLATES["story"].format(name=pascal_name)
        story_file.write_text(story_content)
        files_created.append(str(story_file))

    # Generate index file
    if with_index and not flat:
        index_file = component_dir / "index.ts"
        index_content = TEMPLATES["index"].format(name=pascal_name)
        index_file.write_text(index_content)
        files_created.append(str(index_file))

    return {
        "name": pascal_name,
        "type": component_type,
        "directory": str(component_dir),
        "files": files_created,
    }


def print_result(result: dict, verbose: bool = False) -> None:
    """Print generation result."""
    print(f"\n{'='*50}")
    print(f"Component Generated: {result['name']}")
    print(f"{'='*50}")
    print(f"Type: {result['type']}")
    print(f"Directory: {result['directory']}")
    print(f"\nFiles created:")
    for file in result['files']:
        print(f"  - {file}")
    print(f"{'='*50}\n")

    # Print usage hint
    if result['type'] != 'hook':
        print("Usage:")
        print(f"  import {{ {result['name']} }} from '@/components/{result['name']}';")
        print(f"\n  <{result['name']}>Content</{result['name']}>")
    else:
        print("Usage:")
        print(f"  import {{ use{result['name']} }} from '@/hooks/use{result['name']}';")
        print(f"\n  const {{ isLoading, error }} = use{result['name']}();")


def main():
    parser = argparse.ArgumentParser(
        description="Generate React/Next.js components with TypeScript and Tailwind CSS"
    )
    parser.add_argument(
        "name",
        help="Component name (PascalCase or kebab-case)"
    )
    parser.add_argument(
        "--dir", "-d",
        default="src/components",
        help="Output directory (default: src/components)"
    )
    parser.add_argument(
        "--type", "-t",
        choices=["client", "server", "hook"],
        default="client",
        help="Component type (default: client)"
    )
    parser.add_argument(
        "--with-test",
        action="store_true",
        help="Generate test file"
    )
    parser.add_argument(
        "--with-story",
        action="store_true",
        help="Generate Storybook story file"
    )
    parser.add_argument(
        "--no-index",
        action="store_true",
        help="Skip generating index.ts file"
    )
    parser.add_argument(
        "--flat",
        action="store_true",
        help="Create files directly in output dir without subdirectory"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be generated without creating files"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output"
    )

    args = parser.parse_args()

    output_dir = Path(args.dir)
    pascal_name = to_pascal_case(args.name)

    if args.dry_run:
        print(f"\nDry run - would generate:")
        print(f"  Component: {pascal_name}")
        print(f"  Type: {args.type}")
        print(f"  Directory: {output_dir / pascal_name if not args.flat else output_dir}")
        print(f"  Test: {'Yes' if args.with_test else 'No'}")
        print(f"  Story: {'Yes' if args.with_story else 'No'}")
        return

    try:
        result = generate_component(
            name=args.name,
            output_dir=output_dir,
            component_type=args.type,
            with_test=args.with_test,
            with_story=args.with_story,
            with_index=not args.no_index,
            flat=args.flat,
        )
        print_result(result, args.verbose)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
