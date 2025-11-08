#!/usr/bin/env python3
"""
React + TypeScript Component Generator

Generates a fully-typed React component with TypeScript.
Usage: python create-component-template.py ComponentName [--with-props] [--with-state] [--with-hooks]
"""

import sys
import os
from pathlib import Path
from datetime import datetime


def generate_component(component_name: str, with_props: bool = False, with_state: bool = False, with_hooks: bool = False) -> str:
    """Generate a React component template with proper TypeScript typing."""

    props_interface = ""
    component_type = "React.FC"
    destructure = ""

    if with_props:
        props_interface = f"interface {component_name}Props {{\n  children?: React.ReactNode;\n  className?: string;\n  // Add your props here\n}}\n\n"
        component_type = f"React.FC<{component_name}Props>"
        destructure = "{ children, className }"

    state_section = ""
    if with_state:
        state_section = "  const [count, setCount] = React.useState<number>(0);\n\n  "

    hooks_section = ""
    if with_hooks:
        hooks_section = "  React.useEffect(() => {\n    // Side effect logic here\n  }, []); // Dependency array\n\n  "

    # Build template based on props
    if with_props:
        template = (
            "'use client'; // For Next.js App Router\n\n"
            "import React from 'react';\n\n"
            f"interface {component_name}Props {{\n"
            "  children?: React.ReactNode;\n"
            "  className?: string;\n"
            "  // Add your props here\n"
            "}\n\n"
            f"export const {component_name}: {component_type} = (" + "{\n"
            "  children,\n"
            "  className,\n"
            "}" + f") => {{\n"
            f"{state_section}{hooks_section}"
            "return (\n"
            "    <div className=" + "{className}" + ">\n"
            f"      <h1>{component_name}</h1>\n"
            "      {/* Component content here */}\n"
            "    </div>\n"
            "  );\n"
            "};\n\n"
            f"export default {component_name};\n"
        )
    else:
        template = (
            "'use client'; // For Next.js App Router\n\n"
            "import React from 'react';\n\n"
            f"export const {component_name}: {component_type} = () => {{\n"
            f"{state_section}{hooks_section}"
            "return (\n"
            "    <div>\n"
            f"      <h1>{component_name}</h1>\n"
            "      {/* Component content here */}\n"
            "    </div>\n"
            "  );\n"
            "};\n\n"
            f"export default {component_name};\n"
        )

    return template


def save_component(component_name: str, content: str, output_dir: str = '.') -> str:
    """Save component to file with TypeScript extension."""
    output_path = Path(output_dir) / f"{component_name}.tsx"
    output_path.write_text(content)
    return str(output_path.resolve())


def main():
    """Main entry point for component generation."""
    if len(sys.argv) < 2:
        print("Usage: python create-component-template.py ComponentName [options]")
        print("\nOptions:")
        print("  --with-props    Include Props interface")
        print("  --with-state    Include useState hook")
        print("  --with-hooks    Include useEffect hook")
        print("\nExample:")
        print("  python create-component-template.py Button --with-props")
        sys.exit(1)

    component_name = sys.argv[1]

    # Validate component name
    if not component_name[0].isupper():
        print(f"Error: Component name '{component_name}' must start with uppercase letter")
        sys.exit(1)

    if not component_name.isidentifier():
        print(f"Error: Component name '{component_name}' contains invalid characters")
        sys.exit(1)

    # Parse options
    with_props = '--with-props' in sys.argv
    with_state = '--with-state' in sys.argv
    with_hooks = '--with-hooks' in sys.argv

    # Generate component
    content = generate_component(component_name, with_props, with_state, with_hooks)

    # Save to file
    output_file = save_component(component_name, content)

    print(f"✓ Component created: {output_file}")
    print(f"\nGenerated component:")
    print("-" * 50)
    print(content)
    print("-" * 50)


if __name__ == '__main__':
    main()
