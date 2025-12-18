#!/usr/bin/env python3
"""
Hive Module Creator - Generate new tool modules from template.

Usage:
    python create_module.py my_module           # Create new module
    python create_module.py weather --tools get_forecast,get_current
"""

import argparse
import os
import sys
from datetime import datetime

MODULE_TEMPLATE = '''#!/usr/bin/env python3
"""
{display_name} - {description}

This module provides {module_name} tools for the Swarm agent system.

Usage:
    python swarm_{module_name}.py --test        # Run tests
    python swarm_{module_name}.py --interactive # Interactive mode
"""

import argparse
import json
import os
import sys

# Module metadata
MODULE_NAME = "{module_name}"
DISPLAY_NAME = "{display_name}"
DESCRIPTION = "{description}"

# Tool schemas (OpenAI function calling format)
TOOL_SCHEMAS = [
{tool_schemas}
]

# Tool implementations
TOOL_IMPLEMENTATIONS = {{
{tool_implementations}
}}


def get_tool_schemas():
    """Return tool schemas for registration."""
    return TOOL_SCHEMAS


def handle_tool_calls(tool_name: str, arguments: dict, config: dict = None):
    """Handle tool invocation."""
    if tool_name not in TOOL_IMPLEMENTATIONS:
        return {{"error": f"Unknown tool: {{tool_name}}"}}

    try:
        return TOOL_IMPLEMENTATIONS[tool_name](arguments, config)
    except Exception as e:
        return {{"error": str(e)}}


{tool_functions}


def run_tests():
    """Run module tests."""
    print(f"Testing {{DISPLAY_NAME}}...")
    print("-" * 40)

    for tool in TOOL_SCHEMAS:
        print(f"\\nTesting: {{tool['name']}}")
        # Create test arguments based on required params
        test_args = {{}}
        for param, info in tool.get("parameters", {{}}).get("properties", {{}}).items():
            if param in tool.get("parameters", {{}}).get("required", []):
                if info.get("type") == "string":
                    test_args[param] = "test"
                elif info.get("type") == "integer":
                    test_args[param] = 1

        result = handle_tool_calls(tool["name"], test_args)
        print(f"  Result: {{json.dumps(result, indent=2)[:200]}}")

    print("\\n" + "-" * 40)
    print("Tests complete!")


def interactive_mode():
    """Run interactive mode."""
    print(f"{{DISPLAY_NAME}} - Interactive Mode")
    print("Type 'help' for available tools, 'quit' to exit")
    print("-" * 40)

    while True:
        try:
            cmd = input("\\n> ").strip()
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue
        if cmd.lower() in ["quit", "exit", "q"]:
            break
        if cmd.lower() == "help":
            print("\\nAvailable tools:")
            for tool in TOOL_SCHEMAS:
                print(f"  {{tool['name']}} - {{tool['description']}}")
            continue

        # Parse command as: tool_name arg1=val1 arg2=val2
        parts = cmd.split()
        if not parts:
            continue

        tool_name = parts[0]
        args = {{}}
        for part in parts[1:]:
            if "=" in part:
                k, v = part.split("=", 1)
                args[k] = v

        result = handle_tool_calls(tool_name, args)
        print(json.dumps(result, indent=2))


def main():
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    parser.add_argument("--test", action="store_true", help="Run tests")
    parser.add_argument("--interactive", "-i", action="store_true", help="Interactive mode")
    parser.add_argument("--list", "-l", action="store_true", help="List tools")

    args = parser.parse_args()

    if args.test:
        run_tests()
    elif args.interactive:
        interactive_mode()
    elif args.list:
        print(f"{{DISPLAY_NAME}} Tools:")
        for tool in TOOL_SCHEMAS:
            print(f"  {{tool['name']}} - {{tool['description']}}")
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
'''

def create_tool_schema(name: str) -> str:
    """Generate tool schema."""
    return f'''    {{
        "name": "{name}",
        "description": "Description for {name}",
        "parameters": {{
            "type": "object",
            "properties": {{
                "input": {{
                    "type": "string",
                    "description": "Input parameter"
                }}
            }},
            "required": ["input"]
        }}
    }}'''

def create_tool_implementation(name: str) -> str:
    """Generate tool implementation reference."""
    return f'    "{name}": handle_{name},'

def create_tool_function(name: str) -> str:
    """Generate tool handler function."""
    return f'''def handle_{name}(arguments: dict, config: dict = None) -> dict:
    """Handle {name} tool call."""
    input_val = arguments.get("input", "")
    # TODO: Implement actual logic
    return {{
        "tool": "{name}",
        "status": "success",
        "result": f"Processed: {{input_val}}"
    }}

'''

def create_module(module_name: str, tools: list = None, output_dir: str = "."):
    """Create a new tool module."""
    if not tools:
        tools = [f"{module_name}_action"]

    display_name = module_name.replace("_", " ").title()
    description = f"{display_name} tools for Swarm agent system"

    # Generate tool components
    schemas = ",\n".join(create_tool_schema(t) for t in tools)
    implementations = "\n".join(create_tool_implementation(t) for t in tools)
    functions = "".join(create_tool_function(t) for t in tools)

    # Fill template
    content = MODULE_TEMPLATE.format(
        module_name=module_name,
        display_name=display_name,
        description=description,
        tool_schemas=schemas,
        tool_implementations=implementations,
        tool_functions=functions
    )

    # Write file
    filename = f"swarm_{module_name}.py"
    filepath = os.path.join(output_dir, filename)

    with open(filepath, "w") as f:
        f.write(content)

    print(f"Created module: {filepath}")
    print(f"Tools: {', '.join(tools)}")
    print(f"\nNext steps:")
    print(f"  1. Edit {filename} to implement actual tool logic")
    print(f"  2. Test: python {filename} --test")
    print(f"  3. Interactive: python {filename} --interactive")

def main():
    parser = argparse.ArgumentParser(
        description="Create new Hive tool module from template",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python create_module.py weather                    # Basic module
  python create_module.py weather --tools get_forecast,get_current
  python create_module.py my_module -o ./hive/      # Custom output dir
        """
    )

    parser.add_argument("module_name", help="Name for new module (snake_case)")
    parser.add_argument("--tools", "-t", help="Comma-separated list of tool names")
    parser.add_argument("--output", "-o", default=".", help="Output directory")

    args = parser.parse_args()

    tools = args.tools.split(",") if args.tools else None
    create_module(args.module_name, tools, args.output)

if __name__ == "__main__":
    main()
