#!/usr/bin/env python3
"""
List all available Swarm tools and modules.

Usage:
    python list_tools.py               # List all tools
    python list_tools.py --module search  # Filter by module
    python list_tools.py --schemas     # Show full schemas
"""

import argparse
import json

# Tool registry (would be loaded from actual swarm system)
TOOLS = {
    "search": {
        "display_name": "Search Tools",
        "description": "Web and image search capabilities",
        "tools": [
            {
                "name": "web_search",
                "description": "Search the web for information",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "query": {"type": "string", "description": "Search query"},
                        "num_results": {"type": "integer", "default": 10}
                    },
                    "required": ["query"]
                }
            },
            {
                "name": "image_search",
                "description": "Search for images",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "query": {"type": "string", "description": "Image search query"},
                        "num_results": {"type": "integer", "default": 10}
                    },
                    "required": ["query"]
                }
            },
            {
                "name": "map_search",
                "description": "Search for locations and maps",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "query": {"type": "string", "description": "Location query"},
                        "type": {"type": "string", "enum": ["places", "directions", "geocode"]}
                    },
                    "required": ["query"]
                }
            }
        ]
    },
    "research": {
        "display_name": "Research Tools",
        "description": "Academic and scientific research",
        "tools": [
            {
                "name": "arxiv_search",
                "description": "Search arXiv for academic papers",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "query": {"type": "string"},
                        "max_results": {"type": "integer", "default": 10},
                        "categories": {"type": "array", "items": {"type": "string"}}
                    },
                    "required": ["query"]
                }
            },
            {
                "name": "pubmed_search",
                "description": "Search PubMed for medical literature",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "query": {"type": "string"},
                        "max_results": {"type": "integer", "default": 10}
                    },
                    "required": ["query"]
                }
            },
            {
                "name": "scholar_search",
                "description": "Search Semantic Scholar for papers",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "query": {"type": "string"},
                        "year_range": {"type": "string"},
                        "fields": {"type": "array", "items": {"type": "string"}}
                    },
                    "required": ["query"]
                }
            }
        ]
    },
    "gen": {
        "display_name": "Generation Tools",
        "description": "AI image and content generation",
        "tools": [
            {
                "name": "generate_image",
                "description": "Generate images from text prompts",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "prompt": {"type": "string", "description": "Image description"},
                        "size": {"type": "string", "default": "1024x1024"},
                        "provider": {"type": "string", "enum": ["xai", "openai", "stability"]}
                    },
                    "required": ["prompt"]
                }
            },
            {
                "name": "edit_image",
                "description": "Edit existing images with AI",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "image_url": {"type": "string"},
                        "prompt": {"type": "string"},
                        "mask_url": {"type": "string"}
                    },
                    "required": ["image_url", "prompt"]
                }
            }
        ]
    },
    "finance": {
        "display_name": "Finance Tools",
        "description": "Financial data and market information",
        "tools": [
            {
                "name": "stock_quote",
                "description": "Get current stock price and info",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "symbol": {"type": "string", "description": "Stock ticker symbol"}
                    },
                    "required": ["symbol"]
                }
            },
            {
                "name": "market_data",
                "description": "Get market indices and trends",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "indices": {"type": "array", "items": {"type": "string"}}
                    }
                }
            }
        ]
    },
    "data": {
        "display_name": "Data Tools",
        "description": "Data fetching and transformation",
        "tools": [
            {
                "name": "fetch_json",
                "description": "Fetch JSON from URL",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "url": {"type": "string"},
                        "headers": {"type": "object"}
                    },
                    "required": ["url"]
                }
            },
            {
                "name": "parse_csv",
                "description": "Parse CSV data",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "content": {"type": "string"},
                        "delimiter": {"type": "string", "default": ","}
                    },
                    "required": ["content"]
                }
            }
        ]
    }
}

def list_tools(module: str = None, show_schemas: bool = False):
    """List available tools."""
    modules = {module: TOOLS[module]} if module and module in TOOLS else TOOLS

    if not modules:
        print(f"Unknown module: {module}")
        print(f"Available modules: {', '.join(TOOLS.keys())}")
        return

    total_tools = 0

    for mod_name, mod_info in modules.items():
        print(f"\n{mod_info['display_name']} ({mod_name})")
        print(f"  {mod_info['description']}")
        print()

        for tool in mod_info["tools"]:
            total_tools += 1
            print(f"  {tool['name']}")
            print(f"    {tool['description']}")

            if show_schemas:
                print(f"    Parameters:")
                params = tool.get("parameters", {}).get("properties", {})
                required = tool.get("parameters", {}).get("required", [])
                for param_name, param_info in params.items():
                    req = "*" if param_name in required else ""
                    ptype = param_info.get("type", "any")
                    desc = param_info.get("description", "")
                    print(f"      {param_name}{req} ({ptype}): {desc}")
            print()

    print(f"Total: {total_tools} tools in {len(modules)} modules")

def export_schemas(output: str):
    """Export all schemas to JSON file."""
    with open(output, "w") as f:
        json.dump(TOOLS, f, indent=2)
    print(f"Schemas exported to: {output}")

def main():
    parser = argparse.ArgumentParser(
        description="List Swarm tools and modules",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    parser.add_argument("--module", "-m", help="Filter by module name")
    parser.add_argument("--schemas", "-s", action="store_true", help="Show full parameter schemas")
    parser.add_argument("--export", "-e", help="Export schemas to JSON file")
    parser.add_argument("--json", action="store_true", help="Output as JSON")

    args = parser.parse_args()

    if args.export:
        export_schemas(args.export)
        return

    if args.json:
        print(json.dumps(TOOLS, indent=2))
        return

    list_tools(args.module, args.schemas)

if __name__ == "__main__":
    main()
