#!/usr/bin/env python3
import sys
import json
import logging
import argparse
import tempfile
from pathlib import Path

# Add script directory to path
script_dir = Path(__file__).parent
sys.path.append(str(script_dir))

# Import logic
try:
    from viz_generator import generate_viz
    from d3_scaffold import TEMPLATES
except ImportError:
    import importlib.util
    spec = importlib.util.spec_from_file_location("viz_generator", script_dir / "viz-generator.py")
    viz_generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(viz_generator)
    generate_viz = viz_generator.generate_viz
    
    spec_scaffold = importlib.util.spec_from_file_location("d3_scaffold", script_dir / "d3-scaffold.py")
    d3_scaffold = importlib.util.module_from_spec(spec_scaffold)
    spec_scaffold.loader.exec_module(d3_scaffold)
    TEMPLATES = d3_scaffold.TEMPLATES

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("datavis-server")

def list_tools():
    return [
        {
            "name": "dream_visualize_data",
            "description": "Create interactive visualizations (charts, graphs, maps) from data.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "data": {
                        "type": "string",
                        "description": "JSON string of data, or key-value pairs to visualize"
                    },
                    "template": {
                        "type": "string",
                        "description": f"Visualization template. Options: {', '.join(TEMPLATES.keys())}",
                        "enum": list(TEMPLATES.keys())
                    },
                    "title": {
                        "type": "string",
                        "description": "Title for the visualization"
                    }
                },
                "required": ["data", "template"]
            }
        },
        {
            "name": "dream_list_viz_templates",
            "description": "List available visualization templates with descriptions.",
            "inputSchema": {
                "type": "object",
                "properties": {}
            }
        }
    ]

def handle_call_tool(name, arguments):
    if name == "dream_visualize_data":
        data_str = arguments.get("data")
        template = arguments.get("template")
        title = arguments.get("title", "Data Visualization")
        
        # Parse data
        try:
            if isinstance(data_str, str):
                data = json.loads(data_str)
            else:
                data = data_str
        except json.JSONDecodeError:
            return {"content": [{"type": "text", "text": "Error: Data must be valid JSON."}], "isError": True}
        
        # Create temp file for data
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(data, f)
            data_path = f.name
            
        # Define output path
        output_filename = f"viz_{template}_{Path(data_path).stem}.html"
        output_dir = Path.home() / "geepers" / "visualizations"
        output_dir.mkdir(parents=True, exist_ok=True)
        output_path = output_dir / output_filename
        
        try:
            final_path = generate_viz(data_path, template, str(output_path))
            return {
                "content": [
                    {
                        "type": "text", 
                        "text": f"Visualization created successfully at: {final_path}\n\nYou can open this file in a browser to view interactively."
                    }
                ]
            }
        except Exception as e:
            return {"content": [{"type": "text", "text": f"Generation failed: {str(e)}"}], "isError": True}

    elif name == "dream_list_viz_templates":
        descriptions = [f"- **{k}**: {v['description']}" for k, v in TEMPLATES.items()]
        return {
            "content": [{"type": "text", "text": "Available Templates:\n\n" + "\n".join(descriptions)}]
        }

    return {"content": [{"type": "text", "text": f"Tool not found: {name}"}], "isError": True}

def run_server():
    """Run STDIO server."""
    logging.info("Starting Datavis MCP Server...")
    while True:
        try:
            line = sys.stdin.readline()
            if not line:
                break
            
            request = json.loads(line)
            req_id = request.get("id")
            method = request.get("method")
            params = request.get("params", {})
            
            response = {
                "jsonrpc": "2.0",
                "id": req_id
            }
            
            if method == "initialize":
                response["result"] = {
                    "protocolVersion": "2024-11-05",
                    "capabilities": {
                        "tools": {}
                    },
                    "serverInfo": {
                        "name": "geepers-datavis",
                        "version": "1.0.0"
                    }
                }
            elif method == "tools/list":
                response["result"] = {
                    "tools": list_tools()
                }
            elif method == "tools/call":
                result = handle_call_tool(params.get("name"), params.get("arguments"))
                if result.get("isError"):
                    response["error"] = {"code": -32603, "message": result["content"][0]["text"]}
                else:
                    response["result"] = result
            else:
                # Ignore notifications or methods we don't handle
                continue
                
            print(json.dumps(response), flush=True)
            
        except BrokenPipeError:
            break
        except Exception as e:
            logger.error(f"Error handling request: {e}")
            if 'req_id' in locals() and req_id is not None:
                 print(json.dumps({
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "error": {"code": -32603, "message": str(e)}
                }), flush=True)

if __name__ == "__main__":
    run_server()
