#!/usr/bin/env python3
"""
Visualization Generator
Generates self-contained HTML visualizations from data files and templates.
Wrapper around d3-scaffold.py logic but designed for data injection.
"""
import sys
import os
import json
import argparse
import csv
from pathlib import Path

# Add script directory to path to import d3-scaffold modules if needed
# But better to just import the dict structure if possible or replicate the logic
# For now, we will import the TEMPLATES from d3-scaffold directly
sys.path.append(str(Path(__file__).parent))
try:
    from d3_scaffold import TEMPLATES, HTML_TEMPLATE
except ImportError:
    # If file is named d3-scaffold.py (with hyphen), direct import fails
    import importlib.util
    spec = importlib.util.spec_from_file_location("d3_scaffold", Path(__file__).parent / "d3-scaffold.py")
    d3_scaffold = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(d3_scaffold)
    TEMPLATES = d3_scaffold.TEMPLATES
    HTML_TEMPLATE = d3_scaffold.HTML_TEMPLATE

def parse_data(file_path):
    """Load JSON or CSV data."""
    path = Path(file_path)
    if not path.exists():
        raise FileNotFoundError(f"Data file not found: {file_path}")
    
    if path.suffix.lower() == '.json':
        with open(path, 'r') as f:
            return json.load(f)
    elif path.suffix.lower() == '.csv':
        data = []
        with open(path, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                # Type inference could go here
                data.append(row)
        return data
    else:
        raise ValueError("Unsupported format. Use .json or .csv")

def generate_viz(data_file, template_name, output_file):
    """Generate HTML visualization."""
    
    template = TEMPLATES.get(template_name)
    if not template:
        raise ValueError(f"Unknown template: {template_name}. Available: {list(TEMPLATES.keys())}")

    # Load data
    data = parse_data(data_file)
    data_json = json.dumps(data, indent=2)

    # Inject data into JS
    # We look for "const data = ...;" or "const rawData = ...;" or "const datasets = ...;"
    # This is a simple string replacement hack. A more robust way would be to have explicit data variable names in templates.
    
    js = template['js']
    
    # Heuristics for replacement
    if "const data = {" in js or "const data = [" in js:
        # Replace the first assignment
        import re
        js = re.sub(r'const data = [\{\[].*?;', f'const data = {data_json};', js, flags=re.DOTALL, count=1)
    elif "const datasets =" in js:
         js = re.sub(r'const datasets = [\[].*?;', f'const datasets = {data_json};', js, flags=re.DOTALL, count=1)
    elif "const rawData =" in js:
         js = re.sub(r'const rawData = [\[].*?;', f'const rawData = {data_json};', js, flags=re.DOTALL, count=1)
    
    html = HTML_TEMPLATE.format(
        title=f"{template['title']} - Generated",
        description=f"Visualization of {Path(data_file).name}",
        instructions=template['instructions'],
        extra_scripts=template['extra_scripts'],
        css=template['css'],
        js=js
    )
    
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        f.write(html)
    
    print(f"Generated visualization: {output_path}")
    return output_path

def main():
    parser = argparse.ArgumentParser(description="Generate visualizations from data")
    parser.add_argument("data", help="Path to JSON/CSV data file")
    parser.add_argument("--template", "-t", required=True, choices=list(TEMPLATES.keys()), help="Visualization template")
    parser.add_argument("--output", "-o", help="Output HTML file path")
    
    args = parser.parse_args()
    
    if not args.output:
        args.output = f"{Path(args.data).stem}_{args.template}.html"
        
    try:
        generate_viz(args.data, args.template, args.output)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
