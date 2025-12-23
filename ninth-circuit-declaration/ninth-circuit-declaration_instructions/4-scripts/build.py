import json
import subprocess
import sys
import os
import argparse
from pathlib import Path

# --- Configuration ---
# Relative paths from this script (src/build.py)
SCRIPT_DIR = Path(__file__).parent
SKILL_ROOT = SCRIPT_DIR.parent
WORKSPACE_ROOT = SKILL_ROOT.parent.parent  # Assuming skills/ninth-circuit-declaration/src/build.py

# External Tools (Still referencing shared skills for now)
SKILLS_DIR = WORKSPACE_ROOT / "skills"
COVER_SCRIPT = SKILLS_DIR / "PIMP-SMACK-APP/_archive/COVER_GENERATOR_COMPLETE/generate_cover.py"
RENDER_SCRIPT = SKILLS_DIR / "universal-motion-brief/scripts/render_docx.py"
MERGE_SCRIPT = SKILLS_DIR / "scripts/merge_docs.py"

# Internal Tools
TEMPLATE_GEN_SCRIPT = SCRIPT_DIR / "generator.py"

# Templates
TEMPLATE_DOCX = SKILL_ROOT / "templates/declaration_template.docx"

# Output
OUTPUT_DIR = SKILLS_DIR / ".outbox"  # Global output for the skill

def run_command(cmd, description):
    print(f"[{description}]...")
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"FAILED: {result.stderr}")
        sys.exit(1)
    return result.stdout

def main():
    parser = argparse.ArgumentParser(description="Generate a Ninth Circuit Declaration from a JSON config.")
    parser.add_argument("config_file", nargs="?", default="filing_config.json", help="Path to the JSON configuration file.")
    args = parser.parse_args()

    config_path = Path(args.config_file)
    if not config_path.exists():
        print(f"Error: Configuration file {config_path} not found.")
        sys.exit(1)

    print(f"Reading configuration from {config_path}...")
    with open(config_path, 'r') as f:
        config = json.load(f)

    # Support both simple and advanced config structures
    if 'metadata' in config:
        # Advanced Config
        meta = {
            'case_number': config['placeholders']['runtime'].get('CASE_NUMBER', ''),
            'filing_title': config['placeholders']['runtime'].get('FILING_TITLE', ''),
            'judge_name': config['placeholders']['runtime'].get('JUDGE_NAME', '')
        }
        # Merge standard and runtime placeholders for content
        content = {**config['placeholders'].get('standard', {}), **config['placeholders'].get('runtime', {})}
        tool_name = config['metadata'].get('tool_name', 'Tool')
        base_name = config['metadata'].get('output_filename', 'Generated_Filing.docx')
        
        # Extract font settings from 'Default' style if available for cover page
        default_style = config.get('styles', {}).get('Default', {})
        fmt = {
            'default_font': default_style.get('font'),
            'default_size': default_style.get('size')
        }
    else:
        # Simple Config (Legacy)
        meta = config['case_metadata']
        content = config['document_content']
        tool_name = config.get('tool_name', 'Tool')
        base_name = config.get('output_filename', 'Generated_Filing.docx')
        fmt = config.get("formatting", {})
    
    # Enforce Naming Convention: YYYY-MM-DD-[Tool_Name]-[Filename]
    from datetime import datetime
    date_str = datetime.now().strftime("%Y-%m-%d")
    
    # Strip existing date prefix if present to avoid duplication
    if base_name.startswith(date_str):
        final_name = base_name
    else:
        final_name = f"{date_str}_{tool_name}-{base_name}"
        
    filename = final_name

    # Ensure output directory exists
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    
    # Temporary files
    temp_cover = OUTPUT_DIR / "temp_cover.docx"
    temp_body = OUTPUT_DIR / "temp_body.docx"
    temp_data_json = OUTPUT_DIR / "temp_data.json"
    final_output = OUTPUT_DIR / filename

    try:
        # 0. Regenerate Template with Configured Formatting
        # Now using the strict styles file
        styles_path = SKILL_ROOT / "styles.json"
        cmd_template = [
            "python", str(TEMPLATE_GEN_SCRIPT),
            str(config_path),
            "--styles", str(styles_path)
        ]
        run_command(cmd_template, "Regenerating Template with Strict Styles")

        # 1. Generate Cover
        # Maps JSON config to CLI arguments for the cover generator
        # fmt is already determined above based on config type
        cmd_cover = [
            "python", str(COVER_SCRIPT),
            "--case", meta['case_number'],
            "--filing", meta['filing_title'],
            "--judge", meta['judge_name'],
            "--output", str(temp_cover)
        ]
        
        if fmt.get("default_font"):
            cmd_cover.extend(["--font", fmt["default_font"]])
        if fmt.get("default_size"):
            cmd_cover.extend(["--size", str(fmt["default_size"])])

        run_command(cmd_cover, "Generating Cover Page")

        # 2. Generate Body
        # Write the content section to a temp JSON for the renderer
        with open(temp_data_json, 'w') as f:
            json.dump(content, f, indent=2)

        cmd_body = [
            "python", str(RENDER_SCRIPT),
            "--template", str(TEMPLATE_DOCX),
            "--data", str(temp_data_json),
            "--output", str(temp_body)
        ]
        run_command(cmd_body, "Generating Declaration Body")

        # 3. Merge
        cmd_merge = [
            "python", str(MERGE_SCRIPT),
            str(temp_cover),
            str(temp_body),
            str(final_output)
        ]
        run_command(cmd_merge, "Merging Documents")

        print(f"\nSUCCESS: Generated 2-page document.")
        print(f"Location: {final_output}")

    finally:
        # Cleanup temp files
        if temp_cover.exists(): os.remove(temp_cover)
        if temp_body.exists(): os.remove(temp_body)
        if temp_data_json.exists(): os.remove(temp_data_json)

if __name__ == "__main__":
    main()
