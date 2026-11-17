"""
PIMP SMACK - Template Generator
Generates court-ready documents from Word 2003 XML templates.
Uses placeholder replacement - preserves all Word formatting.

NO FILE EDITING REQUIRED - Everything is programmatic.
Call functions with data, get documents out.

USAGE:
    from template_generator import TemplateGenerator
    gen = TemplateGenerator()
    gen.generate_and_save_motion({"INTRODUCTION_TEXT": "..."}, "my_motion")
    
SEE: CHEAT_SHEET.md for full documentation
"""

import json
import re
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, Optional, List


class TemplateGenerator:
    """Generate documents from Word 2003 XML templates."""
    
    def __init__(self, config_path: Optional[str] = None):
        self.app_dir = Path(__file__).parent
        self.templates_dir = self.app_dir / "templates"
        self.output_dir = self.app_dir / "output"
        self.output_dir.mkdir(exist_ok=True)
        
        # Load master config
        config_path = config_path or self.app_dir / "MASTER_CASE_CONFIG.json"
        self.config = self._load_config(config_path)
        
        # Template paths
        self.templates = {
            "motion": self.templates_dir / "MOTION_TEMPLATE.xml",
            "declaration": self.templates_dir / "DECLARATION_TEMPLATE.xml",
            "notice": self.templates_dir / "NOTICE_TEMPLATE.xml",
        }
    
    def _load_config(self, path) -> dict:
        """Load master case config."""
        path = Path(path)
        if path.exists():
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {}
    
    def _get_base_placeholders(self) -> Dict[str, str]:
        """Get common placeholders from config."""
        case_info = self.config.get("case_info", {})
        party_info = self.config.get("party_info", {})
        
        now = datetime.now()
        
        return {
            # Case info
            "CASE_NUMBER": case_info.get("case_number", "XX-XXXX"),
            "COURT_NAME": case_info.get("court_name", ""),
            "JUDGE_NAME": case_info.get("judge_name", ""),
            
            # Party info
            "PARTY_NAME": party_info.get("name", ""),
            "PARTY_NAME_CAPS": party_info.get("name", "").upper(),
            "ADDRESS_LINE_1": party_info.get("address_line_1", ""),
            "CITY_STATE_ZIP": party_info.get("city_state_zip", ""),
            "EMAIL": party_info.get("email", ""),
            "PHONE": party_info.get("phone", ""),
            
            # Dates
            "DAY": str(now.day),
            "MONTH": now.strftime("%B"),
            "YEAR": str(now.year),
            "SERVICE_DATE": now.strftime("%B %d, %Y"),
            "EXECUTION_DATE": now.strftime("%B %d, %Y"),
            "EXECUTION_CITY": party_info.get("city", ""),
            "EXECUTION_STATE": party_info.get("state", ""),
        }
    
    def _replace_placeholders(self, template: str, data: Dict[str, str]) -> str:
        """Replace {{PLACEHOLDER}} with actual values."""
        result = template
        for key, value in data.items():
            placeholder = "{{" + key + "}}"
            result = result.replace(placeholder, str(value))
        return result
    
    def generate_motion(self, motion_data: Dict[str, str]) -> str:
        """
        Generate a motion document.
        
        motion_data should contain:
        - INTRODUCTION_TEXT
        - STATEMENT_OF_FACTS_TEXT
        - ARGUMENT_I_TITLE, ARGUMENT_I_TEXT
        - ARGUMENT_II_TITLE, ARGUMENT_II_TEXT
        - CONCLUSION_TEXT
        - DOCUMENT_TITLE
        """
        template_path = self.templates["motion"]
        if not template_path.exists():
            raise FileNotFoundError(f"Template not found: {template_path}")
        
        with open(template_path, 'r', encoding='utf-8') as f:
            template = f.read()
        
        # Merge base + motion-specific data
        placeholders = self._get_base_placeholders()
        placeholders.update(motion_data)
        
        # Replace and return
        return self._replace_placeholders(template, placeholders)
    
    def generate_declaration(self, declaration_data: Dict[str, str]) -> str:
        """
        Generate a declaration document (2+2+1 structure).
        
        declaration_data should contain:
        - DECLARANT_NAME
        - DECLARANT_NAME_CAPS
        - FACT_1_IDENTITY
        - FACT_2_RELATIONSHIP
        - FACT_3_PRIMARY
        - FACT_4_SUPPORTING
        - FACT_5_CONCLUSION
        """
        template_path = self.templates["declaration"]
        if not template_path.exists():
            raise FileNotFoundError(f"Template not found: {template_path}")
        
        with open(template_path, 'r', encoding='utf-8') as f:
            template = f.read()
        
        placeholders = self._get_base_placeholders()
        placeholders.update(declaration_data)
        
        return self._replace_placeholders(template, placeholders)
    
    def generate_notice(self, notice_data: Dict[str, str]) -> str:
        """
        Generate a notice document.
        
        notice_data should contain:
        - NOTICE_TITLE
        - NOTICE_RECIPIENTS
        - NOTICE_BODY
        - NOTICE_DATE
        - NOTICE_TIME
        - NOTICE_LOCATION
        - ADDITIONAL_NOTICE
        """
        template_path = self.templates["notice"]
        if not template_path.exists():
            raise FileNotFoundError(f"Template not found: {template_path}")
        
        with open(template_path, 'r', encoding='utf-8') as f:
            template = f.read()
        
        placeholders = self._get_base_placeholders()
        placeholders.update(notice_data)
        
        return self._replace_placeholders(template, placeholders)
    
    def save_document(self, content: str, filename: str) -> Path:
        """Save generated document as .xml (opens in Word)."""
        if not filename.endswith('.xml'):
            filename += '.xml'
        
        output_path = self.output_dir / filename
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"[OK] Document saved: {output_path}")
        return output_path
    
    def generate_and_save_motion(self, motion_data: Dict[str, str], filename: str) -> Path:
        """Generate and save motion in one call."""
        content = self.generate_motion(motion_data)
        return self.save_document(content, filename)
    
    def generate_and_save_declaration(self, declaration_data: Dict[str, str], filename: str) -> Path:
        """Generate and save declaration in one call."""
        content = self.generate_declaration(declaration_data)
        return self.save_document(content, filename)
    
    def generate_and_save_notice(self, notice_data: Dict[str, str], filename: str) -> Path:
        """Generate and save notice in one call."""
        content = self.generate_notice(notice_data)
        return self.save_document(content, filename)
    
    # =========================================================================
    # PLAYLIST SUPPORT
    # =========================================================================
    
    def load_registry(self) -> dict:
        """Load template registry."""
        registry_path = self.templates_dir / "TEMPLATE_REGISTRY.json"
        if registry_path.exists():
            with open(registry_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {}
    
    def get_playlist(self, playlist_name: str) -> dict:
        """Get playlist configuration."""
        registry = self.load_registry()
        playlists = registry.get("playlists", {})
        return playlists.get(playlist_name, {})
    
    def generate_cover(self, cover_data: Dict[str, str]) -> Optional[Path]:
        """
        Generate cover page using existing cover generator.
        
        cover_data should contain:
        - case_number
        - appellant_name  
        - appellee_names (comma-separated)
        - document_title
        - lower_court
        """
        cover_gen_dir = self.app_dir.parent.parent / "COVER_GENERATOR_COMPLETE"
        cover_script = cover_gen_dir / "generate_cover.py"
        
        if not cover_script.exists():
            print(f"[WARN] Cover generator not found: {cover_script}")
            return None
        
        # The cover generator reads from its own config or CLI args
        # For now, return the path - user can run it separately
        print(f"[INFO] Cover generator available at: {cover_script}")
        print(f"[INFO] Run: python \"{cover_script}\"")
        return cover_script
    
    def generate_declaration_docx(self, facts: List[Dict], filename: str) -> Optional[Path]:
        """
        Generate declaration using existing declaration-builder (outputs .docx).
        
        facts should be list of dicts with:
        - title: str
        - circumstance_time_place: str
        - circumstance_parties: str
        - element_primary: str
        - element_supporting: str
        - party_link: str
        """
        try:
            # Import from declaration-builder
            builder_dir = self.app_dir / "declaration-builder" / "scripts"
            if not builder_dir.exists():
                print(f"[WARN] Declaration builder not found: {builder_dir}")
                return None
            
            sys.path.insert(0, str(builder_dir))
            from document_builder import DeclarationBuilder, DeclarationFact
            
            # Get config values
            case_info = self.config.get("case_info", {})
            party_info = self.config.get("party_info", {})
            
            # Create builder
            builder = DeclarationBuilder(
                declarant=party_info.get("name", ""),
                case_number=case_info.get("case_number", ""),
                appellant=party_info.get("name", ""),
                appellee="Defendants",
                jurisdiction="ninth"
            )
            
            # Add facts
            for f in facts:
                fact = DeclarationFact(
                    title=f.get("title", ""),
                    circumstance_time_place=f.get("circumstance_time_place", ""),
                    circumstance_parties=f.get("circumstance_parties", ""),
                    element_primary=f.get("element_primary", ""),
                    element_supporting=f.get("element_supporting", ""),
                    party_link=f.get("party_link", ""),
                    defendant=f.get("defendant", "Defendants"),
                )
                builder.add_fact(fact)
            
            # Save
            if not filename.endswith('.docx'):
                filename += '.docx'
            output_path = self.output_dir / filename
            builder.save(str(output_path))
            
            print(f"[OK] Declaration saved: {output_path}")
            return output_path
            
        except Exception as e:
            print(f"[ERROR] Declaration builder failed: {e}")
            return None
    
    def generate_playlist(self, playlist_name: str, data: Dict[str, str], base_filename: str) -> List[Path]:
        """
        Generate all documents in a playlist.
        
        Args:
            playlist_name: Name from TEMPLATE_REGISTRY.json playlists
            data: Combined data dict for all templates
            base_filename: Base name for output files
            
        Returns:
            List of generated file paths
        """
        playlist = self.get_playlist(playlist_name)
        if not playlist:
            raise ValueError(f"Playlist not found: {playlist_name}")
        
        templates = playlist.get("templates", [])
        generated = []
        
        for template_id in templates:
            try:
                if template_id == "motion":
                    path = self.generate_and_save_motion(data, f"{base_filename}_MOTION")
                    generated.append(path)
                elif template_id == "declaration":
                    path = self.generate_and_save_declaration(data, f"{base_filename}_DECLARATION")
                    generated.append(path)
                elif template_id == "notice":
                    path = self.generate_and_save_notice(data, f"{base_filename}_NOTICE")
                    generated.append(path)
                elif template_id == "cover":
                    cover_path = self.generate_cover(data)
                    if cover_path:
                        generated.append(cover_path)
                else:
                    print(f"[WARN] Unknown template: {template_id}")
            except Exception as e:
                print(f"[ERROR] Failed to generate {template_id}: {e}")
        
        print(f"\n[OK] Playlist '{playlist_name}' complete: {len(generated)} documents")
        return generated
    
    def list_templates(self) -> None:
        """Print available templates."""
        registry = self.load_registry()
        templates = registry.get("templates", {})
        
        print("\n" + "=" * 60)
        print("AVAILABLE TEMPLATES")
        print("=" * 60)
        for tid, tinfo in templates.items():
            print(f"\n  {tid}:")
            print(f"    File: {tinfo.get('file', 'N/A')}")
            print(f"    Desc: {tinfo.get('description', 'N/A')}")
        print()
    
    def list_playlists(self) -> None:
        """Print available playlists."""
        registry = self.load_registry()
        playlists = registry.get("playlists", {})
        
        print("\n" + "=" * 60)
        print("AVAILABLE PLAYLISTS")
        print("=" * 60)
        for pid, pinfo in playlists.items():
            print(f"\n  {pid}:")
            print(f"    Templates: {', '.join(pinfo.get('templates', []))}")
            print(f"    Desc: {pinfo.get('description', 'N/A')}")
        print()
    
    def list_blocks(self) -> None:
        """Print available building blocks."""
        registry = self.load_registry()
        blocks = registry.get("building_blocks", {}).get("blocks", [])
        
        print("\n" + "=" * 60)
        print("AVAILABLE BUILDING BLOCKS")
        print("=" * 60)
        for block in blocks:
            print(f"  {block['id']:30} - {block['use']}")
        print()


# =============================================================================
# CLI
# =============================================================================
def print_help():
    """Print usage help."""
    print("""
PIMP SMACK - Template Generator
================================

USAGE:
    python template_generator.py [command]

COMMANDS:
    --help, -h          Show this help
    --list-templates    List available templates
    --list-playlists    List available playlists
    --list-blocks       List available building blocks
    --demo              Generate demo documents
    
PROGRAMMATIC USAGE:
    from template_generator import TemplateGenerator
    
    gen = TemplateGenerator()
    gen.generate_and_save_motion(data, "filename")
    gen.generate_and_save_declaration(data, "filename")
    gen.generate_and_save_notice(data, "filename")
    gen.generate_playlist("full_motion_package", data, "filename")

SEE ALSO:
    CHEAT_SHEET.md              - Full documentation
    templates/TEMPLATE_REGISTRY.json - Template definitions
    templates/BUILDING_BLOCKS.xml    - XML components
""")


def run_demo(generator):
    """Generate demo documents."""
    print("\n" + "=" * 60)
    print("GENERATING DEMO DOCUMENTS")
    print("=" * 60)
    
    # Motion
    motion_data = {
        "INTRODUCTION_TEXT": "This is a sample motion introduction text.",
        "STATEMENT_OF_FACTS_TEXT": "These are the relevant facts of the case.",
        "ARGUMENT_I_TITLE": "THE COURT HAS JURISDICTION",
        "ARGUMENT_I_TEXT": "The court has jurisdiction because...",
        "ARGUMENT_II_TITLE": "THE MOTION SHOULD BE GRANTED",
        "ARGUMENT_II_TEXT": "For the reasons stated above...",
        "CONCLUSION_TEXT": "For all the foregoing reasons, Appellant respectfully requests that this Court grant the motion.",
        "DOCUMENT_TITLE": "Motion for Summary Judgment",
    }
    
    try:
        generator.generate_and_save_motion(motion_data, "DEMO_MOTION")
    except FileNotFoundError as e:
        print(f"Error: {e}")
    
    # Declaration
    declaration_data = {
        "DECLARANT_NAME": "Tyler Allen Lofall",
        "DECLARANT_NAME_CAPS": "TYLER ALLEN LOFALL",
        "FACT_1_IDENTITY": "I am the Plaintiff in this action and make this declaration based on my personal knowledge.",
        "FACT_2_RELATIONSHIP": "I have personal knowledge of all facts stated herein.",
        "FACT_3_PRIMARY": "On October 1, 2025, I filed a motion via the CM/ECF system.",
        "FACT_4_SUPPORTING": "The CM/ECF system confirmed the filing at 11:57 PM PDT.",
        "FACT_5_CONCLUSION": "Based on the foregoing, the motion was timely filed.",
    }
    
    try:
        generator.generate_and_save_declaration(declaration_data, "DEMO_DECLARATION")
    except FileNotFoundError as e:
        print(f"Error: {e}")
    
    # Notice
    notice_data = {
        "NOTICE_TITLE": "NOTICE OF MOTION",
        "NOTICE_RECIPIENTS": "All Counsel of Record",
        "NOTICE_BODY": "Appellant will move this Court for an order granting summary judgment.",
        "NOTICE_DATE": "January 15, 2026",
        "NOTICE_TIME": "9:00 AM",
        "NOTICE_LOCATION": "Courtroom 3, 9th Floor",
        "ADDITIONAL_NOTICE": "Opposition papers, if any, must be filed within 14 days of service.",
    }
    
    try:
        generator.generate_and_save_notice(notice_data, "DEMO_NOTICE")
    except FileNotFoundError as e:
        print(f"Error: {e}")
    
    print("\n[OK] Demo complete. Check output/ directory.")


if __name__ == "__main__":
    generator = TemplateGenerator()
    
    if len(sys.argv) < 2:
        print_help()
        sys.exit(0)
    
    arg = sys.argv[1].lower()
    
    if arg in ("--help", "-h"):
        print_help()
    elif arg == "--list-templates":
        generator.list_templates()
    elif arg == "--list-playlists":
        generator.list_playlists()
    elif arg == "--list-blocks":
        generator.list_blocks()
    elif arg == "--demo":
        run_demo(generator)
    else:
        print(f"Unknown command: {arg}")
        print_help()
