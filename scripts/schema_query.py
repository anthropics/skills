#!/usr/bin/env python3
"""
Schema Query Helper - Helper functions for models to query .MASTER_SCHEMA.json

This module provides a simple API for models to retrieve information from the master schema
without having to parse JSON themselves. Prevents the "blind formatting" problem by giving
models access to known-good formatting rules and case information.

Usage:
    from schema_query import SchemaQuery
    
    sq = SchemaQuery()
    
    # Get formatting rules for a jurisdiction
    fonts = sq.get_fonts('ninth_circuit')
    margins = sq.get_margins('ninth_circuit')
    
    # Get case information
    case_info = sq.get_case_info('25-6461')
    judge = sq.get_judge('25-6461')
    
    # Get complete config for document generation
    config = sq.get_document_config('25-6461', 'cover_page')
"""

import json
from pathlib import Path
from typing import Dict, List, Any, Optional

# Base directory
BASE_DIR = Path(__file__).parent.parent
MASTER_SCHEMA_PATH = BASE_DIR / ".MASTER_SCHEMA.json"


class SchemaQuery:
    """Query interface for .MASTER_SCHEMA.json"""
    
    def __init__(self, schema_path: Path = MASTER_SCHEMA_PATH):
        self.schema_path = schema_path
        self.schema = self._load_schema()
    
    def _load_schema(self) -> Dict[str, Any]:
        """Load master schema"""
        if not self.schema_path.exists():
            raise FileNotFoundError(
                f".MASTER_SCHEMA.json not found at {self.schema_path}. "
                f"Run 'python scripts/schema_builder.py' to create it."
            )
        
        with open(self.schema_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    
    def reload(self) -> None:
        """Reload schema from disk (use after updates)"""
        self.schema = self._load_schema()
    
    # === Case Information ===
    
    def get_case_info(self, case_number: str) -> Optional[Dict[str, Any]]:
        """Get all information for a case"""
        return self.schema.get('active_cases', {}).get(case_number)
    
    def list_active_cases(self) -> List[str]:
        """List all case numbers in the schema"""
        cases = list(self.schema.get('active_cases', {}).keys())
        # Filter out metadata keys like "_comment" or "example_*"
        return [c for c in cases if not c.startswith('_') and not c.startswith('example_')]
    
    def get_judge(self, case_number: str) -> Optional[str]:
        """Get judge name for a case"""
        case = self.get_case_info(case_number)
        if case and 'judge' in case:
            return case['judge'].get('name', '')
        return None
    
    def get_parties(self, case_number: str, party_type: str = 'all') -> List[str]:
        """Get party names for a case
        
        Args:
            case_number: Case number
            party_type: 'appellants', 'appellees', or 'all'
        """
        case = self.get_case_info(case_number)
        if not case or 'parties' not in case:
            return []
        
        parties = case['parties']
        
        if party_type == 'appellants':
            return [p['name'] for p in parties.get('appellants', [])]
        elif party_type == 'appellees':
            return [p['name'] for p in parties.get('appellees', [])]
        else:
            appellants = [p['name'] for p in parties.get('appellants', [])]
            appellees = [p['name'] for p in parties.get('appellees', [])]
            return appellants + appellees
    
    def get_jurisdiction(self, case_number: str) -> Optional[str]:
        """Get jurisdiction for a case"""
        case = self.get_case_info(case_number)
        return case.get('jurisdiction') if case else None
    
    # === Jurisdiction Rules ===
    
    def get_jurisdiction_rules(self, jurisdiction: str) -> Optional[Dict[str, Any]]:
        """Get all rules for a jurisdiction"""
        return self.schema.get('jurisdiction_rules', {}).get(jurisdiction)
    
    def get_fonts(self, jurisdiction: str) -> Optional[Dict[str, Any]]:
        """Get font rules for a jurisdiction"""
        rules = self.get_jurisdiction_rules(jurisdiction)
        return rules.get('fonts') if rules else None
    
    def get_margins(self, jurisdiction: str) -> Optional[Dict[str, Any]]:
        """Get margin rules for a jurisdiction"""
        rules = self.get_jurisdiction_rules(jurisdiction)
        return rules.get('margins') if rules else None
    
    def get_spacing(self, jurisdiction: str) -> Optional[Dict[str, Any]]:
        """Get spacing rules for a jurisdiction"""
        rules = self.get_jurisdiction_rules(jurisdiction)
        return rules.get('spacing') if rules else None
    
    def get_page_limits(self, jurisdiction: str) -> Optional[Dict[str, Any]]:
        """Get page/word limits for a jurisdiction"""
        rules = self.get_jurisdiction_rules(jurisdiction)
        return rules.get('page_limits') if rules else None
    
    def get_local_rules(self, jurisdiction: str) -> Optional[Dict[str, Any]]:
        """Get local court rules for a jurisdiction"""
        rules = self.get_jurisdiction_rules(jurisdiction)
        return rules.get('local_rules') if rules else None
    
    # === Document Generation Config ===
    
    def get_document_config(self, case_number: str, document_type: str) -> Optional[Dict[str, Any]]:
        """Get complete configuration for generating a document
        
        This merges:
        1. Case information
        2. Jurisdiction formatting rules
        3. User preferences
        4. FRAP/FRCP base rules
        
        Returns everything a model needs to generate a properly formatted document.
        """
        case = self.get_case_info(case_number)
        if not case:
            return None
        
        jurisdiction = case.get('jurisdiction', '')
        
        config = {
            'document_type': document_type,
            'case': case,
            'formatting': self.get_jurisdiction_rules(jurisdiction),
            'preferences': self.schema.get('formatting_preferences', {}),
            'base_rules': self.schema.get('base_rules', {}),
            'templates': self.schema.get('document_templates', {})
        }
        
        return config
    
    # === Templates ===
    
    def get_template_path(self, document_type: str) -> Optional[str]:
        """Get template file path for a document type"""
        templates = self.schema.get('document_templates', {})
        return templates.get(document_type)
    
    # === User Profile ===
    
    def get_user_info(self) -> Dict[str, Any]:
        """Get user profile information"""
        return self.schema.get('user_profile', {})
    
    # === Learned Patterns ===
    
    def get_common_citations(self) -> List[str]:
        """Get list of commonly used citations"""
        return self.schema.get('learned_patterns', {}).get('common_citations', [])
    
    def get_standard_definitions(self) -> Dict[str, str]:
        """Get dictionary of standard legal definitions"""
        return self.schema.get('learned_patterns', {}).get('standard_definitions', {})
    
    # === Validation ===
    
    def get_required_fields(self, document_type: str) -> List[str]:
        """Get list of required fields for a document type"""
        validation_rules = self.schema.get('validation_rules', {})
        required_fields = validation_rules.get('required_fields_by_document_type', {})
        return required_fields.get(document_type, [])
    
    def is_valid_for_document(self, case_number: str, document_type: str) -> bool:
        """Check if schema has all required fields for document generation"""
        required_fields = self.get_required_fields(document_type)
        case = self.get_case_info(case_number)
        
        if not case:
            return False
        
        # Check each required field
        for field_path in required_fields:
            parts = field_path.split('.')
            current = case
            
            try:
                for part in parts:
                    current = current[part]
                
                # Check if value is empty
                if not current or (isinstance(current, str) and not current.strip()):
                    return False
            except (KeyError, TypeError):
                return False
        
        return True
    
    # === Helper Methods for Common Queries ===
    
    def format_caption(self, case_number: str) -> str:
        """Generate caption text for a case"""
        case = self.get_case_info(case_number)
        if not case:
            return ""
        
        appellants = self.get_parties(case_number, 'appellants')
        appellees = self.get_parties(case_number, 'appellees')
        
        caption = ""
        
        if appellants:
            caption += ", ".join(appellants) + ",\n"
            caption += "    Appellant" + ("s" if len(appellants) > 1 else "") + ",\n\n"
        
        caption += "v.\n\n"
        
        if appellees:
            caption += ", ".join(appellees) + ",\n"
            caption += "    Appellee" + ("s" if len(appellees) > 1 else "") + ".\n"
        
        return caption
    
    def get_court_name(self, case_number: str) -> str:
        """Get full court name for a case"""
        case = self.get_case_info(case_number)
        return case.get('court_full_name', '') if case else ''
    
    def get_filing_deadline(self, case_number: str, filing_type: str) -> Optional[str]:
        """Get deadline for a specific filing type"""
        case = self.get_case_info(case_number)
        if not case or 'key_dates' not in case:
            return None
        
        deadline_map = {
            'opening_brief': 'briefing_deadline',
            'reply_brief': 'reply_deadline',
            'motion': 'motion_deadline'
        }
        
        deadline_key = deadline_map.get(filing_type, '')
        return case['key_dates'].get(deadline_key)


# === Convenience functions for quick queries ===

def get_fonts_for_case(case_number: str) -> Optional[Dict[str, Any]]:
    """Quick helper: Get fonts for a case's jurisdiction"""
    sq = SchemaQuery()
    jurisdiction = sq.get_jurisdiction(case_number)
    return sq.get_fonts(jurisdiction) if jurisdiction else None


def get_margins_for_case(case_number: str) -> Optional[Dict[str, Any]]:
    """Quick helper: Get margins for a case's jurisdiction"""
    sq = SchemaQuery()
    jurisdiction = sq.get_jurisdiction(case_number)
    return sq.get_margins(jurisdiction) if jurisdiction else None


def validate_before_generation(case_number: str, document_type: str) -> bool:
    """Quick helper: Validate schema before document generation"""
    sq = SchemaQuery()
    return sq.is_valid_for_document(case_number, document_type)


# === Example Usage ===

if __name__ == '__main__':
    """Example usage for models"""
    
    print("=== Schema Query Helper Examples ===\n")
    
    sq = SchemaQuery()
    
    # List all cases
    print("Active cases:")
    for case_num in sq.list_active_cases():
        print(f"  - {case_num}")
    
    # Get case info (use first case as example)
    cases = sq.list_active_cases()
    if cases:
        case_num = cases[0]
        print(f"\nCase {case_num}:")
        print(f"  Judge: {sq.get_judge(case_num)}")
        print(f"  Jurisdiction: {sq.get_jurisdiction(case_num)}")
        print(f"  Appellants: {', '.join(sq.get_parties(case_num, 'appellants'))}")
        print(f"  Appellees: {', '.join(sq.get_parties(case_num, 'appellees'))}")
        
        # Get formatting rules
        jurisdiction = sq.get_jurisdiction(case_num)
        if jurisdiction:
            print(f"\nFormatting for {jurisdiction}:")
            fonts = sq.get_fonts(jurisdiction)
            if fonts:
                print(f"  Font: {fonts.get('body')} {fonts.get('size')}pt")
            margins = sq.get_margins(jurisdiction)
            if margins:
                print(f"  Margins: {margins.get('top')}\" (all sides)")
        
        # Get complete document config
        print(f"\nValidation for cover_page:")
        is_valid = sq.is_valid_for_document(case_num, 'cover_page')
        print(f"  Ready to generate: {is_valid}")
        
        if is_valid:
            config = sq.get_document_config(case_num, 'cover_page')
            print(f"  Config sections: {', '.join(config.keys())}")
    else:
        print("\nNo active cases found in schema.")
        print("Run 'python scripts/schema_builder.py' to populate from existing files.")
