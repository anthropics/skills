#!/usr/bin/env python3
"""
EXACT QUOTE LOADER
Loads quotes EXACTLY as they appear - NO REWORDING
Pulls from ECF_QUOTES.csv and evidence_pool.json
"""

import csv
import json
from pathlib import Path
from typing import Dict, List, Optional


class ExactQuoteLoader:
    """
    Load exact quotes from your data files.
    NEVER rewrites or paraphrases anything.
    """
    
    def __init__(self, data_dir: str = None):
        self.data_dir = Path(data_dir) if data_dir else Path(__file__).parent / "data"
        self.quotes_cache: Dict[str, List[Dict]] = {}
        
    def load_ecf_quotes(self, csv_path: str = None) -> List[Dict]:
        """
        Load exact quotes from ECF_QUOTES.csv
        Returns raw data - NO MODIFICATION
        """
        if csv_path:
            path = Path(csv_path)
        else:
            # Default location
            path = Path("d:/SKilz/9th_Arch_Angel/9th_Cir_Brief/ECF_QUOTES.csv")
        
        if not path.exists():
            print(f"WARNING: ECF quotes file not found: {path}")
            return []
        
        quotes = []
        with open(path, 'r', encoding='utf-8') as f:
            # Each line is a JSON object in quotes
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    # Remove outer quotes if present
                    if line.startswith('"') and line.endswith('"'):
                        line = line[1:-1]
                    # Unescape inner quotes
                    line = line.replace('""', '"')
                    data = json.loads(line)
                    quotes.append(data)
                except json.JSONDecodeError:
                    continue
        
        self.quotes_cache['ecf'] = quotes
        return quotes
    
    def get_quote_by_ecf_page(self, ecf: str, page: str) -> List[Dict]:
        """Get exact quotes from specific ECF document and page"""
        if 'ecf' not in self.quotes_cache:
            self.load_ecf_quotes()
        
        return [
            q for q in self.quotes_cache.get('ecf', [])
            if q.get('ecf') == ecf and q.get('page') == page
        ]
    
    def get_quotes_by_matter(self, matter_type: str) -> List[Dict]:
        """Get quotes by matter_of type (Fact, Law, etc.)"""
        if 'ecf' not in self.quotes_cache:
            self.load_ecf_quotes()
        
        return [
            q for q in self.quotes_cache.get('ecf', [])
            if q.get('matter_of', '').lower() == matter_type.lower()
        ]
    
    def get_quotes_by_position(self, position: str) -> List[Dict]:
        """Get quotes by position (Positive, Negative, Indifferent)"""
        if 'ecf' not in self.quotes_cache:
            self.load_ecf_quotes()
        
        return [
            q for q in self.quotes_cache.get('ecf', [])
            if q.get('position', '').lower() == position.lower()
        ]
    
    def load_evidence_pool(self) -> Dict:
        """Load evidence pool - EXACT as stored"""
        path = self.data_dir / "evidence_pool.json"
        if path.exists():
            with open(path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {}
    
    def get_fact_exact(self, fact_id: str) -> Optional[Dict]:
        """Get a fact EXACTLY as stored - no modification"""
        pool = self.load_evidence_pool()
        for fact in pool.get('facts', []):
            if fact.get('id') == fact_id:
                return fact
        return None
    
    def format_for_brief(self, quote: Dict) -> str:
        """
        Format quote for insertion into brief.
        EXACT QUOTE with citation - nothing added or removed.
        """
        text = quote.get('quoted_point', quote.get('statement', ''))
        ecf = quote.get('ecf', '')
        page = quote.get('page', '')
        
        # Just the quote with citation
        if ecf and page:
            return f'"{text}" (ECF {ecf} at {page}.)'
        elif ecf:
            return f'"{text}" (ECF {ecf}.)'
        else:
            return f'"{text}"'
    
    def export_quotes_for_section(self, ecf_numbers: List[str], output_path: str = None) -> str:
        """
        Export exact quotes for specific ECF documents.
        Returns text ready to paste - no AI processing.
        """
        if 'ecf' not in self.quotes_cache:
            self.load_ecf_quotes()
        
        output = []
        for ecf in ecf_numbers:
            quotes = [q for q in self.quotes_cache.get('ecf', []) if q.get('ecf') == ecf]
            if quotes:
                output.append(f"\n=== ECF {ecf} ===\n")
                for q in quotes:
                    output.append(self.format_for_brief(q))
                    output.append("")
        
        text = '\n'.join(output)
        
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(text)
            print(f"✓ Exported to {output_path}")
        
        return text


def main():
    """Test loading quotes"""
    loader = ExactQuoteLoader()
    
    print("\n" + "="*60)
    print("EXACT QUOTE LOADER")
    print("="*60)
    
    quotes = loader.load_ecf_quotes()
    print(f"\nLoaded {len(quotes)} quotes from ECF_QUOTES.csv")
    
    # Show breakdown
    by_ecf = {}
    for q in quotes:
        ecf = q.get('ecf', 'unknown')
        by_ecf[ecf] = by_ecf.get(ecf, 0) + 1
    
    print("\nQuotes by ECF document:")
    for ecf, count in sorted(by_ecf.items()):
        print(f"  ECF {ecf}: {count} quotes")
    
    # Show matters
    by_matter = {}
    for q in quotes:
        matter = q.get('matter_of', 'unknown')
        by_matter[matter] = by_matter.get(matter, 0) + 1
    
    print("\nQuotes by type:")
    for matter, count in by_matter.items():
        print(f"  {matter}: {count}")


if __name__ == "__main__":
    main()
