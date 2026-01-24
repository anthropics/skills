#!/usr/bin/env python3
"""
Citation Formatter Script for Research Skills

This script formats citations in various academic styles and generates
bibliographies from source information.
"""

import json
import re
from datetime import datetime
from typing import List, Dict, Optional

class CitationFormatter:
    def __init__(self):
        self.citation_styles = {
            'apa': self._format_apa,
            'mla': self._format_mla,
            'chicago': self._format_chicago,
            'ieee': self._format_ieee,
            'harvard': self._format_harvard
        }
        
        self.source_types = {
            'journal_article': self._format_journal_article,
            'book': self._format_book,
            'webpage': self._format_webpage,
            'report': self._format_report,
            'thesis': self._format_thesis
        }

    def format_citation(self, source: Dict, style: str = 'apa') -> str:
        """Format a single citation in specified style"""
        if style not in self.citation_styles:
            raise ValueError(f"Unsupported citation style: {style}")
        
        source_type = source.get('type', 'webpage')
        if source_type not in self.source_types:
            raise ValueError(f"Unsupported source type: {source_type}")
        
        formatter = self.source_types[source_type]
        style_formatter = self.citation_styles[style]
        
        return style_formatter(formatter(source))

    def format_bibliography(self, sources: List[Dict], style: str = 'apa', 
                          title: str = "References") -> str:
        """Format complete bibliography"""
        if not sources:
            return f"## {title}\n\nNo sources provided."
        
        # Sort sources alphabetically by author
        sorted_sources = sorted(sources, key=lambda x: x.get('author', '').lower())
        
        bibliography = f"## {title}\n\n"
        
        for i, source in enumerate(sorted_sources, 1):
            try:
                citation = self.format_citation(source, style)
                bibliography += f"{i}. {citation}\n\n"
            except Exception as e:
                bibliography += f"{i}. [Error formatting citation: {str(e)}]\n\n"
        
        return bibliography

    def _format_journal_article(self, source: Dict) -> Dict:
        """Extract and format journal article components"""
        return {
            'author': source.get('author', ''),
            'year': source.get('year', ''),
            'title': source.get('title', ''),
            'journal': source.get('journal', ''),
            'volume': source.get('volume', ''),
            'issue': source.get('issue', ''),
            'pages': source.get('pages', ''),
            'doi': source.get('doi', ''),
            'url': source.get('url', '')
        }

    def _format_book(self, source: Dict) -> Dict:
        """Extract and format book components"""
        return {
            'author': source.get('author', ''),
            'year': source.get('year', ''),
            'title': source.get('title', ''),
            'publisher': source.get('publisher', ''),
            'location': source.get('location', ''),
            'edition': source.get('edition', ''),
            'isbn': source.get('isbn', ''),
            'url': source.get('url', '')
        }

    def _format_webpage(self, source: Dict) -> Dict:
        """Extract and format webpage components"""
        return {
            'author': source.get('author', ''),
            'year': source.get('year', ''),
            'title': source.get('title', ''),
            'site_name': source.get('site_name', ''),
            'url': source.get('url', ''),
            'access_date': source.get('access_date', datetime.now().strftime('%Y, %m %d'))
        }

    def _format_report(self, source: Dict) -> Dict:
        """Extract and format report components"""
        return {
            'author': source.get('author', ''),
            'year': source.get('year', ''),
            'title': source.get('title', ''),
            'report_number': source.get('report_number', ''),
            'institution': source.get('institution', ''),
            'location': source.get('location', ''),
            'url': source.get('url', '')
        }

    def _format_thesis(self, source: Dict) -> Dict:
        """Extract and format thesis components"""
        return {
            'author': source.get('author', ''),
            'year': source.get('year', ''),
            'title': source.get('title', ''),
            'degree': source.get('degree', ''),
            'institution': source.get('institution', ''),
            'location': source.get('location', ''),
            'url': source.get('url', '')
        }

    # APA Formatting
    def _format_apa(self, components: Dict) -> str:
        """Format citation in APA 7th edition style"""
        if components.get('journal'):
            # Journal article
            citation = f"{components['author']}. ({components['year']}). {components['title']}. *{components['journal']}*"
            if components.get('volume'):
                citation += f", *{components['volume']}*"
                if components.get('issue'):
                    citation += f"({components['issue']})"
                if components.get('pages'):
                    citation += f", {components['pages']}"
            if components.get('doi'):
                citation += f". https://doi.org/{components['doi']}"
            elif components.get('url'):
                citation += f". {components['url']}"
        elif components.get('publisher'):
            # Book
            citation = f"{components['author']}. ({components['year']}). *{components['title']}*."
            if components.get('edition'):
                citation += f" ({components['edition']})."
            citation += f" {components['publisher']}."
            if components.get('location'):
                citation += f" {components['location']}."
        else:
            # Webpage or other
            citation = f"{components['author']}. ({components['year']}). {components['title']}."
            if components.get('site_name'):
                citation += f" {components['site_name']}."
            citation += f" {components['url']}"
        
        return citation

    # MLA Formatting
    def _format_mla(self, components: Dict) -> str:
        """Format citation in MLA 9th edition style"""
        if components.get('journal'):
            # Journal article
            citation = f"{components['author']}. \"{components['title']}.\" *{components['journal']}*"
            if components.get('volume'):
                citation += f", vol. {components['volume']}"
                if components.get('issue'):
                    citation += f", no. {components['issue']}"
            if components.get('year'):
                citation += f", {components['year']}"
            if components.get('pages'):
                citation += f", pp. {components['pages']}"
            if components.get('doi'):
                citation += f", doi:{components['doi']}"
        elif components.get('publisher'):
            # Book
            citation = f"{components['author']}. *{components['title']}*."
            if components.get('edition'):
                citation += f" {components['edition']}."
            citation += f" {components['publisher']}, {components['year']}."
        else:
            # Webpage
            citation = f"{components['author']}. \"{components['title']}.\" *{components['site_name']}*, {components['year']}, {components['url']}."
        
        return citation

    # Chicago Formatting
    def _format_chicago(self, components: Dict) -> str:
        """Format citation in Chicago Manual of Style (author-date)"""
        if components.get('journal'):
            # Journal article
            citation = f"{components['author']}. {components['year']}. \"{components['title']}.\" *{components['journal']}*"
            if components.get('volume'):
                citation += f" {components['volume']}"
                if components.get('issue'):
                    citation += f", no. {components['issue']}"
                if components.get('pages'):
                    citation += f": {components['pages']}"
        elif components.get('publisher'):
            # Book
            citation = f"{components['author']}. {components['year']}. *{components['title']}*."
            if components.get('edition'):
                citation += f" {components['edition']}."
            citation += f" {components['location']}: {components['publisher']}."
        else:
            # Webpage
            citation = f"{components['author']}. {components['year']}. \"{components['title']}.\" {components['site_name']}. Accessed {components['access_date']}. {components['url']}."
        
        return citation

    # IEEE Formatting
    def _format_ieee(self, components: Dict) -> str:
        """Format citation in IEEE style"""
        if components.get('journal'):
            # Journal article
            citation = f"[1] {components['author']}, \"{components['title']},\" *{components['journal']}*"
            if components.get('volume'):
                citation += f", vol. {components['volume']}"
                if components.get('issue'):
                    citation += f", no. {components['issue']}"
                if components.get('pages'):
                    citation += f", pp. {components['pages']}"
            citation += f", {components['year']}."
            if components.get('doi'):
                citation += f" doi: {components['doi']}"
        else:
            # General format for other types
            citation = f"[1] {components['author']}, \"{components['title']},\""
            if components.get('publisher'):
                citation += f" {components['publisher']},"
            citation += f" {components['year']}."
        
        return citation

    # Harvard Formatting
    def _format_harvard(self, components: Dict) -> str:
        """Format citation in Harvard style"""
        if components.get('journal'):
            # Journal article
            citation = f"{components['author']} ({components['year']}) '{components['title']}', *{components['journal']}*"
            if components.get('volume'):
                citation += f", {components['volume']}"
                if components.get('issue'):
                    citation += f"({components['issue']})"
                if components.get('pages'):
                    citation += f", pp. {components['pages']}"
        elif components.get('publisher'):
            # Book
            citation = f"{components['author']} ({components['year']}) *{components['title']}*."
            if components.get('edition'):
                citation += f" {components['edition']}."
            citation += f" {components['location']}: {components['publisher']}."
        else:
            # Webpage
            citation = f"{components['author']} ({components['year']}) '{components['title']}', {components['site_name']}. Available at: {components['url']} (Accessed: {components['access_date']})."
        
        return citation

    def generate_in_text_citations(self, sources: List[Dict], style: str = 'apa') -> Dict[str, str]:
        """Generate in-text citations for sources"""
        in_text = {}
        
        for i, source in enumerate(sources):
            author = source.get('author', 'Anonymous').split(',')[0] + ' et al.' if ',' in source.get('author', '') else source.get('author', 'Anonymous')
            year = source.get('year', 'n.d.')
            
            if style == 'apa':
                in_text[f"source_{i}"] = f"({author}, {year})"
            elif style == 'mla':
                in_text[f"source_{i}"] = f"({author} {year})"
            elif style == 'chicago':
                in_text[f"source_{i}"] = f"({author} {year})"
            elif style == 'harvard':
                in_text[f"source_{i}"] = f"({author}, {year})"
            elif style == 'ieee':
                in_text[f"source_{i}"] = f"[{i+1}]"
        
        return in_text

def main():
    """Command line interface for citation formatting"""
    import sys
    import argparse
    
    parser = argparse.ArgumentParser(description='Format citations in various academic styles')
    parser.add_argument('input_file', help='JSON file containing source information')
    parser.add_argument('--style', default='apa', choices=['apa', 'mla', 'chicago', 'ieee', 'harvard'],
                       help='Citation style to use')
    parser.add_argument('--output', help='Output file for formatted bibliography')
    parser.add_argument('--title', default='References', help='Title for bibliography')
    
    args = parser.parse_args()
    
    try:
        with open(args.input_file, 'r', encoding='utf-8') as f:
            sources_data = json.load(f)
        
        formatter = CitationFormatter()
        
        # Handle different input formats
        if isinstance(sources_data, list):
            sources = sources_data
        elif isinstance(sources_data, dict) and 'sources' in sources_data:
            sources = sources_data['sources']
        else:
            print("Error: Input JSON must contain a list of sources or a dict with 'sources' key")
            sys.exit(1)
        
        # Generate bibliography
        bibliography = formatter.format_bibliography(sources, args.style, args.title)
        
        # Generate in-text citations
        in_text = formatter.generate_in_text_citations(sources, args.style)
        
        # Combine output
        output = bibliography + "\n## In-Text Citations\n\n"
        for key, citation in in_text.items():
            output += f"- {key}: {citation}\n"
        
        # Save or print output
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(output)
            print(f"Bibliography saved to: {args.output}")
        else:
            print(output)
    
    except FileNotFoundError:
        print(f"Error: Input file '{args.input_file}' not found")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in input file - {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()