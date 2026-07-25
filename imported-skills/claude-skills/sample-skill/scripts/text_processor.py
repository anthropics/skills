#!/usr/bin/env python3
"""
Sample Text Processor - Basic text analysis and transformation tool

This script demonstrates the basic structure and functionality expected in 
BASIC tier skills. It provides text processing capabilities with proper
argument parsing, error handling, and dual output formats.

Usage:
    python text_processor.py analyze <file> [options]
    python text_processor.py transform <file> --mode <mode> [options]
    python text_processor.py batch <directory> [options]

Author: Claude Skills Engineering Team
Version: 1.0.0
Dependencies: Python Standard Library Only
"""

import argparse
import json
import os
import sys
from collections import Counter
from pathlib import Path
from typing import Dict, List, Any, Optional


class TextProcessor:
    """Core text processing functionality"""
    
    def __init__(self, encoding: str = 'utf-8'):
        self.encoding = encoding
        
    def analyze_text(self, text: str) -> Dict[str, Any]:
        """Analyze text and return statistics"""
        lines = text.split('\n')
        words = text.lower().split()
        
        # Calculate basic statistics
        stats = {
            'total_words': len(words),
            'unique_words': len(set(words)),
            'total_characters': len(text),
            'lines': len(lines),
            'average_word_length': sum(len(word) for word in words) / len(words) if words else 0
        }
        
        # Find most frequent word
        if words:
            word_counts = Counter(words)
            most_common = word_counts.most_common(1)[0]
            stats['most_frequent'] = {
                'word': most_common[0],
                'count': most_common[1]
            }
        else:
            stats['most_frequent'] = {'word': '', 'count': 0}
            
        return stats
        
    def transform_text(self, text: str, mode: str) -> str:
        """Transform text according to specified mode"""
        if mode == 'upper':
            return text.upper()
        elif mode == 'lower':
            return text.lower()
        elif mode == 'title':
            return text.title()
        elif mode == 'reverse':
            return text[::-1]
        else:
            raise ValueError(f"Unknown transformation mode: {mode}")
            
    def process_file(self, file_path: str) -> Dict[str, Any]:
        """Process a single text file"""
        try:
            with open(file_path, 'r', encoding=self.encoding) as file:
                content = file.read()
                
            stats = self.analyze_text(content)
            stats['file'] = file_path
            stats['file_size'] = os.path.getsize(file_path)
            
            return stats
            
        except FileNotFoundError:
            raise FileNotFoundError(f"File not found: {file_path}")
        except UnicodeDecodeError:
            raise UnicodeDecodeError(f"Cannot decode file with {self.encoding} encoding: {file_path}")
        except PermissionError:
            raise PermissionError(f"Permission denied accessing file: {file_path}")


class OutputFormatter:
    """Handles dual output format generation"""
    
    @staticmethod
    def format_json(data: Dict[str, Any]) -> str:
        """Format data as JSON"""
        return json.dumps(data, indent=2, ensure_ascii=False)
        
    @staticmethod
    def format_human_readable(data: Dict[str, Any]) -> str:
        """Format data as human-readable text"""
        lines = []
        lines.append("=== TEXT ANALYSIS RESULTS ===")
        lines.append(f"File: {data.get('file', 'Unknown')}")
        lines.append(f"File size: {data.get('file_size', 0)} bytes")
        lines.append(f"Total words: {data.get('total_words', 0)}")
        lines.append(f"Unique words: {data.get('unique_words', 0)}")
        lines.append(f"Total characters: {data.get('total_characters', 0)}")
        lines.append(f"Lines: {data.get('lines', 0)}")
        lines.append(f"Average word length: {data.get('average_word_length', 0):.1f}")
        
        most_frequent = data.get('most_frequent', {})
        lines.append(f"Most frequent word: \"{most_frequent.get('word', '')}\" ({most_frequent.get('count', 0)} occurrences)")
        
        return "\n".join(lines)


class FileManager:
    """Manages file I/O operations and batch processing"""
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        
    def log_verbose(self, message: str):
        """Log verbose message if verbose mode enabled"""
        if self.verbose:
            print(f"[INFO] {message}", file=sys.stderr)
            
    def find_text_files(self, directory: str) -> List[str]:
        """Find all text files in directory"""
        text_extensions = {'.txt', '.md', '.rst', '.csv', '.log'}
        text_files = []
        
        try:
            for file_path in Path(directory).rglob('*'):
                if file_path.is_file() and file_path.suffix.lower() in text_extensions:
                    text_files.append(str(file_path))
                    
        except PermissionError:
            raise PermissionError(f"Permission denied accessing directory: {directory}")
            
        return text_files
        
    def write_output(self, content: str, output_path: Optional[str] = None):
        """Write content to file or stdout"""
        if output_path:
            try:
                # Create directory if needed
                output_dir = os.path.dirname(output_path)
                if output_dir and not os.path.exists(output_dir):
                    os.makedirs(output_dir)
                    
                with open(output_path, 'w', encoding='utf-8') as file:
                    file.write(content)
                    
                self.log_verbose(f"Output written to: {output_path}")
                
            except PermissionError:
                raise PermissionError(f"Permission denied writing to: {output_path}")
        else:
            print(content)


def analyze_command(args: argparse.Namespace) -> int:
    """Handle analyze command"""
    try:
        processor = TextProcessor(args.encoding)
        file_manager = FileManager(args.verbose)
        
        file_manager.log_verbose(f"Analyzing file: {args.file}")
        
        # Process the file
        results = processor.process_file(args.file)
        
        # Format output
        if args.format == 'json':
            output = OutputFormatter.format_json(results)
        else:
            output = OutputFormatter.format_human_readable(results)
            
        # Write output
        file_manager.write_output(output, args.output)
        
        return 0
        
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except UnicodeDecodeError as e:
        print(f"Error: {e}", file=sys.stderr)
        print(f"Try using --encoding option with different encoding", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def transform_command(args: argparse.Namespace) -> int:
    """Handle transform command"""
    try:
        processor = TextProcessor(args.encoding)
        file_manager = FileManager(args.verbose)
        
        file_manager.log_verbose(f"Transforming file: {args.file}")
        
        # Read and transform the file
        with open(args.file, 'r', encoding=args.encoding) as file:
            content = file.read()
            
        transformed = processor.transform_text(content, args.mode)
        
        # Write transformed content
        file_manager.write_output(transformed, args.output)
        
        return 0
        
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def batch_command(args: argparse.Namespace) -> int:
    """Handle batch command"""
    try:
        processor = TextProcessor(args.encoding)
        file_manager = FileManager(args.verbose)
        
        file_manager.log_verbose(f"Finding text files in: {args.directory}")
        
        # Find all text files
        text_files = file_manager.find_text_files(args.directory)
        
        if not text_files:
            print(f"No text files found in directory: {args.directory}", file=sys.stderr)
            return 1
            
        file_manager.log_verbose(f"Found {len(text_files)} text files")
        
        # Process all files
        all_results = []
        for i, file_path in enumerate(text_files, 1):
            try:
                file_manager.log_verbose(f"Processing {i}/{len(text_files)}: {file_path}")
                results = processor.process_file(file_path)
                all_results.append(results)
            except Exception as e:
                print(f"Warning: Failed to process {file_path}: {e}", file=sys.stderr)
                continue
                
        if not all_results:
            print("Error: No files could be processed successfully", file=sys.stderr)
            return 1
            
        # Format batch results
        batch_summary = {
            'total_files': len(all_results),
            'total_words': sum(r.get('total_words', 0) for r in all_results),
            'total_characters': sum(r.get('total_characters', 0) for r in all_results),
            'files': all_results
        }
        
        if args.format == 'json':
            output = OutputFormatter.format_json(batch_summary)
        else:
            lines = []
            lines.append("=== BATCH PROCESSING RESULTS ===")
            lines.append(f"Total files processed: {batch_summary['total_files']}")
            lines.append(f"Total words across all files: {batch_summary['total_words']}")
            lines.append(f"Total characters across all files: {batch_summary['total_characters']}")
            lines.append("")
            lines.append("Individual file results:")
            for result in all_results:
                lines.append(f"  {result['file']}: {result['total_words']} words")
            output = "\n".join(lines)
            
        # Write output
        file_manager.write_output(output, args.output)
        
        return 0
        
    except PermissionError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


def main():
    """Main entry point with argument parsing"""
    parser = argparse.ArgumentParser(
        description="Sample Text Processor - Basic text analysis and transformation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  Analysis:
    python text_processor.py analyze document.txt
    python text_processor.py analyze document.txt --format json --output results.json
  
  Transformation:
    python text_processor.py transform document.txt --mode upper
    python text_processor.py transform document.txt --mode title --output transformed.txt
  
  Batch processing:
    python text_processor.py batch text_files/ --verbose
    python text_processor.py batch text_files/ --format json --output batch_results.json

Transformation modes:
  upper   - Convert to uppercase
  lower   - Convert to lowercase  
  title   - Convert to title case
  reverse - Reverse the text
        """
    )
    
    parser.add_argument('--format', 
                       choices=['json', 'text'], 
                       default='text',
                       help='Output format (default: text)')
    parser.add_argument('--output', 
                       help='Output file path (default: stdout)')
    parser.add_argument('--encoding', 
                       default='utf-8',
                       help='Text file encoding (default: utf-8)')
    parser.add_argument('--verbose', 
                       action='store_true',
                       help='Enable verbose output')
                       
    subparsers = parser.add_subparsers(dest='command', help='Available commands')
    
    # Analyze subcommand
    analyze_parser = subparsers.add_parser('analyze', help='Analyze text file statistics')
    analyze_parser.add_argument('file', help='Text file to analyze')
    
    # Transform subcommand  
    transform_parser = subparsers.add_parser('transform', help='Transform text file')
    transform_parser.add_argument('file', help='Text file to transform')
    transform_parser.add_argument('--mode', 
                                 required=True,
                                 choices=['upper', 'lower', 'title', 'reverse'],
                                 help='Transformation mode')
    
    # Batch subcommand
    batch_parser = subparsers.add_parser('batch', help='Process multiple files')
    batch_parser.add_argument('directory', help='Directory containing text files')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return 1
    
    try:
        if args.command == 'analyze':
            return analyze_command(args)
        elif args.command == 'transform':
            return transform_command(args)
        elif args.command == 'batch':
            return batch_command(args)
        else:
            print(f"Unknown command: {args.command}", file=sys.stderr)
            return 1
            
    except KeyboardInterrupt:
        print("\nOperation interrupted by user", file=sys.stderr)
        return 130
    except Exception as e:
        print(f"Unexpected error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())