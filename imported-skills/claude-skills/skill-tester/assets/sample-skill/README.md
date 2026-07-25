# Sample Text Processor

A basic text processing skill that demonstrates BASIC tier requirements for the claude-skills ecosystem.

## Quick Start

```bash
# Analyze a text file
python scripts/text_processor.py analyze sample.txt

# Get JSON output
python scripts/text_processor.py analyze sample.txt --format json

# Transform text to uppercase  
python scripts/text_processor.py transform sample.txt --mode upper

# Process multiple files
python scripts/text_processor.py batch text_files/ --verbose
```

## Features

- Word count and text statistics
- Text transformations (upper, lower, title, reverse)
- Batch file processing
- JSON and human-readable output formats
- Comprehensive error handling

## Requirements

- Python 3.7 or later
- No external dependencies (standard library only)

## Usage

See [SKILL.md](SKILL.md) for comprehensive documentation and examples.

## Testing

Sample data files are provided in the `assets/` directory for testing the functionality.