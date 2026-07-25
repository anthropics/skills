# Sample Text Processor

---

**Name**: sample-text-processor
**Tier**: BASIC
**Category**: Text Processing
**Dependencies**: None (Python Standard Library Only)
**Author**: Claude Skills Engineering Team
**Version**: 1.0.0
**Last Updated**: 2026-02-16

---

## Description

The Sample Text Processor is a simple skill designed to demonstrate the basic structure and functionality expected in the claude-skills ecosystem. This skill provides fundamental text processing capabilities including word counting, character analysis, and basic text transformations.

This skill serves as a reference implementation for BASIC tier requirements and can be used as a template for creating new skills. It demonstrates proper file structure, documentation standards, and implementation patterns that align with ecosystem best practices.

The skill processes text files and provides statistics and transformations in both human-readable and JSON formats, showcasing the dual output requirement for skills in the claude-skills repository.

## Features

### Core Functionality
- **Word Count Analysis**: Count total words, unique words, and word frequency
- **Character Statistics**: Analyze character count, line count, and special characters
- **Text Transformations**: Convert text to uppercase, lowercase, or title case
- **File Processing**: Process single text files or batch process directories
- **Dual Output Formats**: Generate results in both JSON and human-readable formats

### Technical Features
- Command-line interface with comprehensive argument parsing
- Error handling for common file and processing issues
- Progress reporting for batch operations
- Configurable output formatting and verbosity levels
- Cross-platform compatibility with standard library only dependencies

## Usage

### Basic Text Analysis
```bash
python text_processor.py analyze document.txt
python text_processor.py analyze document.txt --output results.json
```

### Text Transformation
```bash
python text_processor.py transform document.txt --mode uppercase
python text_processor.py transform document.txt --mode title --output transformed.txt
```

### Batch Processing
```bash
python text_processor.py batch text_files/ --output results/
python text_processor.py batch text_files/ --format json --output batch_results.json
```

## Examples

### Example 1: Basic Word Count
```bash
$ python text_processor.py analyze sample.txt
=== TEXT ANALYSIS RESULTS ===
File: sample.txt
Total words: 150
Unique words: 85
Total characters: 750
Lines: 12
Most frequent word: "the" (8 occurrences)
```

### Example 2: JSON Output
```bash
$ python text_processor.py analyze sample.txt --format json
{
  "file": "sample.txt",
  "statistics": {
    "total_words": 150,
    "unique_words": 85,
    "total_characters": 750,
    "lines": 12,
    "most_frequent": {
      "word": "the",
      "count": 8
    }
  }
}
```

### Example 3: Text Transformation
```bash
$ python text_processor.py transform sample.txt --mode title
Original: "hello world from the text processor"
Transformed: "Hello World From The Text Processor"
```

## Installation

This skill requires only Python 3.7 or later with the standard library. No external dependencies are required.

1. Clone or download the skill directory
2. Navigate to the scripts directory
3. Run the text processor directly with Python

```bash
cd scripts/
python text_processor.py --help
```

## Configuration

The text processor supports various configuration options through command-line arguments:

- `--format`: Output format (json, text)
- `--verbose`: Enable verbose output and progress reporting
- `--output`: Specify output file or directory
- `--encoding`: Specify text file encoding (default: utf-8)

## Architecture

The skill follows a simple modular architecture:

- **TextProcessor Class**: Core processing logic and statistics calculation
- **OutputFormatter Class**: Handles dual output format generation
- **FileManager Class**: Manages file I/O operations and batch processing
- **CLI Interface**: Command-line argument parsing and user interaction

## Error Handling

The skill includes comprehensive error handling for:
- File not found or permission errors
- Invalid encoding or corrupted text files
- Memory limitations for very large files
- Output directory creation and write permissions
- Invalid command-line arguments and parameters

## Performance Considerations

- Efficient memory usage for large text files through streaming
- Optimized word counting using dictionary lookups
- Batch processing with progress reporting for large datasets
- Configurable encoding detection for international text

## Contributing

This skill serves as a reference implementation and contributions are welcome to demonstrate best practices:

1. Follow PEP 8 coding standards
2. Include comprehensive docstrings
3. Add test cases with sample data
4. Update documentation for any new features
5. Ensure backward compatibility

## Limitations

As a BASIC tier skill, some advanced features are intentionally omitted:
- Complex text analysis (sentiment, language detection)
- Advanced file format support (PDF, Word documents)
- Database integration or external API calls
- Parallel processing for very large datasets

This skill demonstrates the essential structure and quality standards required for BASIC tier skills in the claude-skills ecosystem while remaining simple and focused on core functionality.