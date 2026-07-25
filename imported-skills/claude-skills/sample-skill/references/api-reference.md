# Text Processor API Reference

## Classes

### TextProcessor

Main class for text processing operations.

#### `__init__(self, encoding: str = 'utf-8')`

Initialize the text processor with specified encoding.

**Parameters:**
- `encoding` (str): Character encoding for file operations. Default: 'utf-8'

#### `analyze_text(self, text: str) -> Dict[str, Any]`

Analyze text and return comprehensive statistics.

**Parameters:**
- `text` (str): Text content to analyze

**Returns:**
- `dict`: Statistics including word count, character count, lines, most frequent word

**Example:**
```python
processor = TextProcessor()
stats = processor.analyze_text("Hello world")
# Returns: {'total_words': 2, 'unique_words': 2, ...}
```

#### `transform_text(self, text: str, mode: str) -> str`

Transform text according to specified mode.

**Parameters:**
- `text` (str): Text to transform
- `mode` (str): Transformation mode ('upper', 'lower', 'title', 'reverse')

**Returns:**
- `str`: Transformed text

**Raises:**
- `ValueError`: If mode is not supported

### OutputFormatter

Static methods for output formatting.

#### `format_json(data: Dict[str, Any]) -> str`

Format data as JSON string.

#### `format_human_readable(data: Dict[str, Any]) -> str`

Format data as human-readable text.

### FileManager

Handles file operations and batch processing.

#### `find_text_files(self, directory: str) -> List[str]`

Find all text files in a directory recursively.

**Supported Extensions:**
- .txt
- .md
- .rst
- .csv
- .log

## Command Line Interface

### Commands

#### `analyze`
Analyze text file statistics.

```bash
python text_processor.py analyze <file> [options]
```

#### `transform`
Transform text file content.

```bash
python text_processor.py transform <file> --mode <mode> [options]
```

#### `batch`
Process multiple files in a directory.

```bash
python text_processor.py batch <directory> [options]
```

### Global Options

- `--format {json,text}`: Output format (default: text)
- `--output FILE`: Output file path (default: stdout)
- `--encoding ENCODING`: Text file encoding (default: utf-8)
- `--verbose`: Enable verbose output

## Error Handling

The text processor handles several error conditions:

- **FileNotFoundError**: When input file doesn't exist
- **UnicodeDecodeError**: When file encoding doesn't match specified encoding
- **PermissionError**: When file access is denied
- **ValueError**: When invalid transformation mode is specified

All errors are reported to stderr with descriptive messages.