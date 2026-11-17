# Ninth Circuit Declaration Skill

This skill generates properly formatted Declarations for the Ninth Circuit Court of Appeals.

## Features
- **Strict Formatting**: Uses `styles.json` to enforce California FB 14pt, proper margins, and line spacing.
- **Automated Structure**: Generates the caption, body, verification, and signature block.

## Usage

### 1. Configure
Edit `examples/config.json` with your case details and declaration text.

### 2. Build
Run the build script:
```bash
python src/build.py examples/config.json
```

## File Structure
- `src/`: Python source code
  - `generator.py`: Creates the DOCX template
  - `build.py`: Orchestrates the generation workflow
- `templates/`: Stores generated templates
- `examples/`: Example configurations
- `styles.json`: Strict style definitions
