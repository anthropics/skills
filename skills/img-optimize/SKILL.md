---
name: img-optimize
description: "Optimize images before reading to reduce token cost and avoid API limits. Auto-resizes to optimal dimensions or extracts text via OCR. Usage: /img <files|--dir> [--ocr] [--lang kor]"
license: MIT - Complete terms in LICENSE.txt
---

# Image Optimizer for Claude Code

Optimize images before reading to avoid API limits and reduce token cost.

## Usage

```
/img screenshot.png                    # Resize then read
/img --dir ./screenshots               # Process entire directory
/img --ocr screenshot.png              # Extract text via OCR
/img --ocr --lang kor image.png        # Korean OCR
/img --ocr --lang eng+kor *.png        # Multi-language OCR
/img --max-dim 600 large.png           # Custom max dimension
```

## Behavior

### 1) Validate Input

- Check that files/directory exist
- Supported formats: png, jpg, jpeg, webp, gif, bmp
- Show usage help if no arguments provided

### 2) Determine Mode

| Condition | Mode | Reason |
|-----------|------|--------|
| `--ocr` flag | OCR extraction | User explicitly requested |
| Text/code screenshot (contextual) | Suggest OCR | 90% token savings |
| General images, UI designs | Resize | Visual information needed |
| Less than 5 images, small size | Read directly | Optimization unnecessary |

### 3) Execute

Run the `img-optimize` CLI tool:

```bash
# Resize mode
img-optimize $FILES_OR_DIR_ARGS

# OCR mode
img-optimize --ocr --lang $LANG $FILES_OR_DIR_ARGS
```

**Resize output**: `/tmp/claude-images/`
**OCR output**: `/tmp/claude-ocr/` (individual .txt files + `_combined.txt`)

### 4) Read Results

- **Resize**: Read optimized images from `/tmp/claude-images/` using the Read tool
- **OCR**: Read text files from `/tmp/claude-ocr/` using the Read tool
- Answer the user's question about the images

### 5) Report

Display processing summary:
- Number of files processed
- Original vs optimized token comparison
- Savings percentage

## API Limits Reference

| Limit | Value |
|-------|-------|
| Max images per request | 100 |
| Max size per image | 5 MB |
| Total request size | 32 MB |
| Resolution limit (20+ images) | 2000x2000 px |
| Token formula | (width x height) / 750 |

## Auto-Optimization Rules

The `img-optimize` script automatically:
- Resizes to 1092px max dimension (optimal token cost)
- Reduces to 1000px for batches of 20+ images
- Warns about batch splitting for 100+ images

## Dependencies

- `scripts/img-optimize` (Python CLI script, bundled)
- `Pillow` (pip install Pillow)
- `tesseract-ocr` (optional, for OCR mode)

## User input

$ARGUMENTS
