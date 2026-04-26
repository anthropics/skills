---
name: pdf-signature
description: "Add handwritten signatures to PDF documents with automatic background removal and flexible positioning. Use when users need to: (1) add signatures to PDF files, (2) sign documents at specific positions (corners), (3) sign either all pages or only the last page, or (4) process signature images to remove backgrounds. Triggers include requests like 'sign this PDF', 'add my signature to all pages', 'sign the last page', or 'add signature to the bottom right'."
license: Apache-2.0. LICENSE.txt has complete terms
---

# PDF Signature

## Overview

Automatically add handwritten signatures to PDF documents with intelligent image processing. The skill handles signature image preprocessing (background removal, cropping) and precise positioning on PDF pages.

## Quick Start

Basic usage - sign all pages at bottom right corner:

```bash
python scripts/add_pdf_signature.py <signature_image> <pdf_file>
```

The script will:
1. Automatically detect and crop the signature from the image
2. Remove the background to make it transparent
3. Add the signature to every page at the bottom right corner
4. Save output as `<original_filename>_已签名.pdf`

## Workflow

When a user requests PDF signing:

1. **Gather inputs:**
   - Signature image path (required)
   - PDF file path (required)
   - Position preference (optional, default: 右下角)
   - Pages to sign (optional, default: 每页)
   - Signature size (optional, default: 80 points)

2. **Run the signature script:**
   ```bash
   python scripts/add_pdf_signature.py <signature_image> <pdf_file> \
     --position <position> \
     --pages <pages> \
     --size <size>
   ```

3. **Verify output:**
   - Output file is created with suffix `_已签名.pdf`
   - Check that signature appears on expected pages

## Parameters

### Position Options
- `右下角` (default) - Bottom right corner
- `左下角` - Bottom left corner
- `右上角` - Top right corner
- `左上角` - Top left corner

### Pages Options
- `每页` (default) - Sign every page
- `尾页` - Sign only the last page

### Size
- Integer value in points (default: 80)
- Larger values create bigger signatures
- Aspect ratio is automatically preserved

## Examples

**Sign every page at bottom right (most common):**
```bash
python scripts/add_pdf_signature.py signature.jpg document.pdf
```

**Sign only the last page at bottom left:**
```bash
python scripts/add_pdf_signature.py signature.jpg contract.pdf --position 左下角 --pages 尾页
```

**Custom signature size:**
```bash
python scripts/add_pdf_signature.py signature.jpg report.pdf --size 100
```

**Specify output location:**
```bash
python scripts/add_pdf_signature.py signature.jpg input.pdf --output /path/to/signed.pdf
```

## How It Works

### Signature Image Processing

The script automatically:

1. **Detects signature region:** Uses pixel brightness analysis (threshold=80) to find dark ink strokes
2. **Crops whitespace:** Removes empty margins around the signature
3. **Removes background:** 
   - Pixels with brightness > 150: Fully transparent
   - Pixels with brightness 100-150: Semi-transparent
   - Pixels with brightness < 100: Opaque (signature ink)
4. **Preserves aspect ratio:** Signature is scaled proportionally

### PDF Processing

1. Reads the original PDF
2. For each target page:
   - Creates a transparent overlay with the signature
   - Positions signature based on --position parameter
   - Merges overlay onto the original page
3. Saves all pages to output file

## Dependencies

Required Python packages:
- `pypdf` - PDF manipulation
- `pillow` - Image processing
- `numpy` - Array operations for pixel analysis
- `reportlab` - PDF canvas creation

Install with:
```bash
pip install pypdf pillow numpy reportlab
```

## Troubleshooting

**Signature not properly cropped:**
- The script uses brightness threshold 80 to detect ink
- Very light signatures may need manual adjustment
- Edit `brightness_threshold` parameter in `process_signature_image()`

**Background not fully transparent:**
- Adjust threshold values in the background removal section
- Light gray backgrounds may need higher threshold (>150)

**Signature too large/small:**
- Use `--size` parameter to adjust width in points
- Default is 80 points (~1.1 inches)

## Resources

### scripts/add_pdf_signature.py

Complete signature tool with command-line interface. Can be executed directly or read for understanding the implementation.
