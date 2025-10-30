---
name: advanced-pptx
description: "Advanced PowerPoint creation, editing, and analysis. Enhanced skill with modular architecture, improved features, and full backward compatibility for professional presentation generation."
license: Proprietary. LICENSE.txt has complete terms
---

# Advanced PPTX: Professional PowerPoint Generation

## Overview

The advanced-pptx skill is an enhanced PowerPoint manipulation tool, providing a modular, extensible, and maintainable architecture for PowerPoint (.pptx) file creation, editing, and analysis. It maintains full backward compatibility with standard pptx workflows while adding significant improvements.

## Key Enhancements Over pptx

### 🏗️ Modular Architecture

- **PresentationManager**: Centralized presentation lifecycle management with metadata
- **SlideManager**: Enhanced slide creation with declarative definitions
- **InventoryExtractor**: Improved text extraction with better formatting detection
- **ReplacementEngine**: Enhanced replacement logic with validation
- **LayoutEngine**: Dynamic layout optimization and auto-fitting
- **MediaHandler**: Extended media support (SVG, remote images, video placeholders)
- **Diagnostics**: Comprehensive validation and error reporting

### 🚀 Enhanced Features

- **Better Layout Engine**: Auto text wrapping, proportional scaling, responsive spacing
- **Extended Media Support**: SVG conversion, remote image caching, video placeholders
- **Declarative Slide API**: Define slides using structured dictionaries
- **Enhanced Metadata**: Comprehensive core properties and custom metadata
- **Improved Diagnostics**: Text overflow detection, shape overlap analysis
- **Performance Optimizations**: Better file integrity checks and export performance

### 🔄 Full Backward Compatibility

- **CLI Scripts**: Drop-in replacements for `inventory.py` and `replace.py`
- **JSON Formats**: Compatible inventory and replacement formats
- **Workflows**: All pptx workflows supported without changes
- **API Interfaces**: Non-breaking API improvements

## Usage

### Basic Presentation Creation

```python
from main import PresentationManager, SlideManager

# Create presentation with metadata
pm = PresentationManager()
pm.set_metadata(
    author="Your Name",
    title="Presentation Title",
    subject="Presentation Subject"
)

# Add slides using enhanced managers
sm = SlideManager(pm.prs)
sm.add_title_slide("Title", "Subtitle")
sm.add_bullet_slide("Features", [
    "Enhanced architecture",
    "Better performance",
    "Full compatibility"
])

# Save with validation
pm.save("presentation.pptx", validate_before_save=True)
```

### Declarative Slide Creation

```python
# Define slides using structured format
slide_def = {
    "layout": "bullet",
    "title": "Key Benefits",
    "content": [
        "Modular and extensible",
        "Enhanced media support",
        "Better diagnostics"
    ]
}

slide = sm.add_declarative_slide(slide_def)
```

### Inventory Extraction (CLI)

```bash
# Extract text inventory (backward compatible)
python scripts/inventory.py presentation.pptx inventory.json

# Extract only shapes with issues
python scripts/inventory.py presentation.pptx inventory.json --issues-only
```

### Text Replacement (CLI)

```bash
# Apply text replacements (backward compatible)
python scripts/replace.py input.pptx replacements.json output.pptx
```

### Enhanced Inventory Extraction (Programmatic)

```python
from main import InventoryExtractor, Presentation

prs = Presentation("input.pptx")
extractor = InventoryExtractor(prs)

# Extract comprehensive inventory
inventory = extractor.extract_text_inventory()
extractor.save_inventory(inventory, "inventory.json")

# Extract only problematic shapes
issues_inventory = extractor.extract_text_inventory(issues_only=True)
```

### Enhanced Text Replacement (Programmatic)

```python
from main import ReplacementEngine, Presentation
import json

prs = Presentation("input.pptx")
engine = ReplacementEngine(prs)

# Load replacement data
with open("replacements.json") as f:
    replacements = json.load(f)

# Apply with validation
success = engine.apply_replacements(replacements, validate_before=True)
if success:
    prs.save("output.pptx")
```

## Inventory Format

The inventory format is fully compatible with pptx with enhancements:

```json
{
  "slide-0": {
    "shape-0": {
      "left": 1.0,
      "top": 0.5,
      "width": 8.0,
      "height": 1.0,
      "placeholder_type": "TITLE",
      "paragraphs": [
        {
          "text": "Slide Title",
          "bold": true,
          "font_size": 24,
          "font_name": "Arial",
          "alignment": "CENTER",
          "color": "#000000"
        }
      ]
    }
  }
}
```

### New Inventory Features

- **Enhanced Positioning**: More accurate EMU to inches conversion
- **Better Formatting Detection**: Improved font, color, and alignment extraction
- **Placeholder Recognition**: Enhanced placeholder type identification
- **Issue Detection**: Flags for text overflow and formatting problems

## Replacement Format

Fully compatible with pptx replacement format:

```json
{
  "slide-0": {
    "shape-0": {
      "paragraphs": [
        {
          "text": "New text content",
          "bold": true,
          "font_size": 18,
          "bullet": true,
          "level": 0,
          "alignment": "CENTER",
          "color": "#FF0000"
        }
      ]
    }
  }
}
```

### Enhanced Replacement Features

- **Validation**: Pre-replacement validation against current inventory
- **Enhanced Formatting**: Support for more font and paragraph properties
- **Error Reporting**: Clear validation errors with available shape information
- **Bulk Operations**: Efficient processing of large replacement sets

## Architecture

### Core Classes

1. **PresentationManager**

   - Handles presentation lifecycle (create, load, save)
   - Manages metadata and core properties
   - Provides validation and diagnostics integration

2. **SlideManager**

   - Enhanced slide creation with multiple layout types
   - Declarative slide definitions
   - Improved error handling and fallbacks

3. **InventoryExtractor**

   - Compatible with pptx inventory.py
   - Enhanced shape detection and sorting
   - Better formatting property extraction
   - Issue detection capabilities

4. **ReplacementEngine**

   - Compatible with pptx replace.py
   - Pre-validation against inventory
   - Enhanced formatting application
   - Improved error reporting

5. **LayoutEngine**

   - Dynamic layout optimization
   - Auto text fitting and wrapping
   - Responsive spacing calculations

6. **MediaHandler**

   - Remote image downloading and caching
   - SVG to PNG conversion
   - Video placeholder generation
   - Media file validation

7. **Diagnostics**
   - Text overflow detection
   - Shape overlap analysis
   - Comprehensive validation reporting
   - Performance metrics

### Design Principles

- **Backward Compatibility**: All pptx workflows work unchanged
- **Modular Design**: Each component has single responsibility
- **Type Safety**: Full type hints and validation
- **Error Handling**: Graceful degradation and clear error messages
- **Performance**: Optimized for large presentations and batch operations
- **Extensibility**: Easy to add new features without breaking existing code

## Migration from pptx

### No Changes Required

- All existing CLI scripts work unchanged
- Inventory and replacement JSON formats are compatible
- All existing workflows continue to function

### Optional Enhancements

- Use new PresentationManager for better metadata handling
- Leverage declarative slide definitions for cleaner code
- Add validation and diagnostics for better error detection
- Use enhanced media support for SVG and remote images

### Performance Improvements

- Faster inventory extraction with better shape sorting
- More efficient replacement processing
- Enhanced validation reduces runtime errors
- Better memory usage for large presentations

## Dependencies

Same as pptx plus optional enhancements:

- **python-pptx**: Core PowerPoint manipulation
- **requests**: For remote image downloading (optional)
- **Pillow**: For image processing and SVG conversion (optional)
- **sharp**: For high-quality SVG to PNG conversion (optional)

## Backward Compatibility Guarantee

presentation is designed as a drop-in replacement for pptx:

- ✅ All existing CLI scripts work unchanged
- ✅ Inventory JSON format is fully compatible
- ✅ Replacement JSON format is fully compatible
- ✅ All workflows and processes continue to function
- ✅ Performance is equal or better than pptx
- ✅ No breaking changes to existing APIs

## Future Roadmap

- **Template Engine**: Advanced template processing and management
- **Batch Operations**: Optimized bulk presentation processing
- **Real-time Collaboration**: Live editing and synchronization features
- **Advanced Analytics**: Presentation content analysis and optimization
- **Cloud Integration**: Direct integration with cloud storage and services
