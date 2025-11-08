# Qwen-Image-Edit v2509: Capabilities & Limitations Reference

## Technical Specifications

### Model Version
- **Name**: Qwen-Image-Edit v2509
- **Release Date**: September 2025
- **Developer**: Alibaba Cloud
- **Base Model**: Qwen vision-language architecture

### Performance Metrics
- **Input Resolution**: Up to 4096x4096 (optimal: 1024x1024)
- **Processing Speed**: 8-15 seconds per composition (single GPU)
- **Output Quality**: 8-bit RGB/RGBA
- **Batch Processing**: Up to 100 concurrent requests
- **Memory Requirements**: 8GB+ GPU VRAM recommended

### Supported Image Formats
- **Input**: PNG, JPEG, WEBP, BMP
- **Output**: PNG (recommended), JPEG, WEBP
- **Color Modes**: RGB, RGBA, Grayscale
- **Maximum File Size**: 50MB per image

## Core Capabilities

### 1. Image Composition

#### Multi-Image Merging
- **Subjects per composition**: 1-5 optimal (degrades at 6+)
- **Subject types**: People, objects, scenes, text overlays
- **Blending modes**: Normal, additive, multiply, screen
- **Mask support**: Binary masks, soft-edge feathering

**Success Rate by Composition Type:**
- Single subject + background: 95%
- 2 subjects + background: 85%
- 3 subjects + background: 70%
- 4+ subjects: 45%

#### Spatial Positioning
- **Coordinate system**: Pixel-based absolute positioning
- **Precision**: ±5px typical; ±10px for complex scenes
- **Transformation**: Scale (0.1x to 10x), rotation (0-360°)
- **Z-ordering**: Layer stacking with depth sorting

### 2. Text Rendering

#### Text Capabilities
- **Languages**: English, Simplified Chinese, Traditional Chinese
- **Font Sizes**: 8pt-96pt effective range
- **Text Styles**: Normal, bold, italic (font-dependent)
- **Color**: Full RGB support, transparency (0-255)
- **Alignment**: Left, center, right, justified

#### Text Limitations
- **Minimum readable size**: 12pt (below 12pt, quality degrades rapidly)
- **Maximum line length**: 80 characters before wrapping
- **Rotation**: 0-360° but quality drops after 45°
- **Special characters**: Unicode support variable; CJK more reliable

**Font Support Matrix:**
| Font Family | English | Chinese | Quality |
|-------------|---------|---------|---------|
| Sans-serif  | Excellent | Good | High |
| Serif       | Good | Fair | Medium |
| Monospace   | Good | Poor | Medium |
| Decorative  | Poor | Unsupported | Low |

### 3. Image Inpainting

#### Inpainting Capabilities
- **Mask types**: Binary (0/255) and soft masks (0-255)
- **Fill methods**: Content-aware, contextual, color-filled
- **Precision**: Works best with 50%+ of image context available
- **Style transfer**: Attempts to match surrounding aesthetics

#### Supported Inpainting Tasks
- Remove objects: Up to ~20% of image area
- Replace regions: Up to ~40% of image area
- Extend edges: Add 10-30% new content at borders
- Seamless blending: Feathering radius 50-200px

### 4. Image Enhancement

#### Enhancement Capabilities
- **Color grading**: Saturation, hue, brightness, contrast adjustment
- **Tone mapping**: Exposure compensation (-2 to +2 stops)
- **Blur/Sharpen**: Gaussian blur, unsharp masking
- **Noise reduction**: Mild to aggressive denoising

#### Limitations
- **Upscaling**: 2x max without quality loss; 4x available but lossy
- **Recovery**: Cannot recover completely blown-out highlights
- **Artifacts**: May introduce halo effects on high-contrast edges

## Known Limitations

### Critical Issues

#### 1. Aspect Ratio Modification
**Severity**: HIGH | **Frequency**: 5-15% of operations

**Symptoms:**
- Output dimensions differ from input despite settings
- Subject proportions appear stretched or compressed
- Typical range: ±2-8% aspect ratio change

**Causes:**
- Internal padding/resizing during processing
- Composition normalization for multi-subject handling
- Optimization for memory efficiency

**Workarounds:**
- Log source dimensions before processing
- Validate output dimensions post-processing
- Implement automatic aspect ratio correction
- Use "preserve_aspect_ratio: true" flag (when available)

**Example:**
```
Source: 1024x768 (1.33:1)
Output: 1024x780 (1.31:1)
Drift: -1.5%
```

#### 2. Alignment Drift
**Severity**: MEDIUM-HIGH | **Frequency**: 15-20% of complex compositions

**Symptoms:**
- Elements appear shifted from specified positions
- Multi-subject spacing inconsistent
- Text overlays offset from target coordinates

**Causes:**
- Spatial reasoning inconsistency in multi-element scenes
- Optimization for visual balance over precision
- Batch processing variations

**Affected Scenarios:**
- 3+ subjects in single composition (20% failure rate)
- Precise text placement (10% drift)
- Complex layering (25% drift)

**Mitigation:**
- Use simpler compositions (2 subjects max) for critical applications
- Test with sample batches before production
- Implement human review step for high-stakes content
- Allow ±10px tolerance in positioning requirements

#### 3. Text Rendering Artifacts
**Severity**: MEDIUM | **Frequency**: 10-15% of text operations

**Common Issues:**
- **Character corruption**: Chinese characters sometimes malformed
- **Font fallback**: Unavailable fonts silently substitute
- **Kerning**: Spacing between characters inconsistent
- **Anti-aliasing**: Pixelation at small sizes

**Critical Text Conditions:**
- Size < 12pt: Quality unreliable
- Mixed language text: Spacing issues 20% of cases
- Rotated text > 45°: Legibility compromised
- Very long strings: Line breaks inaccurate

#### 4. Color Bleeding
**Severity**: LOW-MEDIUM | **Frequency**: 5% of operations

**Symptoms:**
- Colors from one element bleed into adjacent areas
- Particularly visible at high-contrast boundaries
- Affects transparency blending

**Occurs with:**
- Sharp edges between subjects
- High saturation color combinations
- Small subjects near boundaries

#### 5. Memory/Performance Issues
**Severity**: MEDIUM | **Frequency**: 3-5% of operations

**Constraints:**
- GPU VRAM: 8GB minimum; 12GB+ recommended for batch operations
- Processing timeout: 30 seconds default
- Batch size: >100 concurrent requests may fail
- Resolution: >2048x2048 causes 40%+ performance degradation

**Optimization Tips:**
- Process in batches of 10-20 items
- Reduce resolution for prototyping (max 1024x1024)
- Implement queue system for high-volume processing
- Monitor GPU memory usage

### Moderate Issues

#### Missing Features
- **No video support**: Only static images
- **No animated GIFs**: Single-frame output only
- **Limited style transfer**: Cannot match arbitrary artistic styles
- **No face detection**: Cannot automatically detect and preserve faces
- **No semantic segmentation**: Cannot identify object types beyond general spatial reasoning

#### Consistency Issues
- **Non-deterministic output**: Same input may produce slightly different outputs
- **Batch variations**: Items processed separately may differ from batch processing
- **Time-dependent**: Performance varies with server load

### Minor Issues

#### Metadata Loss
- **EXIF stripping**: Original image metadata removed
- **Color profile**: ICC profile not preserved
- **Comments**: XMP/IPTC data discarded

#### Edge Cases
- **Fully transparent images**: May fail or produce artifacts
- **Extreme aspect ratios**: >10:1 ratios unsupported
- **Animated formats**: Single frame extracted
- **Corrupted input**: Error handling varies

## API Behavior Notes

### Input Validation
- **Format checking**: Automated, rejects invalid formats
- **Resolution limits**: Rejects images > 4096px in any dimension
- **File size**: Hard limit 50MB per image
- **Dimension ratio**: Extreme ratios (>20:1) may be rejected

### Output Characteristics
- **PNG**: Default lossless format, includes alpha channel
- **JPEG**: Lossy, smaller file size, opaque (no alpha)
- **Metadata**: Always stripped for privacy
- **Dimensions**: May differ from input (aspect ratio issue)

### Error Responses
```json
{
  "error": "aspect_ratio_violation",
  "message": "Source and target aspect ratios differ by >10%",
  "source_ratio": 1.33,
  "output_ratio": 1.50,
  "code": "RATIO_CHANGE_DETECTED"
}
```

### Rate Limiting
- **Standard tier**: 100 requests/minute, 10,000/day
- **Premium tier**: 1,000 requests/minute, 100,000/day
- **Burst handling**: 5-second exponential backoff after limit
- **Timeout**: 30 seconds maximum per request

## Recommendation Matrix

| Use Case | Recommended | Caution | Avoid |
|----------|------------|---------|-------|
| Single-subject composition | ✓ | | |
| Simple text overlay | ✓ | | |
| 2-subject arrangement | ✓ | | |
| Product consistency | ✓ | | |
| 3+ subject composition | | ✓ | |
| Complex text layout | | ✓ | |
| Medical/scientific accuracy | | | ✗ |
| Aspect-critical content | | | ✗ |
| Real-time processing | | ✓ | |
| Batch processing (100+) | | ✓ | |

## Fallback Strategies

When Qwen-Image-Edit fails or produces poor results:

### For Aspect Ratio Issues
1. Detect aspect ratio change using test suite
2. Crop output to match source ratio (slight quality loss)
3. Or implement aspect ratio correction filter
4. Document in output metadata

### For Alignment Issues
1. Compare output positions to specification
2. If drift > 10px, manually correct OR
3. Simplify composition (reduce subject count)
4. Fall back to alternative composition method

### For Text Rendering Issues
1. Increase font size to minimum 14pt
2. Simplify character set (avoid special unicode)
3. Use single language (avoid mixing Chinese+English)
4. Pre-render text separately and composite manually

### For Memory Issues
1. Reduce batch size (process 5-10 items vs 100)
2. Lower resolution (target 1024x1024)
3. Implement queue system with delays
4. Use smaller model variant if available

## Version History

### v2509 (September 2025) - Current
- Improved multi-image spatial consistency (+10% accuracy)
- Better Chinese text rendering (+15% quality)
- 25% performance improvement (8-12s avg processing time)
- Enhanced inpainting accuracy for complex scenes
- New "preserve_aspect_ratio" parameter (beta)

### v2508 (August 2025)
- Initial release of v2.5 series
- Basic multi-image composition
- Text rendering support
- Known aspect ratio issues (15-20% failure)

### v2407 (Previous stable)
- Single-subject editing only
- Limited text support
- No multi-image composition
- Deprecated; recommend upgrade to v2509
