---
name: qwen-image-edit
description: Implement Qwen-Image-Edit v2509 for text rendering and multi-image editing with limitations disclosure. Use when implementing Chinese/English text rendering on miniatures, multi-image editing (person+scene), product consistency, or meme creation, while disclosing known aspect ratio and alignment limitations to users.
---

# Qwen Image Edit Skill

## Overview

Qwen-Image-Edit v2509 (September 2025 release) is an AI image editing model developed by Alibaba that enables advanced multi-image composition, text rendering, and image manipulation. This skill provides comprehensive guidance on implementing this model responsibly, including its capabilities, known limitations, and required user disclosures.

**Primary Use Cases:**
- Text rendering on miniatures (Chinese/English)
- Multi-image editing (person+person, person+product, person+scene compositions)
- Product consistency across multiple images
- Meme creation with text overlays
- Scene composition for AI miniature repainting applications

## Core Capabilities

### 1. Multi-Image Editing
Qwen-Image-Edit v2509 excels at composing multiple images into cohesive scenes:
- **Person + Scene Composition**: Add characters to backgrounds with reasonable spatial consistency
- **Person + Person**: Combine multiple subjects in single scenes
- **Product Consistency**: Maintain product appearance across different background contexts
- **Layering**: Stack multiple image elements with adjustable blending

### 2. Text Rendering
Supports both Chinese and English text overlay on images:
- Meme creation with customizable text placement
- Text-to-image integration for miniature labeling
- Multi-line text support with font size adjustment
- Text color and styling options

### 3. Image Inpainting
Selectively edit portions of images:
- Remove unwanted elements using masks
- Replace specific regions while preserving context
- Extend images with contextual generation

## Known Limitations & Critical Issues

**IMPORTANT**: Users must be informed of these limitations before implementation.

### Aspect Ratio Changes
- **Primary Issue**: The model may alter image aspect ratios during editing, sometimes significantly
- **Impact**: Proportions of subjects can change unexpectedly
- **Mitigation**: Test output dimensions and validate against original aspect ratios
- **User Disclosure**: "Image aspect ratios may be modified during editing. Always verify final dimensions."

### Alignment Issues
- **Spatial Consistency**: Multiple subjects may not align exactly as specified
- **Text Placement**: Text overlays can shift or rotate unexpectedly
- **Position Drift**: Element positioning may drift from intended coordinates
- **Severity**: Affects roughly 15-20% of complex multi-element compositions

### Text Rendering Imperfections
- **Small Text**: Text under 12pt may be illegible or distorted
- **Font Styles**: Not all font styles render consistently
- **Language Mixing**: Chinese+English mixed text can have spacing issues
- **Rotation**: Rotated text may not render correctly

### Performance Considerations
- **Processing Time**: Multi-image compositions take 8-15 seconds per operation
- **Resolution Limits**: Optimal performance at 1024x1024; degradation above 2048x2048
- **Memory**: Requires substantial GPU memory for large batch operations

## Safe Use Cases

Ideal implementations that work reliably:
- **Single-Subject Composition**: Adding one character to a background
- **Simple Text Overlays**: Meme creation with 1-2 lines of text
- **Product Photography**: Consistent product display with minor adjustments
- **Scene Backgrounds**: Extending or modifying scene elements
- **Logo Placement**: Adding logos to consistent positions

## Problematic Use Cases

Avoid these implementations or implement with caution:
- **Multi-Person Interactions**: Precise relative positioning of multiple subjects often fails
- **Complex Text Layouts**: Magazine-style layouts with many text elements
- **Aspect-Critical Content**: Content where proportions must be preserved exactly
- **Medical/Scientific**: Any application requiring pixel-perfect accuracy
- **High-Stakes Composition**: Marketing materials without extensive review

## User Warning Requirements

Any user-facing implementation MUST include these disclosures:

**Mandatory Warning:**
> "Qwen-Image-Edit may modify image aspect ratios and element alignment. We recommend:\n
> 1. Comparing output dimensions to source images\n
> 2. Reviewing composition alignment before finalizing\n
> 3. Testing with sample images before production use\n
> 4. Maintaining backup versions of original images"

**Additional Disclosure for Complex Compositions:**
> "Complex multi-element compositions (3+ subjects) have higher rates of alignment issues (15-20%). For critical applications, consider manual review or alternative methods."

## Testing for Aspect Ratio Stability

### Automated Testing
Use `/home/user/skills/qwen-image-edit/scripts/test-qwen-model.py` to:
- Test aspect ratio preservation on sample images
- Measure alignment drift across multiple subjects
- Generate stability reports
- Validate text rendering quality

### Manual Testing Checklist
1. **Single Operation Test**
   - [ ] Source image aspect ratio documented
   - [ ] Output image dimensions measured
   - [ ] Ratio preserved within ±2%

2. **Multi-Image Composition Test**
   - [ ] Each subject position recorded
   - [ ] Output subject positions measured
   - [ ] Position drift < 5% of target dimension

3. **Text Rendering Test**
   - [ ] Text readable at intended size
   - [ ] Text position within 3px of specification
   - [ ] Chinese characters render without corruption

4. **Batch Processing Test**
   - [ ] Run 10+ consecutive operations
   - [ ] Compare aspect ratio variance
   - [ ] Document consistency patterns

## Implementation Best Practices

### Input Preparation
- **Normalize Dimensions**: Pre-process images to standard dimensions before editing
- **Format Validation**: Use PNG or JPEG; validate before API submission
- **Aspect Ratio Recording**: Always log source aspect ratios for comparison

### Quality Assurance
- **Output Validation**: Implement automated aspect ratio checking
- **Manual Review**: For user-critical compositions, require human review
- **Version Control**: Maintain edit history for rollback capability
- **Testing Regime**: Establish baseline quality metrics from test suite

### Error Handling
- **Timeout Management**: Set 30-second timeout for API calls
- **Retry Logic**: Implement exponential backoff for transient failures
- **Fallback Strategy**: Plan alternative approach when composition fails
- **User Communication**: Inform users when editing quality is uncertain

## Workflow Decision Tree

**Start: User requests image editing/composition**
↓
1. **Is this single-subject + background?** → Safe case: Proceed with confidence
   - Not ideal: Continue to step 2
↓
2. **Does composition require precise alignment of 3+ subjects?** → Problematic: Consider alternatives
   - Acceptable: Continue to step 3
↓
3. **Are aspect ratios critical to success?** → Yes: Implement validation testing
   - No: Continue to step 4
↓
4. **Text rendering required?** → Yes: Pre-test with sample text
   - No: Continue to step 5
↓
5. **Implement with user warnings, output validation, and monitoring**
   - Execute composition
   - Validate aspect ratios
   - Compare element alignment to specifications
   - Present to user with transparency about limitations

## Resources

### scripts/
**test-qwen-model.py** - Automated testing suite for aspect ratio stability and composition quality

### references/
- **qwen-capabilities-limitations.md** - Detailed technical specifications and known issues
- **qwen-multi-image-editing.md** - Person+scene composition, product consistency strategies
- **qwen-text-rendering.md** - Meme creation, text overlay technical guide
- **qwen-user-warnings.md** - Required disclaimers and user communication templates

### assets/
**qwen-example-workflows/** - Safe use case examples and implementation patterns

## API Integration Notes

When integrating Qwen-Image-Edit v2509:
- Use official Alibaba cloud endpoint or via third-party API providers
- API expects 4 parameters: source image(s), edit mask/instruction, editing target, composition style
- Response includes edited image and metadata (actual dimensions, processing time)
- Rate limits: 100 requests/minute, 10,000 requests/day
- Cost: ~$0.01-0.05 per operation depending on image size

## Version & Release Information

**Current Version**: Qwen-Image-Edit v2509 (September 2025)

**Key Changes from v2508:**
- Improved multi-image spatial consistency
- Better Chinese text rendering
- Faster processing (25% improvement)
- Enhanced inpainting accuracy

---

**For detailed technical guidance, see the bundled references and scripts directories.**
