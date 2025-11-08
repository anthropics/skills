# Qwen-Image-Edit v2509: Multi-Image Editing Guide

## Overview

Multi-image editing in Qwen-Image-Edit involves compositing multiple source images into a single cohesive result. This guide covers person+person, person+product, and person+scene compositions with practical examples for miniature repainting applications.

## API Structure for Multi-Image Editing

### Basic Request Format
```json
{
  "operation": "compose",
  "images": [
    {
      "url": "path/to/base_image.png",
      "role": "background"
    },
    {
      "url": "path/to/subject.png",
      "role": "subject",
      "position": {"x": 256, "y": 128},
      "scale": 1.0,
      "rotation": 0
    }
  ],
  "composition_style": "natural",
  "preserve_aspect_ratio": false,
  "quality": "high"
}
```

### Key Parameters
- **role**: "background", "subject", "accent", "overlay"
- **position**: {x, y} in pixels from top-left corner
- **scale**: 0.1 to 10.0 (1.0 = native size)
- **rotation**: 0-360 degrees clockwise
- **opacity**: 0.0-1.0 (alpha transparency)
- **blend_mode**: "normal", "multiply", "screen", "overlay", "additive"

## Person + Scene Composition

### Use Case: Miniature Portrait in Scenic Background

**Optimal Workflow:**
1. Source a clean cutout of the miniature figure (transparent background preferred)
2. Prepare a suitable scene background at 1024x1024 or larger
3. Define target position within scene
4. Specify scale to achieve desired miniature size proportion
5. Apply composition with natural blending

**Example Configuration:**
```json
{
  "operation": "compose",
  "images": [
    {
      "url": "fantasy_tavern_scene.png",
      "role": "background",
      "description": "1024x1024 tavern interior"
    },
    {
      "url": "painted_knight_cutout.png",
      "role": "subject",
      "position": {"x": 512, "y": 640},
      "scale": 0.5,
      "rotation": 0,
      "opacity": 1.0,
      "blend_mode": "normal"
    }
  ],
  "composition_style": "seamless",
  "preserve_aspect_ratio": true,
  "quality": "high"
}
```

### Best Practices for Person + Scene

#### 1. Subject Preparation
- **Background removal**: Use transparent PNG with alpha channel
- **Edge quality**: Feather edges (2-4px) for softer blending
- **Resolution**: Subject should be 20-50% of scene dimensions
- **Orientation**: Match subject viewing angle to scene perspective

#### 2. Scene Selection
- **Depth**: Scenes with clear foreground/background layers work better
- **Lighting**: Match subject lighting direction to scene illumination
- **Perspective**: Perspective lines should align with subject placement
- **Color palette**: Compatible colors reduce color bleeding artifacts

#### 3. Positioning Strategy
```
Scene Layout:
+----------- 1024px -----------+
|                               |
|   Background                  | 768px
|   (tavern interior)          |
|        [Knight]               |
|        (512x512)              |
|                               |
+-------------------------------+

Knight position: {x: 256, y: 256} (centered)
Knight scale: 0.5 (512px in 1024px scene)
```

#### 4. Common Issues & Solutions

**Issue: Subject appears detached from scene**
- *Cause*: Scale too large or position too high
- *Solution*: Position bottom of subject at scene ground level (~y: 600-700)
- *Testing*: Preview at different Y positions before finalizing

**Issue: Lighting mismatch (subject too bright/dark)**
- *Cause*: Source and scene have different light directions
- *Solution*: Use composition_style: "auto_adjust_lighting" (if available)
- *Testing*: Compare subject lighting to surrounding scene elements

**Issue: Subject appears flat/2D in 3D scene**
- *Cause*: Missing shadow or incorrect perspective scale
- *Solution*: Add subtle drop shadow; scale subject relative to background elements
- *Testing*: Compare subject size to environmental references (furniture, doors)

### Person + Scene Success Metrics

**Assess quality on:**
1. **Visual Integration**: Does subject belong in scene? (subjective)
2. **Lighting Consistency**: Does subject lighting match scene? (check shadows)
3. **Scale Appropriateness**: Is subject size proportional to scene? (compare to furniture)
4. **Edge Blending**: Are edges well-integrated? (zoom to 200% and check)
5. **No artifacts**: Color bleeding, halos, or distortion? (inspect carefully)

**Acceptance Criteria:**
- All 5 metrics should score 8/10 or higher for production use
- If any metric < 6/10, request re-processing with adjusted parameters

## Person + Product Composition

### Use Case: Miniature Figure with Manufactured Product

**Scenario**: Painting completion showing miniature sword alongside painted figure

**Workflow:**
1. Source high-quality product image (e.g., painted sword miniature)
2. Source painted figure/character miniature
3. Define complementary arrangement (side-by-side, figure holding product)
4. Apply composition with careful positioning

**Example Configuration:**
```json
{
  "operation": "compose",
  "images": [
    {
      "url": "neutral_background.png",
      "role": "background",
      "description": "Clean white/gray background, 1024x1024"
    },
    {
      "url": "painted_figure.png",
      "role": "subject",
      "position": {"x": 256, "y": 400},
      "scale": 0.6,
      "rotation": 0,
      "blend_mode": "normal"
    },
    {
      "url": "painted_sword.png",
      "role": "subject",
      "position": {"x": 650, "y": 350},
      "scale": 0.5,
      "rotation": 15,
      "blend_mode": "normal"
    }
  ],
  "composition_style": "product",
  "preserve_aspect_ratio": false,
  "quality": "high"
}
```

### Person + Product Best Practices

#### 1. Product Selection
- **Quality**: Products should be clean, well-lit cutouts
- **Complementarity**: Products should relate to or enhance the figure
- **Scale**: Keep products 30-50% of figure size for balanced composition
- **Orientation**: Orient products to show key details

#### 2. Layout Patterns
**Pattern A: Side-by-Side**
```
[Figure] [Product]
         (Product positioned right of figure)
         Spacing: 20-30% of image width
```

**Pattern B: Figure + Held Object**
```
[Figure holding product]
(Requires close positioning: X offset 30-50px, Y aligned to hands)
```

**Pattern C: Staggered**
```
[Figure]
    [Product]
(Product lower and offset for depth)
```

#### 3. Positioning Mathematics
```python
# For side-by-side at 1024x1024:
figure_center_x = 300
product_center_x = 700
spacing = product_center_x - figure_center_x  # 400px (good separation)

# Vertical alignment (align at middle)
figure_y = 400
product_y = 400
```

#### 4. Product Consistency Issues

**Issue: Products appear misaligned when composited**
- *Diagnosis*: Use alignment test from test-qwen-model.py
- *Solutions*:
  - Reduce product scale (smaller objects have better positioning accuracy)
  - Use simpler background (neutral color vs patterned)
  - Process each product separately, then combine results

**Issue: Product colors/finish changes in composition**
- *Cause*: Color blending or lighting adjustment from model
- *Solution*: Use composition_style: "preserve_colors" if available
- *Fallback*: Increase product opacity and use blend_mode: "normal"

**Issue: Product edges bleed into background**
- *Cause*: Low image quality or edge feathering issues
- *Solution*:
  - Use PNG with clean alpha channel
  - Ensure product has sharp edges (no anti-aliasing beyond 1px)
  - Test with different blend modes

### Product Consistency Validation

For miniature repainting applications where showing product progression:

**Validation Steps:**
1. Compare color values (RGB) of original vs composed product
   - Acceptable drift: ±5% per channel
2. Check dimension preservation
   - Acceptable drift: ±2% in width/height
3. Verify edge integrity
   - No softening beyond 2px from edge
4. Confirm detail visibility
   - Fine details should remain sharp

**Test Composition Process:**
```
1. Create 3 test scenes with same product
2. Process each composition
3. Extract product region from each output
4. Compare RGB values using histogram analysis
5. Measure color consistency (std dev < 5% = good)
```

## Person + Person Composition

### Use Case: Multiple Miniature Figures in Scene

**Scenario**: Battle diorama with multiple painted miniatures arranged together

**Challenges:**
- Alignment of multiple subjects is less reliable (15-20% failure rate)
- Spatial relationships can drift
- Recommended: Use simple 2-figure compositions; avoid 3+

**Example Configuration - Two Characters:**
```json
{
  "operation": "compose",
  "images": [
    {
      "url": "tavern_background.png",
      "role": "background"
    },
    {
      "url": "warrior_figure.png",
      "role": "subject",
      "position": {"x": 300, "y": 500},
      "scale": 0.5,
      "rotation": 0
    },
    {
      "url": "rogue_figure.png",
      "role": "subject",
      "position": {"x": 600, "y": 550},
      "scale": 0.48,
      "rotation": 25
    }
  ],
  "composition_style": "natural",
  "preserve_aspect_ratio": false
}
```

### Person + Person Best Practices

#### 1. Spacing & Positioning
- **Minimum spacing**: 100-150px between figures (prevent overlap artifacts)
- **Vertical offset**: 20-50px variation in Y position for natural grouping
- **Rotation**: Different rotations (0°, 15°, 30°) make scenes more dynamic
- **Depth**: Larger Y value = lower in composition = closer to viewer

#### 2. Positioning Formula
```python
# For two-figure arrangement (1024x1024 scene):

# Figure A: Left side
fig_a_x = 300 + (scene_width * 0.1)  # 300px
fig_a_y = 500

# Figure B: Right side
fig_b_x = 600 + (scene_width * 0.1)  # 600px
fig_b_y = 550  # Slightly lower for depth

# Spacing verification
spacing = fig_b_x - fig_a_x  # 300px (good)
```

#### 3. Quality Expectations

**2-Figure Composition**
- Success rate: 85%
- Alignment accuracy: ±10px
- Suitable for: Most miniature repainting applications
- Recommendation: Use this as standard

**3-Figure Composition**
- Success rate: 70%
- Alignment accuracy: ±15px
- Suitable for: Less critical, casual arrangements
- Recommendation: Test before production use

**4+ Figures**
- Success rate: 45-60%
- Alignment accuracy: ±20px
- Suitable for: Experimental only
- Recommendation: Split into multiple 2-figure compositions and combine

#### 4. Common Failure Patterns

**Pattern A: Figures become misaligned (shifted)**
- Figures drift from specified positions
- *Mitigation*: Reduce to simpler composition; add 20px spacing buffer

**Pattern B: One figure appears "behind" accidentally**
- Opacity or depth ordering incorrect
- *Solution*: Ensure both figures have opacity: 1.0
- *Test*: Verify z-order in output

**Pattern C: Figures merge or overlap**
- Boundaries blur together
- *Solution*: Increase spacing to 150-200px minimum
- *Fallback*: Process figures separately; composite manually

### Testing Multi-Figure Compositions

**Test Matrix:**
```
Composition Type | Recommended | Test Before | Not Recommended
2 figures        | ✓           |            |
3 figures        |             | ✓          |
4 figures        |             |            | ✗
5+ figures       |             |            | ✗
```

**Pre-Production Testing:**
1. Create test composition with 2 figures
2. Run through test-qwen-model.py alignment suite
3. Check if max_drift_percent < 5%
4. If passed: Safe for production
5. If failed: Adjust spacing or simplify composition

## Advanced Composition Techniques

### Layered Composition (3+ Layers)

For complex scenes with foreground, mid-ground, background:

**Recommended Approach:**
1. Compose background + main subject first
2. Output result as new background
3. Compose that result + secondary subject
4. Output final result

**Avoids:** Complex 3-subject operations (which have high failure rates)

**Example:**
```
Step 1: Background + Character
  Input: tavern.png + warrior.png
  Output: tavern_with_warrior.png

Step 2: Result + Accent Element
  Input: tavern_with_warrior.png + sword.png
  Output: final_composition.png
```

### Shadow & Depth Enhancement

To improve visual integration:

1. **Pre-composition**: Generate drop shadow for subject
   - Shadow angle matches scene lighting
   - Shadow blur: 8-12px
   - Shadow opacity: 0.3-0.5

2. **Post-composition**: Apply subtle vignetting
   - Darkens edges to frame composition
   - Strengthens depth perception

### Color Grading for Consistency

If color mismatch detected:

1. **Extract product/figure region** from output
2. **Measure average color** (RGB histogram)
3. **Compare to source** color values
4. **Apply color correction** if drift > 5%:
   ```
   corrected_R = source_R * (output_R / expected_R)
   corrected_G = source_G * (output_G / expected_G)
   corrected_B = source_B * (output_B / expected_B)
   ```

## Performance & Optimization

### Processing Time Estimates
```
Single subject:        8-10 seconds
Two subjects:          10-12 seconds
Three subjects:        12-15 seconds
Post-processing:       2-4 seconds (additional)
Full pipeline:         ~20 seconds for 2-subject composition
```

### Batch Optimization
- Process up to 10 compositions in parallel (if 8GB+ VRAM)
- Reduce resolution to 512x512 for prototyping
- Use "medium" quality for testing; "high" for final output

### GPU Memory Usage
```
Composition Type    | Memory Required
Single subject      | 2-3 GB
2-3 subjects        | 4-5 GB
Batch (10 items)    | 8-12 GB
Post-processing     | +2-3 GB
```

## Miniature Repainting Application Guide

### Portfolio Showcase Use Case

**Goal**: Display painted miniatures in professional context

**Recommended Approach:**
1. Use person+scene compositions for hero shots
2. Keep scenes simple (single figure per scene)
3. Use neutral or thematic backgrounds
4. Test lighting consistency before finalizing

**Quality Standards:**
- Aspect ratio preserved (< 2% drift)
- No alignment issues visible
- Professional color accuracy
- Clean edge integration

### Progress Documentation Use Case

**Goal**: Show painting progression on single miniature

**Recommended Approach:**
1. Use consistent background across all iterations
2. Position figure identically in each composition
3. Document exact positioning parameters for consistency
4. Compare color values across iterations to show progression

**Template:**
```json
{
  "figure": "dragon_miniature_v1.png",
  "background": "neutral_backdrop_1024x1024.png",
  "position": {"x": 512, "y": 650},
  "scale": 0.6,
  "rotation": 0,
  "documentation": "Stage 1: Base coat applied"
}
```

### Comparative Display Use Case

**Goal**: Show before/after or different painting styles

**Approach:**
1. Create two identical compositions with different figures
2. Use same background and positioning
3. Side-by-side comparison shows style differences
4. Maintains aspect ratio for direct comparison

## Troubleshooting Guide

| Issue | Symptoms | Cause | Solution |
|-------|----------|-------|----------|
| **Aspect ratio change** | Output dimensions different | Model internal padding | Log source dimensions; validate output |
| **Alignment drift** | Subjects shifted from positions | Multi-element spatial reasoning | Reduce to 2 subjects; add spacing |
| **Color bleeding** | Colors from one element bleed to another | High-contrast boundaries | Soften edges; check blend mode |
| **Text misalignment** | Text offset from target position | Text-specific positioning | Increase font size; test separately |
| **Scale inconsistency** | Subject scales differently | Scale parameter handling | Use explicit pixel dimensions instead |
| **Background artifacts** | Visible seams or artifacts | Composition boundary issues | Use larger background image |
| **Memory error** | Processing fails mid-operation | Insufficient GPU memory | Reduce resolution or batch size |

## Best Practices Summary

1. **Start Simple**: Begin with single-subject compositions before complex multi-element scenes
2. **Test Alignment**: Use test suite before production for 2+ subject compositions
3. **Document Parameters**: Keep detailed records of successful positioning parameters
4. **Validate Output**: Always check aspect ratio and element alignment post-processing
5. **Plan Fallbacks**: Have manual composition method ready for failed automated attempts
6. **Batch Test**: Process 5-10 test compositions before full production run
7. **User Disclosure**: Inform users of 15-20% alignment issue rate for complex compositions
8. **Quality Thresholds**: Establish minimum acceptance criteria for aspect ratio and alignment drift
