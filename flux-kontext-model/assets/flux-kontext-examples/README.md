# FLUX.1 Kontext Examples and Reference Resources

This directory contains comprehensive examples, prompts, and quality benchmarks for FLUX.1 Kontext image generation workflows.

## Contents

### example-prompts.md
Complete collection of production-tested prompts for miniature painting workflows:

- **Character Miniatures:** Fantasy knights, dark elves, dwarves with detailed prompt templates
- **Creature Miniatures:** Dragons, demons, celestial beings with specialized lighting descriptions
- **Complex Scenes:** Dioramas, castles, and narrative compositions
- **Quick Iteration Examples:** Batch processing templates with Lightning LoRA
- **Professional Workflows:** Portfolio pieces, production efficiency, and fast preview patterns

Each example includes:
- Complete prompt text (copy-paste ready)
- Quality level and estimated generation time
- Best use case recommendations
- Prompt structure breakdown

**Use this file for:** Finding working prompts, understanding effective prompt patterns, and adapting examples to your specific subjects.

### quality-benchmarks.md
Detailed performance benchmarks and quality metrics across different configurations:

#### Quality Metrics
- SSIM scores for different quantization levels
- Visual quality assessment across configurations
- Impact of step count, guidance scale, and other parameters
- Inpainting quality and denoise parameter analysis
- Multi-image control consistency benchmarks

#### Hardware Performance
- RTX 4090 benchmarks (standard, optimized, Lightning LoRA)
- RTX 4060 benchmarks (limited VRAM scenarios)
- CPU inference performance (batch processing)
- Memory usage and efficiency metrics

#### Production Recommendations
- Small batch (1-4 images): 200 images/hour, 97% quality
- Medium batch (5-20 images): 220 images/hour, 97% quality
- Large batch (20+ images): 450+ images/hour, 94% quality

**Use this file for:** Optimizing your specific hardware, understanding quality/performance tradeoffs, and selecting appropriate configurations for your use case.

## Quick Start: Using These Resources

### For Prompt Development
1. Open `example-prompts.md`
2. Find a similar subject to your target miniature
3. Copy the prompt template
4. Customize material, technique, subject, and lighting details
5. Test with your FLUX.1 Kontext setup

### For Performance Optimization
1. Open `quality-benchmarks.md`
2. Find your hardware profile (RTX 4090, 4060, CPU, etc.)
3. Select appropriate configuration based on quality needs
4. Note VRAM requirements and estimated times
5. Implement recommended settings in your pipeline

### For Production Planning
1. Check Production Workflow Benchmarks section
2. Select configuration matching your constraints (quality, time, throughput)
3. Calculate resources needed for your batch size
4. Plan scheduling based on images/hour metrics

## Integration with Skill Resources

These examples work together with the skill's reference documentation:

```
Your Workflow Decision:
        │
        ├─ Need a prompt? → example-prompts.md
        │
        ├─ Want to optimize performance? → quality-benchmarks.md
        │
        ├─ Need detailed guidance? → ../flux-kontext-prompting.md
        │
        ├─ Need capability details? → ../flux-kontext-capabilities.md
        │
        ├─ Want to optimize inference? → ../flux-kontext-optimization.md
        │
        └─ Setting up ComfyUI? → ../flux-kontext-comfyui-workflow.md
```

## Example Workflows

### Scenario 1: Portfolio Piece Development

**Goal:** Create high-quality miniature painting for gallery display

**Prompt Selection:** Look for "Portfolio Piece" examples in `example-prompts.md`
**Configuration:** See "Premium/Client Deliverables" in `quality-benchmarks.md`
**Expected Time:** 60-90 seconds per image
**Quality Level:** 99-100%

### Scenario 2: Batch Commercial Production

**Goal:** Generate 50 variations of miniature designs efficiently

**Prompt Selection:** Use "Production Efficiency" template from `example-prompts.md`
**Configuration:** See "Production/Commercial Quality" in `quality-benchmarks.md`
**Expected Throughput:** 200 images/hour
**Quality Level:** 97%

### Scenario 3: Real-Time Creative Iteration

**Goal:** Rapidly explore different styles and subjects

**Prompt Selection:** Use "Fast Preview" template from `example-prompts.md`
**Configuration:** See "Interactive/Real-Time Use" in `quality-benchmarks.md`
**Expected Time:** 8 seconds per image
**Quality Level:** 94% (acceptable for preview)

## Prompt Engineering Tips from Examples

### Material Selection
```
Available materials in examples:
- Acrylic: Fast-drying, opaque matte finish
- Oil: Rich colors, glossy appearance, transparent glazing
- Watercolor: Transparent, luminous, delicate
- Gouache: Opaque watercolor, matte finish
- Mixed Media: Multiple techniques combined
```

### Technique Descriptions
```
Featured techniques:
- Wet Blending: Smooth color transitions, realistic shading
- Glazing: Transparent layers, depth building
- Drybrushing: Textured details, weathered appearance
- Stippling: Pointillist technique for fine detail
- Impasto: Thick visible brushstrokes, dimensional texture
```

### Lighting Patterns
```
Effective lighting descriptions:
- Sidelighting: Dimensional, emphasizes texture
- Backlighting: Creates separation, dramatic mood
- Overhead: Professional, shadowless, technical display
- Candlelit: Warm, intimate, atmospheric
- Cinematic: Complex three-point lighting, storytelling
```

### Photography Details
```
Resolution considerations (from benchmarks):
- 512x512: Good previews, fast iteration (15s)
- 768x768: Excellent production standard (45s) ← Most used
- 1024x1024: Premium quality (90s)
- 1536x1536: Maximum detail for prints (180s)

Aspect ratio recommendations:
- 1:1 Square: Gallery-friendly, balanced composition
- 4:3 Standard: Traditional photography, classic proportions
- 16:9 Widescreen: Dramatic, cinematic, landscape-heavy
- 3:2 Professional: Professional photography standard
```

## Quality Expectations by Configuration

### Q4_K + 20 Steps (Most Common)
- **Quality Score:** 97% (excellent)
- **Visual:** Imperceptible quality loss vs full precision
- **Time:** 18 seconds per 768x768 image
- **VRAM:** 8GB peak
- **Best for:** Production standard, portfolio pieces
- **Appearance:** Detailed, professional, painterly

### Q3_K + Lightning LoRA + 8 Steps (Real-Time)
- **Quality Score:** 94% (good)
- **Visual:** Minor quality reduction, acceptable for previews
- **Time:** 8 seconds per 512x512 image
- **VRAM:** 6GB peak
- **Best for:** Interactive workflows, rapid exploration
- **Appearance:** Good proportions, fewer fine details

### Full Precision + 28 Steps (Maximum Quality)
- **Quality Score:** 100% (baseline)
- **Visual:** Maximum detail and clarity
- **Time:** 45+ seconds per 768x768 image
- **VRAM:** 24GB required
- **Best for:** Award-winning portfolio pieces
- **Appearance:** Exceptional detail, museum-quality

## Customizing Examples

### Example Template for Your Subject
```
[Material] [Technique] miniature of [YOUR SUBJECT], [YOUR LIGHTING], [YOUR PHOTOGRAPHY]

Template from examples:
Acrylic wet blending miniature of fantasy [paladin/ranger/warrior],
[armor details], [sidelighting color], [lighting direction],
macro photography [aspect ratio], [depth of field], [background],
[quality descriptor], [texture details], [emotion/context]
```

### Testing Strategy (from Benchmarks)
1. Start with 512x512 and 8 steps (preview)
2. Evaluate quality and iterate on prompt
3. When satisfied, run at 768x768 and 20 steps
4. Final version at 1024x1024+ if needed

## File Organization

```
flux-kontext-examples/
├── README.md                    (This file)
├── example-prompts.md           (Production-tested prompts)
└── quality-benchmarks.md        (Performance metrics)
```

## Related Documentation

This examples directory is part of the complete FLUX.1 Kontext skill:

- **SKILL.md** - Main skill overview and core capabilities
- **flux-kontext-capabilities.md** - Feature documentation
- **flux-kontext-prompting.md** - Advanced prompting guide
- **flux-kontext-optimization.md** - Performance optimization
- **flux-kontext-comfyui-workflow.md** - ComfyUI integration
- **test-flux-kontext.py** - Validation script

## Feedback and Updates

As you use these examples, you may discover:
- Better working prompts for your specific style
- Performance improvements on different hardware
- Quality optimizations specific to your workflow
- New techniques or material combinations

Consider documenting your discoveries by extending `example-prompts.md` or creating additional benchmark data in `quality-benchmarks.md` for your specific use cases.

## Version Information

- FLUX.1 Kontext Model: 12B parameters
- Skill Version: 1.0
- Last Updated: 2025-01-08
- Compatible with: Diffusers, ComfyUI, llama.cpp

## Getting Started

1. **For immediate use:** Copy a prompt from `example-prompts.md` matching your subject
2. **For optimization:** Check `quality-benchmarks.md` for your hardware profile
3. **For deeper understanding:** Reference the skill's comprehensive guides in the references/ directory
4. **For validation:** Run `scripts/test-flux-kontext.py` to verify your setup

Happy miniature generating!
