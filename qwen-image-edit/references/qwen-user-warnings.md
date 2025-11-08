# Qwen-Image-Edit v2509: User Warnings & Communication Guide

## Mandatory User Disclosures

**IMPORTANT**: Any user-facing implementation of Qwen-Image-Edit MUST include these warnings. Legal and ethical responsibility requires transparent communication about AI model limitations.

## Primary Warning (Required for All Users)

### Standard Disclosure

Use this language in your application UI, help documentation, or terms of service:

> **Image Editing Notice**
>
> This application uses AI-powered image editing (Qwen-Image-Edit v2509). While powerful, the AI model has known limitations you should be aware of:
>
> **Aspect Ratio Changes**: The AI may modify image aspect ratios (proportions may be stretched or compressed) by up to 8%. We recommend:
> - Comparing output image dimensions to your original
> - Verifying that proportions look correct before finalizing
>
> **Alignment Variations**: When combining multiple images or adding elements, positioning may shift by 3-10 pixels from the specification. This is normal and expected behavior.
>
> **Quality Variability**: Results vary based on image content. We recommend testing with sample images before using for critical purposes.
>
> By using this feature, you acknowledge and accept these limitations.

### Condensed Version (For Space-Limited Contexts)

Use this in tooltips, status messages, or limited space:

> **AI-Generated Edits**: Qwen-Image-Edit may modify aspect ratios and element positioning. Always review results before finalizing.

### Expanded Version (For Detailed Documentation)

Use this in help articles, FAQs, or comprehensive guides:

> **Important Limitations of Qwen-Image-Edit v2509**
>
> Qwen-Image-Edit is a powerful but imperfect AI image editing tool. It excels at certain tasks but struggles with others. To get the best results and avoid disappointment, please understand these limitations:
>
> **1. Aspect Ratio Changes (Most Important)**
> The AI frequently modifies the aspect ratio (width-to-height proportion) of your images. Changes typically range from 1-8%, but can occasionally be larger. Your painting might appear wider, taller, or compressed.
>
> *What to do:*
> - Measure your original image dimensions (e.g., 1024×768)
> - Check the output dimensions (e.g., 1024×775)
> - Calculate if the proportion changed significantly
> - If unacceptable, you may need to manually adjust or use traditional editing
>
> **2. Element Alignment Issues**
> When you request multiple images to be combined (e.g., a character and a background), the AI sometimes positions them slightly off from where you specified—typically 3-10 pixels.
>
> *What to do:*
> - Expect minor misalignments
> - For critical applications, manually review and adjust
> - Provide more specific positioning parameters
> - Accept "good enough" for casual use
>
> **3. Text Rendering Problems**
> - Small text (under 12pt) may be illegible or distorted
> - Chinese characters sometimes render incorrectly (~5% failure rate)
> - Rotated text often looks wrong
> - Mixed Chinese-English text has spacing issues
>
> *What to do:*
> - Use font sizes 16pt or larger
> - Test text with a sample first
> - Keep text horizontal (don't rotate)
> - Use single-language text blocks
>
> **4. When NOT to Use**
> - Medical imaging (accuracy critical)
> - Scientific measurements (precision required)
> - Professional product photography (quality standards high)
> - Any application where pixel-perfect accuracy is essential
>
> **5. When It Works Well**
> - Adding a single character to a scene background
> - Simple text overlays on images
> - Product photography with minor adjustments
> - Casual meme creation
> - Portfolio showcase images (some review acceptable)

## Layered Warning System

Implement warnings at different levels based on user actions:

### Level 1: Pre-Operation Warning (Before Starting)

**Trigger**: User initiates any image editing operation

**Message**:
> "This uses AI-powered image editing. The model may modify aspect ratios and element positioning. Continue?"
> [Continue] [Learn More]

**Implementation**:
```
Display warning dialog before starting operation
Include link to detailed information
Require explicit confirmation to proceed
```

### Level 2: Quality Notice (After Completion)

**Trigger**: Image editing operation completes

**Message**:
> "Image editing complete. Please review for aspect ratio changes and alignment before finalizing. [View Checklist]"

**Checklist Provided**:
```
□ Compare output dimensions to original
□ Check if proportions look correct
□ Verify element positioning is acceptable
□ Review text rendering quality (if applicable)
□ Accept or try alternative
```

### Level 3: Feature-Specific Warnings

**For Multi-Image Compositions**:
> "Combining multiple elements (3+ subjects) has a 15-20% failure rate. Simpler compositions are more reliable. Continue?"

**For Text on Chinese Characters**:
> "Chinese text rendering has a ~5% corruption rate. Consider testing with a sample first."

**For Aspect-Critical Content**:
> "This feature may modify image proportions. For aspect-critical work, manual adjustment may be needed."

### Level 4: Error Recovery

**If Operation Fails**:
> "Image editing failed or produced poor results. This is normal due to AI limitations. Try again with different parameters or use manual editing."

## User-Facing Disclosure Templates

### For Website Terms of Service

```markdown
### AI Image Editing Tool

Our application includes Qwen-Image-Edit v2509 powered by Alibaba Cloud.
This AI model can:
- Combine multiple images into scenes
- Add text to images
- Modify and enhance images

This model has limitations:
- May modify image aspect ratios by 1-8%
- May position elements 3-10px off from specifications
- Struggles with complex multi-element compositions
- May render small text or Chinese characters incorrectly

Users accept these limitations when using this feature.
We do not guarantee aspect-ratio preservation or pixel-perfect accuracy.
```

### For Help Documentation

```markdown
## Known Limitations

### Aspect Ratio Changes
The model sometimes changes your image proportions. This is a known limitation.
- Always check output dimensions
- Compare proportions to original
- The AI is not suitable for aspect-ratio-critical work

### Alignment Variations
When combining images, elements may shift 3-10 pixels.
- Expected behavior, not an error
- More common with complex compositions (3+ elements)
- Simpler compositions are more reliable

### Text Rendering
- Small text (<12pt) doesn't render clearly
- Chinese characters occasionally corrupt
- Rotation not supported
- Mixed language text has spacing issues

### When to Use Alternatives
If any of these limitations are unacceptable for your use case,
we recommend traditional image editing tools like Photoshop.
```

### For Support Docs / FAQ

```markdown
## Why did my image's proportions change?

This is a known limitation of Qwen-Image-Edit. The AI model sometimes
modifies aspect ratios by 1-8% during processing. To address this:

1. Check the output dimensions (right-click > Properties)
2. Calculate if the change is significant
3. If unacceptable, try again or use manual editing

This behavior is expected and not a bug.

## Why is my text positioned incorrectly?

Text and element positioning has typical accuracy of ±3-10px.
For critical positioning, consider using manual editing tools.

## Should I use this for professional work?

Use with caution. The AI is good for:
- Portfolio images with some human review
- Casual meme creation
- Non-critical compositions

The AI is NOT suitable for:
- Medical imaging
- Scientific measurements
- Professional product photography
- Any aspect-ratio-critical work
```

## Issue-Specific Warnings

### Aspect Ratio Warning

**When to show**: Before or after aspect-ratio-sensitive operations

**Message**:
> "Your image aspect ratio may be modified. Always verify output dimensions:
> - Original: 1024×768 (1.33:1)
> - Output: Check your file properties
> - If ratio changed >2%, consider alternative methods"

### Alignment Warning

**When to show**: Before multi-element compositions (3+ subjects)

**Message**:
> "Complex compositions (3+ elements) have a 15-20% misalignment rate.
> Elements may shift 5-15px from specified positions.
> For critical work, limit to 2 subjects or use manual editing."

### Text Rendering Warning

**When to show**: Before adding small text or Chinese characters

**Message for Small Text**:
> "Text under 12pt may not render clearly. Use 16pt or larger for best results."

**Message for Chinese**:
> "Chinese character rendering occasionally fails (~5% of cases). Consider testing a sample first."

### Complex Composition Warning

**When to show**: Before attempting 4+ subject composition

**Message**:
> "Compositions with 4+ elements have limited reliability. For best results:
> - Limit to 2 subjects maximum, OR
> - Compose in stages (background + subject 1, then add subject 2)"

## Recommended Warning Workflow

```
User Request
    ↓
[Evaluate Complexity]
    ├→ Simple (1-2 subjects, English text, standard aspect ratio)
    │   └→ Show Level 1 warning only
    │
    ├→ Moderate (3 subjects OR Chinese text OR aspect-critical)
    │   └→ Show Level 1 + Level 3 warnings
    │
    └→ Complex (4+ subjects, mixed language, critical accuracy)
        └→ Show Level 1 + Level 3 + recommendation to use alternatives

[User Proceeds]
    ↓
[Process Image]
    ↓
[Complete Operation]
    ↓
[Show Level 2 quality notice with checklist]
    ↓
[User Reviews Results]
    ├→ Acceptable
    │   └→ User finalizes
    │
    └→ Not Acceptable
        ├→ Retry with adjusted parameters
        └→ Or use manual editing tools
```

## Accessibility & Clear Communication

### Principle 1: Be Honest About Limitations

- Use clear, non-technical language
- Avoid jargon (explain "aspect ratio" = "proportions")
- Provide specific examples
- Don't minimize serious limitations

**Bad**: "May have minor variations in composition"
**Good**: "Elements may move 3-10 pixels from where you specify"

### Principle 2: Provide Clear Guidance

- Tell users what to check
- Provide step-by-step procedures
- Explain what "acceptable" means
- Suggest alternatives when appropriate

### Principle 3: Don't Blame Users

- Limitations are model limitations, not user error
- Use passive voice: "Text may be positioned incorrectly" not "You positioned text incorrectly"
- Normalize failures: "This is normal behavior for this AI model"

### Principle 4: Respect User Autonomy

- Let users make informed decisions
- Don't force warnings on every action (causes fatigue)
- Provide "Learn More" links, not just scary messages
- Trust users to handle complexity

## Content Warning Variations by Context

### For Casual Meme Creator
```
"Hey! Just so you know, our AI sometimes shifts things around
slightly and might change your image proportions a bit.
Usually looks great, but always do a quick check before you share!"
```

### For Professional Miniature Painter
```
"Qwen-Image-Edit uses AI composition with known limitations:
- Aspect ratio drift: 1-8% (typical)
- Alignment accuracy: ±5-10px (expected)
- Recommended for portfolio use with human review
- Not suitable for critical product photography

See documentation for detailed technical specifications."
```

### For Hobbyist/Educational User
```
"This AI tool is great for fun projects! Just know that it might:
- Change image proportions slightly (check the output)
- Position things a few pixels off (totally normal)
- Struggle with text smaller than 12pt (use bigger text)

It's not perfect, but it's very useful for learning and experimentation!"
```

## Legal Compliance Notes

### Liability Disclaimer

Consider including language like:

> "Image editing results are provided as-is. We do not guarantee
> aspect-ratio preservation, pixel-perfect accuracy, or any specific
> quality level. Users are responsible for reviewing results before use,
> particularly for professional or critical applications."

### Data Privacy Notice

> "Images submitted for editing are processed by Alibaba Cloud's
> Qwen-Image-Edit service. By using this feature, you agree to their
> terms of service and data processing practices."

### AI Disclosure

> "This application uses artificial intelligence. AI-generated content
> may contain errors, artifacts, or unexpected behaviors.
> Always review outputs before use or sharing."

## Testing User Understanding

After presenting warnings, consider:

1. **Confirmation Dialog**: "Do you understand that aspect ratios may change?"
2. **Knowledge Check**: "What are the typical alignment variations?" (educational)
3. **Acceptance Checkbox**: "I understand the limitations and accept the risks"

This demonstrates informed consent and reduces liability.

## Support Resources to Link

Provide links to:
- [Detailed Limitations Guide] - Full technical specifications
- [Best Practices] - How to use the tool successfully
- [Troubleshooting] - Common issues and solutions
- [Alternatives] - When to use other tools
- [Report Issue] - How to provide feedback

## Periodic Reminder System

For users who repeatedly operate the tool:

**First use**: Show full warning
**Uses 2-5**: Show condensed warning
**Uses 6+**: Show brief notice with link to full warning

This balances user education with user experience.

## Multilingual Warning Templates

If supporting Chinese users:

**Simplified Chinese**:
> "使用AI图像编辑工具的注意事项：
> - 可能改变图像纵横比（比例变化1-8%）
> - 元素位置可能偏移3-10像素
> - 小字体（<12pt）可能渲染不清楚
>
> 请在最终使用前检查结果。"

**Traditional Chinese**:
> "使用AI圖像編輯工具的注意事項：
> - 可能改變圖像縱橫比（比例變化1-8%）
> - 元素位置可能偏移3-10像素
> - 小字體（<12pt）可能渲染不清楚
>
> 請在最終使用前檢查結果。"

## Summary: Implementation Checklist

- [ ] Show mandatory warning before operation (Level 1)
- [ ] Show quality notice after completion (Level 2)
- [ ] Add feature-specific warnings for complex operations (Level 3)
- [ ] Provide detailed documentation for each limitation
- [ ] Include troubleshooting guide for common issues
- [ ] Offer suggestions for alternative tools when appropriate
- [ ] Use clear, non-technical language in all warnings
- [ ] Respect user autonomy (inform, don't prevent)
- [ ] Provide "Learn More" links in all warning messages
- [ ] Test understanding through confirmation or educational questions
- [ ] Include legal disclaimers in terms of service
- [ ] Consider multilingual support for user base
- [ ] Implement warning fatigue prevention (different messaging per use count)
- [ ] Gather user feedback on warning effectiveness
- [ ] Update warnings as model improves or limitations change

This comprehensive warning system ensures users are informed while maintaining a positive user experience.
