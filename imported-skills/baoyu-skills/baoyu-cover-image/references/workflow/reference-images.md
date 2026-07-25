# Reference Image Handling

Guide for processing user-provided reference images in cover generation.

## Input Detection

| Input Type | Action |
|------------|--------|
| Image file path provided | Copy to `refs/` → can use `--ref` |
| Image in conversation (no path) | **ASK user for file path** with AskUserQuestion |
| User can't provide path | Extract style/palette verbally → append to prompt (NO frontmatter references) |

**CRITICAL**: Only add `references` to prompt frontmatter if files are ACTUALLY SAVED to `refs/` directory.

## File Saving

**If user provides file path**:
1. Copy to `refs/ref-NN-{slug}.{ext}` (NN = 01, 02, ...)
2. **Only** create description file `refs/ref-NN-{slug}.md` when model does NOT support `--ref` (see below)
3. Verify image file exists before proceeding

**When to create description file**:

| Situation | Action |
|-----------|--------|
| Model supports `--ref` (Google, OpenAI, OpenRouter, Replicate, Seedream 4.0+) | Copy image only. **No description file needed.** Pass via `--ref` at generation. |
| Model does NOT support `--ref` (Jimeng, Seedream 3.0) | Copy image + create description file. Embed description in prompt text. |

**Description File Format** (only when needed):
```yaml
---
ref_id: NN
filename: ref-NN-{slug}.{ext}
usage: direct | style | palette
---
[Character or style description to embed in prompt]
```

| Usage | When to Use |
|-------|-------------|
| `direct` | Model sees reference image directly; required if people must appear in output |
| `style` | Extract visual style only (not for people who must appear) |
| `palette` | Extract color scheme only |

## Verbal Extraction (No File)

When user can't provide file path:
1. Analyze image visually, extract: colors, style, composition
2. Create `refs/extracted-style.md` with extracted info
3. DO NOT add `references` to prompt frontmatter
4. Append extracted style/colors directly to prompt text

## Deep Analysis ⚠️ CRITICAL

References are high-priority inputs. Extract **specific, concrete, reproducible** elements:

| Analysis | Description | Example (good vs bad) |
|----------|-------------|----------------------|
| **Brand elements** | Logos, wordmarks, specific typography | Good: "Logo uses vertical parallel lines for 'm'" / Bad: "Has a logo" |
| **Signature patterns** | Unique decorative motifs, textures | Good: "Woven intersecting curves forming diamond grid" / Bad: "Has patterns" |
| **Color palette** | Exact hex values for key colors | Good: "#2D4A3E dark teal, #F5F0E0 cream" / Bad: "Dark and light colors" |
| **Layout structure** | Specific spatial arrangement | Good: "Bottom 30% dark banner with branding" / Bad: "Has a banner" |
| **Typography** | Font style, weight, spacing, case | Good: "Uppercase, wide letter-spacing" / Bad: "Has text" |
| **Content/subject** | What the reference depicts | Factual description |
| **Usage recommendation** | `direct` / `style` / `palette` | Based on analysis |

**Output format**: List each element as bullet that can be copy-pasted into prompt as mandatory instruction.

### Character Analysis ⚠️ If Reference Contains People

Use `usage: direct` so model sees the reference image. Additionally describe per character: **appearance**, **pose**, **clothing** → with **transformation rules** (stylize to match rendering).

| Extract | Good | Bad |
|---------|------|-----|
| Appearance | "Woman: long wavy blonde hair, friendly smile" | "A woman" |
| Pose | "Standing, facing camera, confident posture" | "Standing" |
| Clothing | "Dark T-shirt, business casual" | "Formal" |
| Transform | "Flat-vector cartoon, keep hair color & clothing" | "Make cartoon" |

Use `usage: direct`. Output each character as MUST/REQUIRED prompt instruction.

## Verification Output

**For saved files**:
```
Reference Images Saved:
- ref-01-{slug}.png ✓ (can use --ref)
- ref-02-{slug}.png ✓ (can use --ref)
```

**For extracted style**:
```
Reference Style Extracted (no file):
- Colors: #E8756D coral, #7ECFC0 mint...
- Style: minimal flat vector, clean lines...
→ Will append to prompt text (not --ref)
```

## Priority Rules

When user provides references, they are **HIGH PRIORITY**:

- **References override defaults**: If reference conflicts with preferred palette/rendering, reference takes precedence
- **Concrete > abstract**: Extract specific elements — not vague "clean style"
- **Mandatory language**: Use "MUST", "REQUIRED" in prompt for reference elements
- **Visible in output**: Verify elements are present after generation; strengthen prompt if not
