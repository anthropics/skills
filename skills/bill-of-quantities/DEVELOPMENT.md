# Bill of Quantities Skill - Setup & Development Guide

## Skill Location

```
/Users/user/Documents/GitHub/skills/skills/bill-of-quantities/
├── SKILL.md                    # Main skill definition
├── LICENSE.txt                 # MIT License
├── references/
│   └── standards.md           # BoQ standards & reference data
├── evals/
│   └── evals.json             # Test cases for evaluation
├── scripts/
│   └── generate_sample_boq.py  # Helper to generate sample outputs
└── evals/                      # (created during eval runs)
    └── [iteration results]
```

## Quick Start

### 1. View the Skill

```bash
cat /Users/user/Documents/GitHub/skills/skills/bill-of-quantities/SKILL.md
```

### 2. Review Test Cases

```bash
cat /Users/user/Documents/GitHub/skills/skills/bill-of-quantities/evals/evals.json
```

### 3. Generate Sample BoQ Outputs

```bash
cd /Users/user/Documents/GitHub/skills/skills/bill-of-quantities
python scripts/generate_sample_boq.py
```

This creates sample outputs showing expected format.

## Test Cases Overview

The skill has 3 evaluation scenarios:

### Eval 1: Simple Single-Storey Building

- **Complexity**: Low-Medium
- **Input**: Clear specifications with dimensions
- **Tests**: Basic extraction, section organization, standard BoQ format
- **Expected**: 20+ items, accurate quantity calculations

### Eval 2: Medium-Complexity Multi-Storey

- **Complexity**: Medium-High
- **Input**: Detailed 3-storey residential building specs
- **Tests**: Complex area calculations, multiple finishes, full MEP systems
- **Expected**: 40+ items, organized sections, complete coverage

### Eval 3: Partial Specs with Inference

- **Complexity**: High (Assessment of assumptions & reasoning)
- **Input**: Incomplete renovation brief
- **Tests**: Estimation, assumption documentation, confidence levels
- **Expected**: 15-25 items with clearly marked assumptions & confidence levels

## Evaluation Workflow

### Phase 1: Run Initial Tests

When you're ready to evaluate the skill:

1. **Spawn subagents** (with-skill vs. baseline) for each test case
2. The **with-skill** version uses this skill to generate BoQ
3. The **baseline** version attempts the same task without the skill
4. Compare outputs for quality, completeness, accuracy

### Phase 2: Review Outputs

In the evaluation viewer, you'll see:

- **Qualitative outputs**: Generated BoQ documents, structure, clarity
- **Quantitative metrics**: Items generated, sections, accuracy of quantities
- **Assumptions documentation**: Quality of reasoning and flagged uncertainties

### Phase 3: Iterate

Based on feedback:

- Refine extraction methodology
- Improve section organization
- Enhance assumptions documentation
- Add missing guidance for edge cases

## Key Assertions to Evaluate

When running evals, consider these checks:

✓ **Completeness**: Does BoQ include all major items from specs?
✓ **Organization**: Are items properly grouped into RICS sections?
✓ **Accuracy**: Are quantities correctly calculated/extracted?
✓ **Clarity**: Are descriptions detailed enough for pricing?
✓ **Documentation**: Are assumptions clearly listed?
✓ **Format**: Is output in requested format (CSV, Markdown, etc.)?
✓ **Consistency**: Are units consistent? (m² not mixed with m³)
✓ **Flags**: Missing information clearly noted?

## Reference Materials

### For Understanding BoQ Standards

See `references/standards.md` which includes:

- RICS classification & section codes
- Standard unit conventions
- Conversion factors
- Common building dimensions
- Specification keywords
- Calculation examples
- Common mistakes

### Sample Output

Run the helper script to see example outputs:

```bash
python scripts/generate_sample_boq.py
ls sample_outputs/
```

This shows:

- CSV/Excel format structure
- Markdown table layout
- Assumptions documentation
- Section breakdowns

## Integration with Skill-Creator

To run full evaluations with the skill-creator framework:

```bash
# From the skills directory
python -m skills.skill_creator.scripts.evaluate_skill \
  --skill bill-of-quantities \
  --iteration 1
```

Or use the web-based evaluation viewer:

```bash
python -m skills.skill_creator.eval-viewer.generate_review.py \
  bill-of-quantities-workspace/iteration-1 \
  --skill-name bill-of-quantities
```

## Development Workflow

### Iteration Cycle

1. **Run evals** on current skill version
2. **Review outputs** in viewer (qualitative + quantitative)
3. **Gather feedback** on BoQ quality, assumptions, completeness
4. **Refine SKILL.md** based on feedback
5. **Repeat** until satisfied

### Common Improvements

- **Better extraction methodology**: More explicit rules for ambiguous specs
- **Enhanced assumption documentation**: Templates for common assumptions
- **Added examples**: More diverse project types in guidance
- **Precision guidance**: When to round quantities, handling tolerances
- **Error detection**: Flagging suspicious quantities or duplicates

## Tips for Quality BoQ Generation

### Critical Success Factors

1. **Parse thoroughly**: Extract ALL items from specs, don't miss details
2. **Calculate correctly**: Verify area/volume calculations against building dimensions
3. **Organize logically**: Use consistent section structure (RICS standard)
4. **Document assumptions**: Every inference should be explained
5. **Flag gaps**: Missing specs should be noted for clarification

### Common Pitfalls to Avoid

- Don't double-count items across sections
- Don't ignore services (electrical, plumbing)
- Don't skip finishes (paint, flooring)
- Don't use imprecise descriptions
- Don't forget waste allowances in specs

## Next Steps

1. ✅ **Skill created** - SKILL.md written with comprehensive guidance
2. ✅ **Test cases defined** - 3 evals covering different complexity levels
3. ✅ **References provided** - Standards & sample outputs available
4. 🔄 **Ready for evaluation** - Run tests with skill-creator framework
5. 📊 **Iterate based on results** - Refine based on output quality

## Questions?

For detailed skill definition: `cat SKILL.md`
For test case details: `cat evals/evals.json`
For standards reference: `cat references/standards.md`
For sample outputs: `python scripts/generate_sample_boq.py`

---
**Skill Status**: Draft - Ready for initial evaluation
**Created**: 2026-04-21
**Version**: 1.0
