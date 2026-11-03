# Skill Debugging Diagnostic Checklist

Use this checklist to systematically debug why a skill isn't triggering.

## Phase 1: Installation & Discovery

- [ ] **File exists**: Skill folder at `~/.claude/skills/[name]/` or `.claude/skills/[name]/`
- [ ] **SKILL.md present**: File named exactly `SKILL.md` (case-sensitive)
- [ ] **Folder name correct**: No spaces, special characters, or uppercase
- [ ] **Location visible**: `ls ~/.claude/skills/` shows the folder

## Phase 2: YAML Frontmatter

- [ ] **Frontmatter exists**: File starts with `---`
- [ ] **Proper delimiters**: Three dashes (`---`) at start and end
- [ ] **name field**: `name: skill-name` present
- [ ] **description field**: `description: ...` present
- [ ] **Name matches folder**: YAML `name:` exactly matches folder name
- [ ] **Kebab-case**: Name uses lowercase with hyphens (not snake_case or camelCase)

## Phase 3: Description Quality

- [ ] **Not too short**: Description ≥ 50 characters
- [ ] **Not too long**: Description ≤ 150 characters
- [ ] **Specific**: Mentions what the skill actually does
- [ ] **Includes use case**: Says "for X" or "when Y"
- [ ] **No vague words**: Avoids "helps", "various", "assists", "many"
- [ ] **Has keywords**: Includes words users would naturally say
- [ ] **Unique**: Not too similar to other skill descriptions

## Phase 4: Content Structure

- [ ] **Capabilities section**: Lists specific features
- [ ] **When to Use**: Explains triggering conditions (or similar section)
- [ ] **Usage examples**: At least 3-5 concrete examples
- [ ] **Clear purpose**: First paragraph explains what it does

## Phase 5: Trigger Keywords

- [ ] **Keyword alignment**: Description keywords match how users ask
- [ ] **Domain-specific**: Uses terminology from the problem domain
- [ ] **Action verbs**: Includes what it does (analyze, calculate, generate, etc.)
- [ ] **Noun specificity**: Clear what it operates on (financial data, code, images, etc.)

## Phase 6: Conflict Detection

- [ ] **No overlaps**: No other skill has very similar description
- [ ] **Clear differentiation**: Unique value vs other skills
- [ ] **Specific niche**: Focused on particular use case

## Quick Diagnostic Scores

### ✅ Healthy Skill (Should Trigger Well)
```yaml
name: financial-ratio-calculator
description: Calculates financial ratios (P/E, ROE, ROA, debt-to-equity) from company financial statements for investment analysis
```

**Checklist**:
- ✅ All phases pass
- ✅ Specific keywords: ratios, P/E, ROE, financial statements, investment
- ✅ Clear use case: "for investment analysis"
- ✅ 95 characters (good length)

### ⚠️ Problematic Skill (Rarely Triggers)
```yaml
name: data_analyzer
description: Helps analyze data
```

**Checklist**:
- ❌ Phase 2: Name not kebab-case (data_analyzer → data-analyzer)
- ❌ Phase 3: Too short (20 chars)
- ❌ Phase 3: Vague ("helps")
- ❌ Phase 3: No use case
- ❌ Phase 5: Generic keywords ("data")

## Debugging Priority Order

1. **Critical (Fix First)**
   - File not found
   - Invalid YAML
   - Name mismatch

2. **High (Fix Soon)**
   - Description too vague
   - No trigger keywords
   - Conflicts with other skills

3. **Medium (Improves Triggering)**
   - Missing "When to Use" section
   - No usage examples
   - Description too short/long

4. **Low (Polish)**
   - Better keyword optimization
   - More specific use case
   - Clearer differentiation

## After Fixing Checklist

- [ ] Updated YAML frontmatter
- [ ] Improved description with keywords
- [ ] Added/updated "When to Use" section
- [ ] Added usage examples
- [ ] Tested with Claude: "What would trigger [skill-name]?"
- [ ] Verified no conflicts: "Check skill conflicts"
- [ ] Tested actual triggering with natural query

## Maintenance Schedule

- **Weekly**: Test triggering of your most-used skills
- **Monthly**: Run full diagnostic on all skills
- **After adding new skill**: Check for conflicts with existing skills
- **After Claude updates**: Verify skills still trigger correctly
