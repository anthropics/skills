---
name: a11y-auditor
description: Accessibility audit guidance and WCAG compliance checking. Use when users need to evaluate web content accessibility, check WCAG compliance, review for screen reader compatibility, audit color contrast, assess keyboard navigation, or improve accessibility of digital content. Triggers on requests like "check accessibility", "WCAG audit", "screen reader compatible", "accessibility review", "ADA compliance", or "a11y check".
---

# Accessibility Auditor

Guide accessibility evaluations using WCAG standards as the reality benchmark for validation.

## WCAG Quick Reference

### Conformance Levels

| Level | Meaning | Typical Requirement |
|-------|---------|---------------------|
| **A** | Minimum | Legal baseline in most jurisdictions |
| **AA** | Standard | Most common compliance target |
| **AAA** | Enhanced | Specialized contexts (government, healthcare) |

### Four Principles (POUR)

1. **Perceivable** - Information must be presentable to users
2. **Operable** - Interface must be navigable and usable
3. **Understandable** - Content and operation must be clear
4. **Robust** - Content must work with assistive technologies

## Audit Checklist by Category

### 1. Text Alternatives (WCAG 1.1)

**Images**
- [ ] All `<img>` have `alt` attributes
- [ ] Decorative images use `alt=""` or CSS background
- [ ] Complex images have extended descriptions
- [ ] Alt text describes function, not appearance

**Verification:**
```
Check: Does alt text answer "What information does this image convey?"
Pass: "Submit button" or "Company logo linking to homepage"
Fail: "image.jpg" or "picture of a button"
```

### 2. Time-Based Media (WCAG 1.2)

- [ ] Videos have captions
- [ ] Audio has transcripts
- [ ] Live audio has real-time captions (AA)
- [ ] Audio descriptions for visual-only content (AA)

### 3. Adaptable Content (WCAG 1.3)

**Structure**
- [ ] Headings in logical order (h1 → h2 → h3)
- [ ] Lists use proper `<ul>`, `<ol>`, `<dl>` markup
- [ ] Tables have headers (`<th>`) and scope
- [ ] Forms have associated labels

**Verification:**
```
Test: Read content with CSS disabled
Pass: Content order and structure still make sense
Fail: Content becomes jumbled or loses meaning
```

### 4. Distinguishable Content (WCAG 1.4)

**Color Contrast**

| Text Type | AA Requirement | AAA Requirement |
|-----------|----------------|-----------------|
| Normal text | 4.5:1 | 7:1 |
| Large text (18pt+) | 3:1 | 4.5:1 |
| UI components | 3:1 | 3:1 |

- [ ] Text meets contrast ratios
- [ ] Color is not only indicator of meaning
- [ ] Text resizes to 200% without loss
- [ ] No horizontal scroll at 320px width (AA)

**Verification:**
```
Tool: Use contrast checker (WebAIM, Colour Contrast Analyser)
Test: View in grayscale - is all information still clear?
```

### 5. Keyboard Accessible (WCAG 2.1)

- [ ] All functions available via keyboard
- [ ] No keyboard traps
- [ ] Focus order is logical
- [ ] Focus indicator is visible
- [ ] Skip navigation link present

**Verification:**
```
Test: Unplug mouse, navigate entire site using only:
- Tab / Shift+Tab (move focus)
- Enter / Space (activate)
- Arrow keys (within components)
- Escape (close dialogs)

Pass: Can access all content and functions
Fail: Any element unreachable or traps focus
```

### 6. Timing (WCAG 2.2)

- [ ] Time limits can be extended or disabled
- [ ] Auto-updating content can be paused
- [ ] No content flashes more than 3 times/second

### 7. Navigation (WCAG 2.4)

- [ ] Pages have descriptive titles
- [ ] Focus order matches visual order
- [ ] Link purpose clear from text (or context)
- [ ] Multiple ways to find pages (AA)
- [ ] Headings and labels are descriptive

**Verification:**
```
Test: Read only the links on a page
Pass: Each link makes sense out of context
Fail: "Click here", "Read more", "Link" without context
```

### 8. Input Modalities (WCAG 2.5)

- [ ] Touch targets at least 44x44 CSS pixels
- [ ] Gestures have alternatives
- [ ] Labels match accessible names

### 9. Readable Content (WCAG 3.1)

- [ ] Page language declared (`lang` attribute)
- [ ] Language changes marked in content
- [ ] Unusual words/abbreviations explained

### 10. Predictable Behavior (WCAG 3.2)

- [ ] Focus doesn't trigger unexpected changes
- [ ] Input doesn't trigger unexpected changes
- [ ] Navigation is consistent across pages

### 11. Input Assistance (WCAG 3.3)

- [ ] Errors clearly identified
- [ ] Error suggestions provided
- [ ] Labels/instructions for input
- [ ] Error prevention for legal/financial (AA)

**Verification:**
```
Test: Submit forms with errors intentionally
Pass: Error messages are specific and adjacent to field
Fail: Generic "Form error" or error at page top only
```

### 12. Compatible Markup (WCAG 4.1)

- [ ] Valid HTML (no duplicate IDs)
- [ ] ARIA used correctly
- [ ] Custom components have proper roles
- [ ] Status messages announced (AA)

## Screen Reader Testing

### Quick Test Protocol

1. **Headings navigation**: Press `H` to jump between headings
2. **Links list**: View all links (should make sense)
3. **Forms mode**: Tab through form, verify labels read
4. **Images**: Confirm alt text is appropriate
5. **Dynamic content**: Check live regions announce updates

### Common Screen Readers

| Platform | Screen Reader | Key Commands |
|----------|---------------|--------------|
| Windows | NVDA (free) | Insert = NVDA key |
| Windows | JAWS | Insert = JAWS key |
| macOS/iOS | VoiceOver | VO = Ctrl+Option |
| Android | TalkBack | Swipe gestures |

## Automated Testing Tools

### Integrate in Workflow

```bash
# Axe-core (CLI)
npx @axe-core/cli https://example.com

# Pa11y
npx pa11y https://example.com

# Lighthouse (Chrome)
lighthouse --only-categories=accessibility https://example.com
```

### Tool Limitations

Automated tools catch ~30-40% of issues. Manual testing required for:
- Alt text quality (not just presence)
- Focus order logic
- Cognitive accessibility
- Actual screen reader experience

## Audit Report Structure

```markdown
# Accessibility Audit Report

**Site/Application**: [Name]
**Date**: [Date]
**Standard**: WCAG 2.1 Level AA
**Auditor**: [Name]

## Executive Summary
[Overall findings, critical issues count, pass rate]

## Critical Issues (Must Fix)
### Issue 1: [Description]
- **WCAG Criterion**: [Number and name]
- **Location**: [URL/component]
- **Impact**: [User groups affected]
- **Recommendation**: [How to fix]

## Major Issues (Should Fix)
[Same format]

## Minor Issues (Consider Fixing)
[Same format]

## Passed Criteria
[List of criteria that passed]

## Testing Methodology
[Tools used, manual tests performed]
```

## Quick Fixes Reference

| Issue | Quick Fix |
|-------|-----------|
| Missing alt text | Add descriptive `alt` attribute |
| Low contrast | Increase color difference (use checker) |
| Missing form labels | Add `<label for="id">` |
| No focus indicator | Add `:focus { outline: 2px solid }` |
| Missing page title | Add descriptive `<title>` |
| No skip link | Add hidden skip to main content link |
| Missing lang | Add `<html lang="en">` |
