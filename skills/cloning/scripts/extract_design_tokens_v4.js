/**
 * Design Token Extraction Script (v4.0 Enhanced)
 *
 * Extracts design tokens with confidence scoring for better Gemini prompts.
 * HIGH confidence tokens are brand-critical, MEDIUM are interactive, LOW are generic.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with confidence-scored design tokens
 */
(function() {
    const result = {
        colors: {
            high: [],    // Brand colors, primary CTAs, logo, hero
            medium: [],  // Interactive elements, nav, buttons
            low: []      // Generic UI (borders, subtle backgrounds)
        },
        typography: {
            primary: null,          // Most common body font
            heading: null,          // H1-H3 font (if different)
            accent: null,           // Decorative text
            fontFamilies: [],       // All font families
            fontSizes: [],          // All sizes used
            fontWeights: [],        // All weights used
            lineHeights: [],        // All line heights
            letterSpacings: []      // All letter spacings
        },
        fontManifest: {},           // Detailed font info with URLs
        spacing: {
            scale: [],              // Common spacing values
            pagePadding: null,      // Page edge padding
            sectionGaps: [],        // Gaps between sections
            componentGaps: []       // Gaps within components
        },
        shadows: [],                // Box shadows
        borderRadius: [],           // Border radius values
        borders: [],                // Border styles
        gradients: [],              // Gradient backgrounds
        customProperties: {},       // CSS variables
        timingConstants: {
            easings: [],
            durations: [],
            premiumEasing: null
        }
    };

    // Helper to convert RGB to Hex
    function rgbToHex(rgb) {
        if (!rgb || rgb === 'transparent' || rgb === 'rgba(0, 0, 0, 0)') return null;
        const match = rgb.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)/);
        if (!match) return rgb;
        const r = parseInt(match[1]);
        const g = parseInt(match[2]);
        const b = parseInt(match[3]);
        return '#' + [r, g, b].map(x => x.toString(16).padStart(2, '0')).join('');
    }

    // Helper to get selector
    function getSelector(el) {
        if (el.id) return '#' + el.id;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(' ').filter(c => c).slice(0, 2).join('.');
            if (classes) return el.tagName.toLowerCase() + '.' + classes;
        }
        return el.tagName.toLowerCase();
    }

    // Helper to determine color confidence
    function getColorConfidence(el, property) {
        const tag = el.tagName.toLowerCase();
        const className = (el.className && typeof el.className === 'string') ?
                          el.className.toLowerCase() : '';
        const id = el.id ? el.id.toLowerCase() : '';
        const combined = className + ' ' + id;

        // HIGH: Brand-critical elements
        if (combined.includes('logo') ||
            combined.includes('brand') ||
            combined.includes('primary') ||
            combined.includes('cta') ||
            combined.includes('hero') ||
            tag === 'h1' ||
            (tag === 'button' && combined.includes('primary'))) {
            return 'high';
        }

        // MEDIUM: Interactive elements
        if (tag === 'button' ||
            tag === 'a' ||
            combined.includes('btn') ||
            combined.includes('nav') ||
            combined.includes('link') ||
            combined.includes('card') ||
            combined.includes('icon') ||
            combined.includes('header') ||
            combined.includes('footer') ||
            tag === 'h2' ||
            tag === 'h3') {
            return 'medium';
        }

        // LOW: Generic UI
        return 'low';
    }

    // ==========================================================================
    // COLOR EXTRACTION WITH CONFIDENCE
    // ==========================================================================

    const colorMap = {
        high: new Map(),
        medium: new Map(),
        low: new Map()
    };

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        const colorProperties = [
            { prop: 'backgroundColor', name: 'background' },
            { prop: 'color', name: 'text' },
            { prop: 'borderColor', name: 'border' },
            { prop: 'fill', name: 'fill' },
            { prop: 'stroke', name: 'stroke' }
        ];

        colorProperties.forEach(({ prop, name }) => {
            const value = s[prop];
            if (value &&
                value !== 'rgba(0, 0, 0, 0)' &&
                value !== 'transparent' &&
                value !== 'none' &&
                value !== 'rgb(0, 0, 0)' && // Skip pure black (often default)
                value !== 'rgb(255, 255, 255)') { // Skip pure white (often default)

                const hex = rgbToHex(value);
                if (!hex) return;

                const confidence = getColorConfidence(el, prop);
                const key = hex;

                if (!colorMap[confidence].has(key)) {
                    colorMap[confidence].set(key, {
                        hex: hex,
                        property: name,
                        context: getSelector(el),
                        count: 1
                    });
                } else {
                    colorMap[confidence].get(key).count++;
                }
            }
        });
    });

    // Convert maps to arrays and sort by count
    ['high', 'medium', 'low'].forEach(level => {
        result.colors[level] = Array.from(colorMap[level].values())
            .sort((a, b) => b.count - a.count)
            .slice(0, level === 'low' ? 5 : 10); // Limit low confidence
    });

    // ==========================================================================
    // TYPOGRAPHY EXTRACTION
    // ==========================================================================

    const fontFamilyCount = new Map();
    const fontSizeSet = new Set();
    const fontWeightSet = new Set();
    const lineHeightSet = new Set();
    const letterSpacingSet = new Set();

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        // Font family
        const family = s.fontFamily.split(',')[0].replace(/['"]/g, '').trim();
        if (family && family !== 'inherit') {
            fontFamilyCount.set(family, (fontFamilyCount.get(family) || 0) + 1);
        }

        // Font size
        if (s.fontSize && s.fontSize !== '0px') {
            fontSizeSet.add(s.fontSize);
        }

        // Font weight
        if (s.fontWeight) {
            fontWeightSet.add(s.fontWeight);
        }

        // Line height
        if (s.lineHeight && s.lineHeight !== 'normal') {
            lineHeightSet.add(s.lineHeight);
        }

        // Letter spacing
        if (s.letterSpacing && s.letterSpacing !== 'normal' && s.letterSpacing !== '0px') {
            letterSpacingSet.add(s.letterSpacing);
        }
    });

    // Determine primary font (most common)
    const sortedFonts = [...fontFamilyCount.entries()].sort((a, b) => b[1] - a[1]);
    if (sortedFonts.length > 0) {
        result.typography.primary = sortedFonts[0][0];
    }

    // Check if headings use different font
    const headings = document.querySelectorAll('h1, h2, h3');
    if (headings.length > 0) {
        const headingFont = getComputedStyle(headings[0]).fontFamily.split(',')[0].replace(/['"]/g, '').trim();
        if (headingFont !== result.typography.primary) {
            result.typography.heading = headingFont;
        }
    }

    result.typography.fontFamilies = sortedFonts.map(([f]) => f).slice(0, 5);
    result.typography.fontSizes = [...fontSizeSet].map(s => parseFloat(s)).sort((a, b) => a - b).map(s => s + 'px');
    result.typography.fontWeights = [...fontWeightSet].sort((a, b) => parseInt(a) - parseInt(b));
    result.typography.lineHeights = [...lineHeightSet].slice(0, 10);
    result.typography.letterSpacings = [...letterSpacingSet].slice(0, 5);

    // ==========================================================================
    // FONT MANIFEST (URLs and weights)
    // ==========================================================================

    // From @font-face rules
    Array.from(document.styleSheets).forEach(sheet => {
        try {
            Array.from(sheet.cssRules || []).forEach(rule => {
                if (rule instanceof CSSFontFaceRule) {
                    const family = rule.style.getPropertyValue('font-family').replace(/['"]/g, '').trim();
                    const weight = rule.style.getPropertyValue('font-weight') || '400';
                    const src = rule.style.getPropertyValue('src');

                    if (family) {
                        if (!result.fontManifest[family]) {
                            result.fontManifest[family] = {
                                weights: [],
                                urls: {}
                            };
                        }

                        if (!result.fontManifest[family].weights.includes(weight)) {
                            result.fontManifest[family].weights.push(weight);
                        }

                        // Extract URL from src
                        const urlMatch = src.match(/url\(["']?([^"')]+)["']?\)/);
                        if (urlMatch) {
                            result.fontManifest[family].urls[weight] = urlMatch[1];
                        }
                    }
                }
            });
        } catch (e) {
            // CORS blocked
        }
    });

    // From network requests (performance API)
    try {
        const fontRequests = performance.getEntriesByType('resource')
            .filter(r => r.name.includes('woff') || r.name.includes('font') ||
                        r.name.includes('ttf') || r.name.includes('otf'))
            .map(r => r.name);

        result.fontUrls = fontRequests;
    } catch (e) {
        result.fontUrls = [];
    }

    // From document.fonts API
    try {
        const loadedFonts = [];
        document.fonts.forEach(font => {
            loadedFonts.push({
                family: font.family.replace(/['"]/g, ''),
                weight: font.weight,
                style: font.style,
                status: font.status
            });
        });
        result.loadedFonts = loadedFonts;
    } catch (e) {
        result.loadedFonts = [];
    }

    // ==========================================================================
    // SPACING EXTRACTION
    // ==========================================================================

    const spacingSet = new Set();
    const sectionGaps = [];

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        ['margin', 'padding', 'gap', 'rowGap', 'columnGap'].forEach(prop => {
            const value = s[prop];
            if (value && value !== '0px' && value !== 'normal') {
                // Parse individual values
                value.split(' ').forEach(v => {
                    const px = parseFloat(v);
                    if (px > 0 && px <= 200) {
                        spacingSet.add(px);
                    }
                });
            }
        });
    });

    // Extract section gaps specifically
    document.querySelectorAll('section, [class*="section"]').forEach(el => {
        const s = getComputedStyle(el);
        const marginTop = parseFloat(s.marginTop);
        const paddingTop = parseFloat(s.paddingTop);
        const marginBottom = parseFloat(s.marginBottom);
        const paddingBottom = parseFloat(s.paddingBottom);

        if (marginTop > 30) sectionGaps.push(marginTop);
        if (paddingTop > 30) sectionGaps.push(paddingTop);
        if (marginBottom > 30) sectionGaps.push(marginBottom);
        if (paddingBottom > 30) sectionGaps.push(paddingBottom);
    });

    // Create spacing scale (common values)
    result.spacing.scale = [...spacingSet]
        .sort((a, b) => a - b)
        .filter(v => v > 0)
        .map(v => Math.round(v) + 'px');

    result.spacing.sectionGaps = [...new Set(sectionGaps)]
        .sort((a, b) => a - b)
        .map(v => Math.round(v) + 'px');

    // Page padding
    const body = document.body;
    const main = document.querySelector('main, [class*="container"], [class*="wrapper"]');
    const containerEl = main || body;
    const containerStyle = getComputedStyle(containerEl);

    result.spacing.pagePadding = {
        left: containerStyle.paddingLeft,
        right: containerStyle.paddingRight,
        source: getSelector(containerEl)
    };

    // ==========================================================================
    // SHADOWS EXTRACTION
    // ==========================================================================

    const shadowSet = new Set();

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);
        if (s.boxShadow && s.boxShadow !== 'none') {
            shadowSet.add(s.boxShadow);
        }
    });

    result.shadows = [...shadowSet].slice(0, 10);

    // ==========================================================================
    // BORDER RADIUS EXTRACTION
    // ==========================================================================

    const radiusSet = new Set();

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);
        if (s.borderRadius && s.borderRadius !== '0px') {
            radiusSet.add(s.borderRadius);
        }
    });

    result.borderRadius = [...radiusSet]
        .map(r => parseFloat(r))
        .filter(r => r > 0)
        .sort((a, b) => a - b)
        .map(r => r + 'px');

    // ==========================================================================
    // GRADIENTS EXTRACTION
    // ==========================================================================

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);
        const bg = s.backgroundImage;
        if (bg && bg !== 'none' && bg.includes('gradient')) {
            if (!result.gradients.includes(bg)) {
                result.gradients.push(bg);
            }
        }
    });

    result.gradients = result.gradients.slice(0, 10);

    // ==========================================================================
    // CSS CUSTOM PROPERTIES
    // ==========================================================================

    const root = document.documentElement;
    const rootStyle = getComputedStyle(root);

    // Check inline styles for CSS variables
    for (let i = 0; i < root.style.length; i++) {
        const prop = root.style[i];
        if (prop.startsWith('--')) {
            result.customProperties[prop] = rootStyle.getPropertyValue(prop);
        }
    }

    // Try to get variables from stylesheets
    Array.from(document.styleSheets).forEach(sheet => {
        try {
            Array.from(sheet.cssRules || []).forEach(rule => {
                if (rule instanceof CSSStyleRule && rule.selectorText === ':root') {
                    for (let i = 0; i < rule.style.length; i++) {
                        const prop = rule.style[i];
                        if (prop.startsWith('--')) {
                            result.customProperties[prop] = rule.style.getPropertyValue(prop);
                        }
                    }
                }
            });
        } catch (e) {
            // CORS blocked
        }
    });

    // ==========================================================================
    // TIMING CONSTANTS
    // ==========================================================================

    const easingSet = new Set();
    const durationSet = new Set();

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        if (s.transitionTimingFunction &&
            s.transitionTimingFunction !== 'ease' &&
            s.transitionTimingFunction !== 'ease 0s') {
            easingSet.add(s.transitionTimingFunction);
        }

        if (s.transitionDuration && s.transitionDuration !== '0s') {
            durationSet.add(s.transitionDuration);
        }

        if (s.animationDuration && s.animationDuration !== '0s') {
            durationSet.add(s.animationDuration);
        }
    });

    result.timingConstants.easings = [...easingSet];
    result.timingConstants.durations = [...durationSet].sort((a, b) => parseFloat(a) - parseFloat(b));

    // Identify premium easing
    const cubicBeziers = result.timingConstants.easings.filter(e => e.includes('cubic-bezier'));
    if (cubicBeziers.length > 0) {
        result.timingConstants.premiumEasing = cubicBeziers[0];
    }

    // ==========================================================================
    // SUMMARY
    // ==========================================================================

    result.summary = {
        highConfidenceColors: result.colors.high.length,
        mediumConfidenceColors: result.colors.medium.length,
        primaryFont: result.typography.primary,
        headingFont: result.typography.heading,
        fontCount: result.typography.fontFamilies.length,
        fontWeightCount: result.typography.fontWeights.length,
        spacingScaleSize: result.spacing.scale.length,
        hasCssVariables: Object.keys(result.customProperties).length > 0,
        cssVariableCount: Object.keys(result.customProperties).length,
        premiumEasing: result.timingConstants.premiumEasing,
        topColors: result.colors.high.slice(0, 5).map(c => c.hex)
    };

    return result;
})();
