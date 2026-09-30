/**
 * Hover State Matrix Capture Script (v4.0)
 *
 * Automatically captures ALL hover state changes on a webpage.
 * Enhanced for v4 with better transition detection and categorization.
 *
 * Purpose: Static screenshots can't show hover effects.
 * This script captures the EXACT CSS differences when hovering,
 * giving Gemini precise values to implement.
 *
 * Usage: Run via Playwright or mcp__claude-in-chrome__javascript_tool
 *
 * What it captures:
 * - Background color changes
 * - Text color changes
 * - Transform effects (scale, translate, rotate)
 * - Box shadow additions/changes
 * - Border changes
 * - Opacity changes
 * - Transition timing functions
 * - Underline animations (text-decoration)
 *
 * Output: JSON object with hover state matrix
 */

(function() {
    /**
     * Get a unique CSS selector for an element
     * This helps Gemini know exactly which element to target
     */
    function getSelector(el) {
        if (el.id) return `#${el.id}`;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(/\s+/).filter(c => c);
            if (classes.length > 0) {
                return `${el.tagName.toLowerCase()}.${classes[0]}`;
            }
        }
        return el.tagName.toLowerCase();
    }

    /**
     * Get full class list for an element (for more specific selectors)
     */
    function getFullSelector(el) {
        if (el.id) return `#${el.id}`;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(/\s+/).filter(c => c).slice(0, 3);
            if (classes.length > 0) {
                return `${el.tagName.toLowerCase()}.${classes.join('.')}`;
            }
        }
        return el.tagName.toLowerCase();
    }

    /**
     * Properties we care about for hover states
     * These are the most commonly changed properties on hover
     */
    const HOVER_PROPERTIES = [
        'backgroundColor',
        'color',
        'opacity',
        'transform',
        'scale',
        'boxShadow',
        'borderColor',
        'borderWidth',
        'borderStyle',
        'textDecoration',
        'textDecorationColor',
        'textDecorationThickness',
        'textUnderlineOffset',
        'outline',
        'outlineColor',
        'outlineWidth',
        'filter',
        'cursor',
        'fill',           // For SVGs
        'stroke',         // For SVGs
        'strokeWidth',    // For SVGs
        // Transition properties
        'transitionDuration',
        'transitionTimingFunction',
        'transitionProperty'
    ];

    /**
     * Categorize hover effects by type
     */
    function categorizeHoverEffect(changes) {
        const categories = [];

        if (changes.transform || changes.scale) {
            categories.push('scale');
        }
        if (changes.backgroundColor) {
            categories.push('background');
        }
        if (changes.color) {
            categories.push('color');
        }
        if (changes.boxShadow) {
            categories.push('shadow');
        }
        if (changes.textDecoration || changes.textDecorationColor) {
            categories.push('underline');
        }
        if (changes.opacity) {
            categories.push('fade');
        }
        if (changes.borderColor || changes.borderWidth) {
            categories.push('border');
        }
        if (changes.fill || changes.stroke) {
            categories.push('svg');
        }

        return categories.length > 0 ? categories : ['other'];
    }

    /**
     * Compare two computed style objects and return differences
     */
    function computeStyleDiff(before, after) {
        const changes = {};

        HOVER_PROPERTIES.forEach(prop => {
            const beforeVal = before[prop];
            const afterVal = after[prop];

            // Only record if there's an actual change
            if (beforeVal !== afterVal) {
                changes[prop] = {
                    from: beforeVal,
                    to: afterVal
                };
            }
        });

        return changes;
    }

    /**
     * Check if an element is visible and interactive
     */
    function isInteractive(el) {
        const rect = el.getBoundingClientRect();
        const style = getComputedStyle(el);

        // Skip invisible elements
        if (rect.width === 0 || rect.height === 0) return false;
        if (style.display === 'none') return false;
        if (style.visibility === 'hidden') return false;
        if (parseFloat(style.opacity) === 0) return false;

        // Skip elements way off-screen
        if (rect.bottom < 0 || rect.top > window.innerHeight * 3) return false;

        return true;
    }

    /**
     * Get the transition info from an element
     */
    function getTransitionInfo(el) {
        const style = getComputedStyle(el);
        return {
            duration: style.transitionDuration,
            timing: style.transitionTimingFunction,
            property: style.transitionProperty,
            delay: style.transitionDelay
        };
    }

    /**
     * Determine confidence level based on element type and context
     */
    function getConfidence(el, changes) {
        const tag = el.tagName.toLowerCase();
        const className = (el.className && typeof el.className === 'string') ?
                          el.className.toLowerCase() : '';

        // HIGH: Primary CTAs, buttons, navigation
        if (className.includes('cta') ||
            className.includes('primary') ||
            className.includes('btn-primary') ||
            (tag === 'button' && className.includes('primary'))) {
            return 'high';
        }

        // HIGH: Main navigation links
        if (className.includes('nav') && (tag === 'a' || tag === 'button')) {
            return 'high';
        }

        // MEDIUM: Cards, secondary buttons, links
        if (tag === 'button' || tag === 'a' ||
            className.includes('card') ||
            className.includes('link')) {
            return 'medium';
        }

        // LOW: Generic elements with hover effects
        return 'low';
    }

    // Find all potentially interactive elements
    const interactiveSelectors = [
        'a',                     // Links
        'button',                // Buttons
        '[role="button"]',       // ARIA buttons
        'input[type="submit"]',  // Submit buttons
        '.card',                 // Common card class
        '.btn',                  // Common button class
        '[data-hover]',          // Explicitly marked hover elements
        '.product-card',         // Product cards
        '.nav-link',             // Navigation links
        '.social-icon',          // Social icons
        '[class*="hover"]',      // Any class containing "hover"
        'li > a',                // Menu links
        '.menu-item',            // Menu items
        '[class*="card"]',       // Any card-like element
        '[class*="link"]',       // Any link-like element
        '[class*="btn"]',        // Any button-like element
        '[class*="icon"]',       // Icon elements
        'svg',                   // SVG icons (may have hover)
        'figure',                // Images with hover effects
        '[class*="image"]',      // Image containers
        '[class*="item"]',       // List items
    ];

    const elements = document.querySelectorAll(interactiveSelectors.join(', '));
    const hoverMatrix = [];
    const seen = new Set(); // Avoid duplicates

    elements.forEach(el => {
        // Skip if not visible/interactive
        if (!isInteractive(el)) return;

        // Skip duplicates
        const selector = getSelector(el);
        if (seen.has(selector)) return;
        seen.add(selector);

        // Get current (non-hover) styles
        const beforeStyles = {};
        const computedBefore = getComputedStyle(el);
        HOVER_PROPERTIES.forEach(prop => {
            beforeStyles[prop] = computedBefore[prop];
        });

        // Get transition info (even before hover)
        const transitionInfo = getTransitionInfo(el);

        // Check if element has :hover styles defined in CSS
        let hasHoverRule = false;
        let hoverStyles = {};

        try {
            Array.from(document.styleSheets).forEach(sheet => {
                try {
                    Array.from(sheet.cssRules).forEach(rule => {
                        if (rule.selectorText && rule.selectorText.includes(':hover')) {
                            // Check if this rule matches our element
                            const baseSelector = rule.selectorText.replace(':hover', '').trim();
                            try {
                                if (el.matches(baseSelector)) {
                                    hasHoverRule = true;
                                    // Extract the hover styles from the rule
                                    for (let i = 0; i < rule.style.length; i++) {
                                        const prop = rule.style[i];
                                        const camelCase = prop.replace(/-([a-z])/g, (g) => g[1].toUpperCase());
                                        hoverStyles[camelCase] = rule.style.getPropertyValue(prop);
                                    }
                                }
                            } catch (e) {
                                // matches() can throw for complex selectors
                            }
                        }
                    });
                } catch (e) {
                    // CORS blocked stylesheet
                }
            });
        } catch (e) {
            // Error accessing stylesheets
        }

        // If we found hover styles, record them
        if (hasHoverRule && Object.keys(hoverStyles).length > 0) {
            const changes = {};

            Object.keys(hoverStyles).forEach(prop => {
                if (HOVER_PROPERTIES.includes(prop) && beforeStyles[prop] !== hoverStyles[prop]) {
                    changes[prop] = {
                        from: beforeStyles[prop],
                        to: hoverStyles[prop]
                    };
                }
            });

            if (Object.keys(changes).length > 0) {
                const entry = {
                    selector: selector,
                    fullSelector: getFullSelector(el),
                    element: el.tagName.toLowerCase(),
                    classes: el.className || '',
                    changes: changes,
                    categories: categorizeHoverEffect(changes),
                    confidence: getConfidence(el, changes),
                    transition: transitionInfo.duration !== '0s' ? {
                        duration: transitionInfo.duration,
                        timing: transitionInfo.timing,
                        property: transitionInfo.property,
                        delay: transitionInfo.delay !== '0s' ? transitionInfo.delay : null
                    } : null
                };

                hoverMatrix.push(entry);
            }
        }
    });

    // Also extract any :hover rules we might have missed
    const allHoverRules = [];
    try {
        Array.from(document.styleSheets).forEach(sheet => {
            try {
                Array.from(sheet.cssRules).forEach(rule => {
                    if (rule.selectorText && rule.selectorText.includes(':hover')) {
                        allHoverRules.push({
                            selector: rule.selectorText,
                            styles: rule.cssText
                        });
                    }
                });
            } catch (e) {
                // CORS blocked
            }
        });
    } catch (e) {
        // Error
    }

    // Categorize by confidence
    const highConfidence = hoverMatrix.filter(h => h.confidence === 'high');
    const mediumConfidence = hoverMatrix.filter(h => h.confidence === 'medium');
    const lowConfidence = hoverMatrix.filter(h => h.confidence === 'low');

    // Find most common transition timing
    const timings = hoverMatrix
        .filter(h => h.transition?.timing)
        .map(h => h.transition.timing);
    const timingCounts = {};
    timings.forEach(t => {
        timingCounts[t] = (timingCounts[t] || 0) + 1;
    });
    const mostCommonTiming = Object.keys(timingCounts)
        .sort((a, b) => timingCounts[b] - timingCounts[a])[0];

    // Find most common duration
    const durations = hoverMatrix
        .filter(h => h.transition?.duration)
        .map(h => h.transition.duration);
    const durationCounts = {};
    durations.forEach(d => {
        durationCounts[d] = (durationCounts[d] || 0) + 1;
    });
    const mostCommonDuration = Object.keys(durationCounts)
        .sort((a, b) => durationCounts[b] - durationCounts[a])[0];

    return {
        hoverStates: hoverMatrix,
        byConfidence: {
            high: highConfidence,
            medium: mediumConfidence,
            low: lowConfidence
        },
        totalInteractiveElements: elements.length,
        totalCaptured: hoverMatrix.length,
        allHoverRules: allHoverRules.slice(0, 50), // Limit for output size
        // Summary for Gemini
        summary: {
            hasScaleEffects: hoverMatrix.some(h =>
                h.changes.transform?.to?.includes('scale')
            ),
            hasColorChanges: hoverMatrix.some(h =>
                h.changes.backgroundColor || h.changes.color
            ),
            hasShadowEffects: hoverMatrix.some(h => h.changes.boxShadow),
            hasUnderlineEffects: hoverMatrix.some(h => h.changes.textDecoration),
            hasSvgEffects: hoverMatrix.some(h => h.changes.fill || h.changes.stroke),
            commonTimingFunction: mostCommonTiming || 'ease',
            commonDuration: mostCommonDuration || '0.3s',
            highConfidenceCount: highConfidence.length,
            mediumConfidenceCount: mediumConfidence.length,
            lowConfidenceCount: lowConfidence.length
        }
    };
})();
