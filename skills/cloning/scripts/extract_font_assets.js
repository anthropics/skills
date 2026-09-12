/**
 * Font Assets Extraction Script (v4.0)
 *
 * Parses @font-face rules from CSSOM to extract font family names, source URLs
 * (woff2/woff/ttf), weight ranges, font-display, and format. Also captures
 * text rendering settings (font-variation-settings, text-rendering,
 * font-feature-settings) from body and key elements.
 *
 * Output matches the Gemini prompt template "Font Manifest" format for seamless
 * integration into the clone generation pipeline.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with font manifest and text rendering data
 */
(function() {
    const result = {
        fontFaces: [],
        textRendering: {
            body: null,
            headings: []
        },
        usedFonts: [],
        metadata: {
            extractedAt: new Date().toISOString(),
            sheetsAnalyzed: 0,
            corsBlockedSheets: 0
        }
    };

    // Helper: parse src descriptor from @font-face
    function parseFontSrc(srcValue) {
        if (!srcValue) return [];
        const sources = [];
        // Match url("...") format("...")  patterns
        const urlRegex = /url\(["']?([^"')]+)["']?\)\s*(?:format\(["']?([^"')]+)["']?\))?/g;
        let match;
        while ((match = urlRegex.exec(srcValue)) !== null) {
            const url = match[1];
            const format = match[2] || null;
            // Determine format from URL extension if not specified
            let inferredFormat = format;
            if (!inferredFormat) {
                if (url.endsWith('.woff2')) inferredFormat = 'woff2';
                else if (url.endsWith('.woff')) inferredFormat = 'woff';
                else if (url.endsWith('.ttf')) inferredFormat = 'truetype';
                else if (url.endsWith('.otf')) inferredFormat = 'opentype';
                else if (url.endsWith('.eot')) inferredFormat = 'embedded-opentype';
            }
            sources.push({
                url: url,
                format: inferredFormat
            });
        }
        return sources;
    }

    // Helper: parse font-weight range (e.g., "100 900" for variable fonts)
    function parseFontWeight(weightValue) {
        if (!weightValue) return { min: 400, max: 400 };
        const parts = weightValue.toString().trim().split(/\s+/);
        if (parts.length === 2) {
            return { min: parseInt(parts[0]), max: parseInt(parts[1]) };
        }
        const single = parseInt(parts[0]) || 400;
        return { min: single, max: single };
    }

    // ==========================================================================
    // EXTRACT @font-face RULES FROM CSSOM
    // ==========================================================================
    const sheets = document.styleSheets;
    for (let i = 0; i < sheets.length; i++) {
        result.metadata.sheetsAnalyzed++;
        let rules;
        try {
            rules = sheets[i].cssRules || sheets[i].rules;
        } catch (e) {
            // CORS-blocked stylesheet
            result.metadata.corsBlockedSheets++;
            continue;
        }
        if (!rules) continue;

        for (let j = 0; j < rules.length; j++) {
            const rule = rules[j];
            if (rule.type === CSSRule.FONT_FACE_RULE) {
                const style = rule.style;
                const family = (style.getPropertyValue('font-family') || '').replace(/['"]/g, '').trim();
                const srcValue = style.getPropertyValue('src');
                const weight = parseFontWeight(style.getPropertyValue('font-weight'));
                const fontStyle = style.getPropertyValue('font-style') || 'normal';
                const fontDisplay = style.getPropertyValue('font-display') || null;
                const unicodeRange = style.getPropertyValue('unicode-range') || null;

                const sources = parseFontSrc(srcValue);

                if (family && sources.length > 0) {
                    result.fontFaces.push({
                        family: family,
                        sources: sources,
                        weight: weight,
                        style: fontStyle,
                        display: fontDisplay,
                        unicodeRange: unicodeRange,
                        isVariable: weight.min !== weight.max
                    });
                }
            }
        }
    }

    // ==========================================================================
    // GROUP BY FONT FAMILY (for Gemini template format)
    // ==========================================================================
    const fontMap = {};
    result.fontFaces.forEach(face => {
        if (!fontMap[face.family]) {
            fontMap[face.family] = {
                family: face.family,
                isVariable: false,
                weights: [],
                sources: []
            };
        }
        const entry = fontMap[face.family];
        if (face.isVariable) entry.isVariable = true;

        // Collect unique weights
        const weightKey = face.weight.min + '-' + face.weight.max;
        if (!entry.weights.some(w => w.min === face.weight.min && w.max === face.weight.max)) {
            entry.weights.push(face.weight);
        }

        // Collect all sources with their weight association
        face.sources.forEach(src => {
            entry.sources.push({
                url: src.url,
                format: src.format,
                weight: face.weight,
                style: face.style,
                display: face.display
            });
        });
    });

    // Convert to array sorted by family name
    result.fontManifest = Object.values(fontMap).sort((a, b) => a.family.localeCompare(b.family));

    // ==========================================================================
    // TEXT RENDERING SETTINGS
    // ==========================================================================
    const body = document.body;
    if (body) {
        const bodyCS = getComputedStyle(body);
        result.textRendering.body = {
            fontFamily: bodyCS.fontFamily,
            fontSize: bodyCS.fontSize,
            fontWeight: bodyCS.fontWeight,
            lineHeight: bodyCS.lineHeight,
            letterSpacing: bodyCS.letterSpacing !== 'normal' ? bodyCS.letterSpacing : null,
            textRendering: bodyCS.textRendering,
            fontFeatureSettings: bodyCS.fontFeatureSettings !== 'normal' ? bodyCS.fontFeatureSettings : null,
            fontKerning: bodyCS.fontKerning,
            fontVariationSettings: bodyCS.fontVariationSettings !== 'normal' ? bodyCS.fontVariationSettings : null,
            webkitFontSmoothing: bodyCS.webkitFontSmoothing || null,
            color: bodyCS.color
        };
    }

    // Heading text rendering (h1-h4)
    ['h1', 'h2', 'h3', 'h4'].forEach(tag => {
        const el = document.querySelector(tag);
        if (el) {
            const cs = getComputedStyle(el);
            result.textRendering.headings.push({
                tag: tag,
                fontFamily: cs.fontFamily,
                fontSize: cs.fontSize,
                fontWeight: cs.fontWeight,
                lineHeight: cs.lineHeight,
                letterSpacing: cs.letterSpacing !== 'normal' ? cs.letterSpacing : null,
                textRendering: cs.textRendering,
                fontFeatureSettings: cs.fontFeatureSettings !== 'normal' ? cs.fontFeatureSettings : null,
                fontVariationSettings: cs.fontVariationSettings !== 'normal' ? cs.fontVariationSettings : null,
                textTransform: cs.textTransform !== 'none' ? cs.textTransform : null
            });
        }
    });

    // ==========================================================================
    // DETECT ACTUALLY USED FONTS
    // ==========================================================================
    const usedFamilies = new Set();
    // Check body and key elements
    const elementsToCheck = [
        document.body,
        document.querySelector('h1'),
        document.querySelector('h2'),
        document.querySelector('h3'),
        document.querySelector('p'),
        document.querySelector('a'),
        document.querySelector('button'),
        document.querySelector('nav'),
        document.querySelector('footer')
    ].filter(Boolean);

    elementsToCheck.forEach(el => {
        const family = getComputedStyle(el).fontFamily;
        if (family) {
            // Parse out individual font names
            family.split(',').forEach(f => {
                const cleaned = f.trim().replace(/['"]/g, '');
                if (cleaned && !['serif', 'sans-serif', 'monospace', 'cursive', 'fantasy', 'system-ui', '-apple-system', 'BlinkMacSystemFont', 'Segoe UI', 'Roboto', 'Helvetica Neue', 'Arial', 'Helvetica'].includes(cleaned)) {
                    usedFamilies.add(cleaned);
                }
            });
        }
    });

    result.usedFonts = Array.from(usedFamilies);

    // ==========================================================================
    // FONT LOADING STATUS
    // ==========================================================================
    result.fontLoadingStatus = [];
    if (document.fonts) {
        try {
            document.fonts.forEach(font => {
                result.fontLoadingStatus.push({
                    family: font.family.replace(/['"]/g, ''),
                    weight: font.weight,
                    style: font.style,
                    status: font.status // 'unloaded', 'loading', 'loaded', 'error'
                });
            });
        } catch (e) {
            // Some browsers restrict font enumeration
        }
    }

    // ==========================================================================
    // SUMMARY
    // ==========================================================================
    result.summary = {
        totalFontFaces: result.fontFaces.length,
        uniqueFamilies: result.fontManifest.length,
        variableFonts: result.fontManifest.filter(f => f.isVariable).length,
        usedFontCount: result.usedFonts.length,
        usedFonts: result.usedFonts,
        hasWoff2: result.fontFaces.some(f => f.sources.some(s => s.format === 'woff2' || s.format === 'woff2-variations')),
        corsBlockedSheets: result.metadata.corsBlockedSheets,
        bodyFontFamily: result.textRendering.body ? result.textRendering.body.fontFamily : null,
        bodyTextRendering: result.textRendering.body ? result.textRendering.body.textRendering : null
    };

    return result;
})();
