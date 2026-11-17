/**
 * SVG & Icon Extraction Script (v4.0)
 *
 * Extracts inline SVGs, detects icon libraries, and captures icon usage patterns.
 * This ensures Gemini can reproduce exact icons in the clone.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with SVG and icon data
 */
(function() {
    const result = {
        inlineSvgs: [],           // All inline SVG icons
        iconClasses: [],          // Icon class patterns detected
        spriteReferences: [],     // <use> references to sprite sheets
        externalSvgs: [],         // External SVG file references
        iconLibrary: {
            detected: null,
            heroicons: false,
            lucide: false,
            fontAwesome: false,
            phosphor: false,
            feather: false,
            materialIcons: false,
            bootstrap: false,
            tabler: false
        },
        decorativeSvgs: [],       // Large SVGs (backgrounds, illustrations)
        logoSvg: null,            // Logo SVG if found
        statistics: {
            totalSvgs: 0,
            iconSvgs: 0,
            decorativeSvgs: 0,
            uniqueIcons: 0
        }
    };

    // Helper to get a meaningful selector
    function getSelector(el) {
        if (el.id) return '#' + el.id;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(' ').filter(c => c).slice(0, 2).join('.');
            if (classes) return el.tagName.toLowerCase() + '.' + classes;
        }
        // Check parent for context
        const parent = el.parentElement;
        if (parent) {
            if (parent.className && typeof parent.className === 'string') {
                const parentClasses = parent.className.trim().split(' ').filter(c => c)[0];
                if (parentClasses) {
                    return parent.tagName.toLowerCase() + '.' + parentClasses + ' > svg';
                }
            }
        }
        return 'svg';
    }

    // Helper to check if SVG is likely an icon (small size)
    function isIconSize(svg) {
        const width = svg.getAttribute('width');
        const height = svg.getAttribute('height');
        const viewBox = svg.getAttribute('viewBox');

        // Check explicit dimensions
        if (width && height) {
            const w = parseInt(width);
            const h = parseInt(height);
            if (w > 0 && w <= 64 && h > 0 && h <= 64) return true;
        }

        // Check computed dimensions
        const rect = svg.getBoundingClientRect();
        if (rect.width > 0 && rect.width <= 64 && rect.height <= 64) return true;

        // Check viewBox for small icons
        if (viewBox) {
            const parts = viewBox.split(' ').map(parseFloat);
            if (parts.length === 4) {
                const [, , vbWidth, vbHeight] = parts;
                if (vbWidth <= 48 && vbHeight <= 48) return true;
            }
        }

        return false;
    }

    // Helper to normalize SVG for comparison
    function normalizeSvg(svgHtml) {
        return svgHtml
            .replace(/\s+/g, ' ')
            .replace(/<!--.*?-->/g, '')
            .replace(/\s*=\s*/g, '=')
            .trim();
    }

    // Helper to extract SVG paths for fingerprinting
    function getSvgFingerprint(svg) {
        const paths = svg.querySelectorAll('path, circle, rect, line, polyline, polygon');
        return Array.from(paths).map(p => {
            if (p.tagName === 'path') return p.getAttribute('d')?.slice(0, 50);
            return p.tagName;
        }).join('|');
    }

    // ==========================================================================
    // INLINE SVG EXTRACTION
    // ==========================================================================

    const allSvgs = document.querySelectorAll('svg');
    const seenFingerprints = new Set();

    allSvgs.forEach((svg, index) => {
        result.statistics.totalSvgs++;

        const isIcon = isIconSize(svg);
        const width = svg.getAttribute('width');
        const height = svg.getAttribute('height');
        const viewBox = svg.getAttribute('viewBox');
        const className = svg.getAttribute('class') || '';
        const fill = getComputedStyle(svg).fill;
        const stroke = getComputedStyle(svg).stroke;

        // Get SVG content
        const svgHtml = svg.outerHTML;
        const svgSize = svgHtml.length;

        // Create fingerprint to detect duplicates
        const fingerprint = getSvgFingerprint(svg);

        // Check if this is a logo
        const isLogo = className.toLowerCase().includes('logo') ||
                       svg.closest('[class*="logo"]') !== null ||
                       svg.closest('a[href="/"], a[href="./"]') !== null;

        if (isIcon) {
            result.statistics.iconSvgs++;

            // Check for duplicates
            const isUnique = !seenFingerprints.has(fingerprint);
            if (fingerprint) seenFingerprints.add(fingerprint);

            if (isUnique) {
                result.statistics.uniqueIcons++;
            }

            const iconData = {
                index: index,
                selector: getSelector(svg),
                viewBox: viewBox,
                width: width,
                height: height,
                className: className,
                fill: fill !== 'rgb(0, 0, 0)' ? fill : null,
                stroke: stroke !== 'none' ? stroke : null,
                pathCount: svg.querySelectorAll('path').length,
                isUnique: isUnique,
                context: svg.closest('button, a, [class*="icon"]')?.className || null
            };

            // Store SVG HTML only if it's not too large (< 3KB)
            if (svgSize < 20000) {
                iconData.html = svgHtml;
            } else {
                iconData.html = '[too large - ' + svgSize + ' bytes]';
            }

            result.inlineSvgs.push(iconData);

            // Store logo separately
            if (isLogo && !result.logoSvg) {
                result.logoSvg = {
                    html: svgHtml,
                    viewBox: viewBox,
                    width: width,
                    height: height
                };
            }
        } else {
            // Decorative/large SVG
            result.statistics.decorativeSvgs++;

            result.decorativeSvgs.push({
                index: index,
                selector: getSelector(svg),
                viewBox: viewBox,
                width: width,
                height: height,
                className: className,
                sizeBytes: svgSize,
                pathCount: svg.querySelectorAll('path').length,
                isBackground: svg.closest('[class*="background"], [class*="hero"], [class*="bg-"]') !== null,
                html: svg.outerHTML.slice(0, 20000),
                context: svg.closest('section')?.id || svg.closest('[class]')?.className?.split(' ')[0] || 'unknown',
                role: 'decorative-shape'
            });
        }
    });

    // ==========================================================================
    // ICON CLASS PATTERN DETECTION
    // ==========================================================================

    const iconPatterns = [
        { pattern: /heroicon/, library: 'heroicons' },
        { pattern: /lucide/, library: 'lucide' },
        { pattern: /\bfa\b|\bfas\b|\bfar\b|\bfab\b|fa-/, library: 'fontAwesome' },
        { pattern: /\bph-|\bph\b/, library: 'phosphor' },
        { pattern: /feather/, library: 'feather' },
        { pattern: /material-icon|material-symbols/, library: 'materialIcons' },
        { pattern: /\bbi\b|bi-/, library: 'bootstrap' },
        { pattern: /tabler/, library: 'tabler' }
    ];

    // Check all elements for icon classes
    document.querySelectorAll('[class*="icon"], [class*="Icon"], svg').forEach(el => {
        const className = el.className;
        if (!className || typeof className !== 'string') return;

        iconPatterns.forEach(({ pattern, library }) => {
            if (pattern.test(className)) {
                result.iconLibrary[library] = true;
                if (!result.iconLibrary.detected) {
                    result.iconLibrary.detected = library;
                }
            }
        });

        // Collect icon class patterns
        const iconClasses = className.split(' ').filter(c =>
            c.includes('icon') || c.includes('Icon') ||
            c.startsWith('fa-') || c.startsWith('ph-') ||
            c.startsWith('bi-') || c.includes('lucide')
        );

        iconClasses.forEach(cls => {
            if (!result.iconClasses.includes(cls)) {
                result.iconClasses.push(cls);
            }
        });
    });

    // ==========================================================================
    // SPRITE REFERENCES
    // ==========================================================================

    document.querySelectorAll('use').forEach(use => {
        const href = use.getAttribute('href') || use.getAttribute('xlink:href');
        if (href) {
            result.spriteReferences.push({
                href: href,
                parent: getSelector(use.closest('svg')),
                isExternal: href.startsWith('/') || href.startsWith('http')
            });
        }
    });

    // ==========================================================================
    // EXTERNAL SVG FILES
    // ==========================================================================

    // Check for SVG images
    document.querySelectorAll('img[src$=".svg"], object[data$=".svg"], embed[src$=".svg"]').forEach(el => {
        const src = el.src || el.getAttribute('data') || el.getAttribute('src');
        if (src) {
            result.externalSvgs.push({
                type: el.tagName.toLowerCase(),
                src: src,
                alt: el.alt || null,
                width: el.width || el.getAttribute('width'),
                height: el.height || el.getAttribute('height')
            });
        }
    });

    // Check for SVG in CSS backgrounds
    const allElements = document.querySelectorAll('*');
    allElements.forEach(el => {
        const style = getComputedStyle(el);
        const bgImage = style.backgroundImage;
        if (bgImage && bgImage.includes('.svg')) {
            const match = bgImage.match(/url\(["']?([^"')]+\.svg)["']?\)/);
            if (match) {
                result.externalSvgs.push({
                    type: 'background-image',
                    src: match[1],
                    element: getSelector(el)
                });
            }
        }
    });

    // ==========================================================================
    // SUMMARY
    // ==========================================================================

    result.summary = {
        totalSvgs: result.statistics.totalSvgs,
        iconSvgs: result.statistics.iconSvgs,
        decorativeSvgs: result.statistics.decorativeSvgs,
        uniqueIcons: result.statistics.uniqueIcons,
        iconLibrary: result.iconLibrary.detected || 'inline-svg',
        hasLogo: !!result.logoSvg,
        hasSpriteSheet: result.spriteReferences.length > 0,
        externalSvgCount: result.externalSvgs.length,
        iconClassPatterns: result.iconClasses.slice(0, 10)
    };

    // Limit output size
    if (result.inlineSvgs.length > 30) {
        result.inlineSvgs = result.inlineSvgs.slice(0, 30);
        result.summary.note = 'Limited to first 30 icons. Total: ' + result.statistics.iconSvgs;
    }

    if (result.decorativeSvgs.length > 25) {
        result.decorativeSvgs = result.decorativeSvgs.slice(0, 25);
    }

    return result;
})();
