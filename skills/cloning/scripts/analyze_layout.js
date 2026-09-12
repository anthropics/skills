/**
 * Layout Analysis Script (v4.0)
 *
 * Analyzes CSS Grid, Flexbox, Z-index stacking contexts, and responsive breakpoints.
 * This information ensures Gemini generates the correct layout structure.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with layout analysis
 */
(function() {
    const result = {
        layoutMethod: {
            grid: [],      // CSS Grid containers
            flexbox: [],   // Flexbox containers
            positioned: [], // Position: absolute/fixed/sticky elements
            floats: []     // Legacy float layouts
        },
        breakpoints: [],           // Media query breakpoints
        stackingContexts: [],      // Z-index layers
        containerQueries: [],      // Container queries (modern CSS)
        pageStructure: {
            maxWidth: null,        // Max content width
            pagePadding: null,     // Page edge padding
            sectionGaps: [],       // Gaps between sections
            gridAreas: []          // Named grid areas if any
        }
    };

    // Helper function to get a meaningful selector for an element
    function getSelector(el) {
        if (el.id) return '#' + el.id;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(' ').filter(c => c).slice(0, 2).join('.');
            if (classes) return el.tagName.toLowerCase() + '.' + classes;
        }
        return el.tagName.toLowerCase();
    }

    // Helper to check if a value is meaningful (not default)
    function isSignificant(value, defaults) {
        return value && !defaults.includes(value);
    }

    // ==========================================================================
    // GRID LAYOUT DETECTION
    // ==========================================================================

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        // Detect CSS Grid containers
        if (s.display === 'grid' || s.display === 'inline-grid') {
            const gridInfo = {
                selector: getSelector(el),
                display: s.display,
                gridTemplateColumns: s.gridTemplateColumns,
                gridTemplateRows: s.gridTemplateRows,
                gridTemplateAreas: s.gridTemplateAreas !== 'none' ? s.gridTemplateAreas : null,
                gap: s.gap,
                rowGap: s.rowGap,
                columnGap: s.columnGap,
                justifyItems: s.justifyItems,
                alignItems: s.alignItems,
                justifyContent: s.justifyContent,
                alignContent: s.alignContent,
                childCount: el.children.length
            };

            // Only add if it has meaningful grid structure
            if (gridInfo.gridTemplateColumns !== 'none' ||
                gridInfo.gridTemplateRows !== 'none' ||
                gridInfo.gridTemplateAreas) {
                result.layoutMethod.grid.push(gridInfo);
            }

            // Track named grid areas
            if (gridInfo.gridTemplateAreas) {
                result.pageStructure.gridAreas.push({
                    selector: gridInfo.selector,
                    areas: gridInfo.gridTemplateAreas
                });
            }
        }
    });

    // ==========================================================================
    // FLEXBOX LAYOUT DETECTION
    // ==========================================================================

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        if (s.display === 'flex' || s.display === 'inline-flex') {
            const flexInfo = {
                selector: getSelector(el),
                display: s.display,
                flexDirection: s.flexDirection,
                flexWrap: s.flexWrap,
                justifyContent: s.justifyContent,
                alignItems: s.alignItems,
                alignContent: s.alignContent,
                gap: s.gap,
                rowGap: s.rowGap,
                columnGap: s.columnGap,
                childCount: el.children.length
            };

            // Only add if it's not a basic default flex
            if (flexInfo.flexDirection !== 'row' ||
                flexInfo.flexWrap !== 'nowrap' ||
                flexInfo.justifyContent !== 'normal' ||
                flexInfo.alignItems !== 'normal' ||
                flexInfo.gap !== 'normal') {
                result.layoutMethod.flexbox.push(flexInfo);
            }
        }
    });

    // ==========================================================================
    // POSITIONED ELEMENTS (Stacking Contexts)
    // ==========================================================================

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);
        const position = s.position;
        const zIndex = s.zIndex;

        // Detect positioned elements that create stacking contexts
        if (position === 'absolute' || position === 'fixed' || position === 'sticky') {
            const posInfo = {
                selector: getSelector(el),
                position: position,
                zIndex: zIndex,
                top: s.top,
                right: s.right,
                bottom: s.bottom,
                left: s.left,
                inset: s.inset
            };

            result.layoutMethod.positioned.push(posInfo);
        }

        // Detect stacking contexts (created by various CSS properties)
        const createsStackingContext = (
            (position !== 'static' && zIndex !== 'auto') ||
            s.opacity !== '1' ||
            s.transform !== 'none' ||
            s.filter !== 'none' ||
            s.perspective !== 'none' ||
            s.clipPath !== 'none' ||
            s.mask !== 'none' ||
            s.isolation === 'isolate' ||
            s.mixBlendMode !== 'normal' ||
            s.contain === 'layout' ||
            s.contain === 'paint' ||
            s.contain === 'strict' ||
            s.contain === 'content' ||
            s.willChange.includes('transform') ||
            s.willChange.includes('opacity')
        );

        if (createsStackingContext) {
            let reason = [];
            if (position !== 'static' && zIndex !== 'auto') reason.push('position + z-index');
            if (s.opacity !== '1') reason.push('opacity');
            if (s.transform !== 'none') reason.push('transform');
            if (s.filter !== 'none') reason.push('filter');
            if (s.isolation === 'isolate') reason.push('isolation');
            if (s.mixBlendMode !== 'normal') reason.push('mix-blend-mode');

            result.stackingContexts.push({
                selector: getSelector(el),
                zIndex: zIndex,
                position: position,
                reason: reason.join(', ') || 'other',
                opacity: s.opacity,
                transform: s.transform !== 'none' ? 'has transform' : null
            });
        }
    });

    // Sort stacking contexts by z-index (numeric)
    result.stackingContexts.sort((a, b) => {
        const aZ = parseInt(a.zIndex) || 0;
        const bZ = parseInt(b.zIndex) || 0;
        return bZ - aZ; // Highest first
    });

    // ==========================================================================
    // FLOAT DETECTION (Legacy Layouts)
    // ==========================================================================

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);
        if (s.float === 'left' || s.float === 'right') {
            result.layoutMethod.floats.push({
                selector: getSelector(el),
                float: s.float,
                clear: s.clear
            });
        }
    });

    // ==========================================================================
    // MEDIA QUERY BREAKPOINTS
    // ==========================================================================

    const breakpointSet = new Set();

    Array.from(document.styleSheets).forEach(sheet => {
        try {
            Array.from(sheet.cssRules || []).forEach(rule => {
                if (rule instanceof CSSMediaRule) {
                    const query = rule.conditionText || rule.media.mediaText;
                    breakpointSet.add(query);

                    // Extract numeric breakpoints
                    const widthMatch = query.match(/\((?:max|min)-width:\s*(\d+)(?:px|em|rem)\)/);
                    if (widthMatch) {
                        result.breakpoints.push({
                            query: query,
                            value: parseInt(widthMatch[1]),
                            type: query.includes('max-width') ? 'max' : 'min',
                            rulesCount: rule.cssRules ? rule.cssRules.length : 0
                        });
                    }
                }

                // Container queries (modern CSS)
                if (rule instanceof CSSContainerRule) {
                    result.containerQueries.push({
                        name: rule.containerName,
                        query: rule.conditionText,
                        rulesCount: rule.cssRules ? rule.cssRules.length : 0
                    });
                }
            });
        } catch (e) {
            // CORS blocked - skip this stylesheet
        }
    });

    // Sort breakpoints by value
    result.breakpoints.sort((a, b) => a.value - b.value);

    // Deduplicate breakpoints
    result.breakpoints = result.breakpoints.filter((bp, index, self) =>
        index === self.findIndex(b => b.value === bp.value && b.type === bp.type)
    );

    // ==========================================================================
    // PAGE STRUCTURE ANALYSIS
    // ==========================================================================

    // Find max-width container
    const containers = document.querySelectorAll('[class*="container"], [class*="wrapper"], main, .content');
    containers.forEach(el => {
        const s = getComputedStyle(el);
        const maxWidth = s.maxWidth;
        if (maxWidth && maxWidth !== 'none' && maxWidth !== '100%') {
            if (!result.pageStructure.maxWidth ||
                parseInt(maxWidth) > parseInt(result.pageStructure.maxWidth)) {
                result.pageStructure.maxWidth = maxWidth;
            }
        }
    });

    // Find page padding
    const body = document.body;
    const bodyStyle = getComputedStyle(body);
    result.pageStructure.pagePadding = {
        paddingLeft: bodyStyle.paddingLeft,
        paddingRight: bodyStyle.paddingRight,
        paddingTop: bodyStyle.paddingTop,
        paddingBottom: bodyStyle.paddingBottom
    };

    // Check main/wrapper padding too
    const main = document.querySelector('main, [class*="container"], [class*="wrapper"]');
    if (main) {
        const mainStyle = getComputedStyle(main);
        if (parseInt(mainStyle.paddingLeft) > parseInt(bodyStyle.paddingLeft)) {
            result.pageStructure.pagePadding = {
                paddingLeft: mainStyle.paddingLeft,
                paddingRight: mainStyle.paddingRight,
                source: getSelector(main)
            };
        }
    }

    // Find section gaps
    const sections = document.querySelectorAll('section, [class*="section"]');
    sections.forEach(section => {
        const s = getComputedStyle(section);
        if (s.marginTop && s.marginTop !== '0px') {
            result.pageStructure.sectionGaps.push(s.marginTop);
        }
        if (s.paddingTop && s.paddingTop !== '0px') {
            result.pageStructure.sectionGaps.push(s.paddingTop);
        }
    });

    // Deduplicate and sort section gaps
    result.pageStructure.sectionGaps = [...new Set(result.pageStructure.sectionGaps)]
        .map(g => parseInt(g))
        .filter(g => g > 20) // Only significant gaps
        .sort((a, b) => a - b)
        .map(g => g + 'px');

    // ==========================================================================
    // SUMMARY
    // ==========================================================================

    result.summary = {
        primaryLayout: result.layoutMethod.grid.length > 0 ? 'grid' :
                       result.layoutMethod.flexbox.length > 0 ? 'flexbox' : 'block',
        gridCount: result.layoutMethod.grid.length,
        flexboxCount: result.layoutMethod.flexbox.length,
        positionedCount: result.layoutMethod.positioned.length,
        floatCount: result.layoutMethod.floats.length,
        breakpointCount: result.breakpoints.length,
        hasContainerQueries: result.containerQueries.length > 0,
        maxZIndex: result.stackingContexts.length > 0 ?
                   Math.max(...result.stackingContexts.map(s => parseInt(s.zIndex) || 0)) : 0,
        contentMaxWidth: result.pageStructure.maxWidth,
        commonBreakpoints: result.breakpoints.map(b => b.value)
    };

    return result;
})();
