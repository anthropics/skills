/**
 * Computed Measurements Extraction Script (v4.0)
 *
 * Extracts exact pixel measurements from key layout elements using
 * getComputedStyle() and getBoundingClientRect(). This gives Gemini exact
 * Tailwind values (h-[52px], max-w-[1496px]) instead of guessing from screenshots.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with per-element computed measurements
 */
(function() {
    const result = {
        viewport: {
            width: window.innerWidth,
            height: window.innerHeight,
            devicePixelRatio: window.devicePixelRatio
        },
        header: null,
        hero: null,
        containers: [],
        logoBar: null,
        gridSections: [],
        footer: null,
        metadata: {
            extractedAt: new Date().toISOString()
        }
    };

    // Helper: extract key computed styles from an element
    function getMeasurements(el) {
        if (!el) return null;
        const cs = getComputedStyle(el);
        const rect = el.getBoundingClientRect();
        return {
            // Box model
            width: Math.round(rect.width) + 'px',
            height: Math.round(rect.height) + 'px',
            // Max constraints
            maxWidth: cs.maxWidth,
            maxHeight: cs.maxHeight,
            minHeight: cs.minHeight,
            // Padding
            paddingTop: cs.paddingTop,
            paddingRight: cs.paddingRight,
            paddingBottom: cs.paddingBottom,
            paddingLeft: cs.paddingLeft,
            // Margin
            marginTop: cs.marginTop,
            marginBottom: cs.marginBottom,
            marginLeft: cs.marginLeft,
            marginRight: cs.marginRight,
            // Position
            position: cs.position,
            top: cs.top,
            zIndex: cs.zIndex,
            // Display
            display: cs.display,
            flexDirection: cs.flexDirection !== 'row' ? cs.flexDirection : undefined,
            justifyContent: cs.justifyContent !== 'normal' ? cs.justifyContent : undefined,
            alignItems: cs.alignItems !== 'normal' ? cs.alignItems : undefined,
            gap: cs.gap !== 'normal' ? cs.gap : undefined,
            // Grid
            gridTemplateColumns: cs.gridTemplateColumns !== 'none' ? cs.gridTemplateColumns : undefined,
            gridTemplateRows: cs.gridTemplateRows !== 'none' ? cs.gridTemplateRows : undefined,
            // Typography (only if relevant)
            fontSize: cs.fontSize,
            lineHeight: cs.lineHeight,
            fontWeight: cs.fontWeight,
            letterSpacing: cs.letterSpacing !== 'normal' ? cs.letterSpacing : undefined,
            fontFamily: cs.fontFamily,
            // Visual
            backgroundColor: cs.backgroundColor !== 'rgba(0, 0, 0, 0)' ? cs.backgroundColor : undefined,
            borderRadius: cs.borderRadius !== '0px' ? cs.borderRadius : undefined,
            // Overflow
            overflow: cs.overflow !== 'visible' ? cs.overflow : undefined,
            // Selector hint
            _selector: el.tagName.toLowerCase() + (el.id ? '#' + el.id : '') + (el.className ? '.' + el.className.toString().split(' ')[0] : '')
        };
    }

    // Helper: compact measurements (remove undefined values)
    function compact(obj) {
        if (!obj) return null;
        const cleaned = {};
        for (const [k, v] of Object.entries(obj)) {
            if (v !== undefined && v !== null && v !== 'none' && v !== 'normal' && v !== 'auto' && v !== '0px') {
                cleaned[k] = v;
            }
        }
        // Always keep width, height, maxWidth even if "auto"/"none"
        cleaned.width = obj.width;
        cleaned.height = obj.height;
        if (obj.maxWidth) cleaned.maxWidth = obj.maxWidth;
        return cleaned;
    }

    // ==========================================================================
    // HEADER / NAV
    // ==========================================================================
    const header = document.querySelector('header');
    if (header) {
        result.header = {
            outer: compact(getMeasurements(header)),
            inner: null
        };
        // Inner container (usually a div with max-width)
        const innerContainer = header.querySelector('[class*="container"], [class*="wrapper"], [class*="inner"]')
            || header.children[0];
        if (innerContainer && innerContainer !== header) {
            result.header.inner = compact(getMeasurements(innerContainer));
        }
        // Nav element if separate from header
        const nav = header.querySelector('nav');
        if (nav) {
            result.header.nav = compact(getMeasurements(nav));
        }
    }

    // ==========================================================================
    // HERO (first h1 and its container)
    // ==========================================================================
    const h1 = document.querySelector('h1');
    if (h1) {
        const heroSection = h1.closest('section') || h1.parentElement;
        result.hero = {
            section: compact(getMeasurements(heroSection)),
            h1: compact(getMeasurements(h1)),
            // Also capture font-variation-settings for the heading
            h1FontVariation: getComputedStyle(h1).fontVariationSettings || null,
            h1TextRendering: getComputedStyle(h1).textRendering || null
        };
        // Hero subtitle / description
        const heroP = heroSection.querySelector('p');
        if (heroP) {
            result.hero.subtitle = compact(getMeasurements(heroP));
        }
        // Hero CTA container
        const ctaContainer = heroSection.querySelector('[class*="cta"], [class*="button"], [class*="action"]');
        if (ctaContainer) {
            result.hero.ctaContainer = compact(getMeasurements(ctaContainer));
        }
    }

    // ==========================================================================
    // CONTAINERS (all elements with max-width set)
    // ==========================================================================
    const potentialContainers = document.querySelectorAll(
        '[class*="container"], [class*="wrapper"], [class*="inner"], main > * > div:first-child'
    );
    const seenMaxWidths = new Set();
    potentialContainers.forEach(el => {
        const cs = getComputedStyle(el);
        const maxW = cs.maxWidth;
        if (maxW && maxW !== 'none' && !seenMaxWidths.has(maxW)) {
            seenMaxWidths.add(maxW);
            result.containers.push({
                maxWidth: maxW,
                paddingLeft: cs.paddingLeft,
                paddingRight: cs.paddingRight,
                marginLeft: cs.marginLeft,
                marginRight: cs.marginRight,
                _selector: el.tagName.toLowerCase() + (el.className ? '.' + el.className.toString().split(' ')[0] : '')
            });
        }
    });

    // ==========================================================================
    // LOGO BAR
    // ==========================================================================
    const allSections = document.querySelectorAll('section, [class*="logo"], [class*="partner"], [class*="client"]');
    for (const section of allSections) {
        const imgs = section.querySelectorAll('img');
        if (imgs.length >= 4) {
            let allSmall = true;
            imgs.forEach(img => {
                if (img.getBoundingClientRect().height > 80) allSmall = false;
            });
            if (allSmall) {
                const container = section.querySelector('div') || section;
                const flexParent = imgs[0].parentElement.parentElement || container;
                result.logoBar = {
                    section: compact(getMeasurements(section)),
                    container: compact(getMeasurements(container)),
                    flexParent: compact(getMeasurements(flexParent)),
                    itemCount: imgs.length,
                    firstItemHeight: Math.round(imgs[0].getBoundingClientRect().height) + 'px',
                    // Measure gap between first two items
                    gapBetweenItems: null
                };
                if (imgs.length >= 2) {
                    const rect1 = imgs[0].parentElement.getBoundingClientRect();
                    const rect2 = imgs[1].parentElement.getBoundingClientRect();
                    result.logoBar.gapBetweenItems = Math.round(rect2.left - rect1.right) + 'px';
                }
                break;
            }
        }
    }

    // ==========================================================================
    // GRID SECTIONS (detect CSS Grid or multi-column Flexbox)
    // ==========================================================================
    document.querySelectorAll('section').forEach((section, index) => {
        const children = section.querySelectorAll(':scope > div, :scope > div > div');
        children.forEach(div => {
            const cs = getComputedStyle(div);
            const isGrid = cs.display === 'grid' || cs.display === 'inline-grid';
            const isFlexWrap = cs.display === 'flex' && cs.flexWrap === 'wrap';
            const isMultiCol = cs.display === 'flex' && div.children.length >= 2;

            if (isGrid || isFlexWrap) {
                result.gridSections.push({
                    sectionIndex: index,
                    type: isGrid ? 'grid' : 'flexWrap',
                    measurements: compact(getMeasurements(div)),
                    childCount: div.children.length,
                    firstChild: div.children[0] ? compact(getMeasurements(div.children[0])) : null,
                    // For cards: aspect ratio
                    firstChildAspectRatio: div.children[0] ?
                        (div.children[0].getBoundingClientRect().width /
                         div.children[0].getBoundingClientRect().height).toFixed(2) : null
                });
            }
        });
    });

    // ==========================================================================
    // FOOTER
    // ==========================================================================
    const footer = document.querySelector('footer');
    if (footer) {
        result.footer = {
            outer: compact(getMeasurements(footer)),
            inner: null,
            columns: []
        };
        const footerInner = footer.querySelector('[class*="container"], [class*="wrapper"], [class*="inner"]')
            || footer.children[0];
        if (footerInner && footerInner !== footer) {
            result.footer.inner = compact(getMeasurements(footerInner));
        }
        // Footer column layout
        const footerGrid = footer.querySelector('[class*="grid"], [class*="columns"]')
            || footerInner;
        if (footerGrid) {
            const fcs = getComputedStyle(footerGrid);
            result.footer.gridLayout = {
                display: fcs.display,
                gridTemplateColumns: fcs.gridTemplateColumns !== 'none' ? fcs.gridTemplateColumns : undefined,
                gap: fcs.gap !== 'normal' ? fcs.gap : undefined,
                flexDirection: fcs.flexDirection,
                justifyContent: fcs.justifyContent
            };
        }
        // Individual column measurements (first 6)
        const colEls = footer.querySelectorAll('nav, [class*="col"], [class*="group"]');
        for (let i = 0; i < Math.min(colEls.length, 6); i++) {
            result.footer.columns.push(compact(getMeasurements(colEls[i])));
        }
    }

    // ==========================================================================
    // SUMMARY
    // ==========================================================================
    result.summary = {
        headerHeight: result.header ? result.header.outer.height : null,
        heroH1FontSize: result.hero ? result.hero.h1.fontSize : null,
        heroH1MaxWidth: result.hero ? result.hero.h1.maxWidth : null,
        primaryMaxWidth: result.containers.length > 0 ? result.containers[0].maxWidth : null,
        primaryPadding: result.containers.length > 0 ? result.containers[0].paddingLeft : null,
        logoBarItemCount: result.logoBar ? result.logoBar.itemCount : 0,
        gridSectionCount: result.gridSections.length,
        footerHeight: result.footer ? result.footer.outer.height : null
    };

    return result;
})();
