/**
 * Component Semantic Analysis Script (v4.0)
 *
 * Analyzes ARIA landmarks, component patterns, section structure, and accessibility.
 * This ensures Gemini generates properly structured, accessible components.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with component analysis
 */
(function() {
    const result = {
        landmarks: [],       // ARIA landmarks (header, nav, main, footer, etc.)
        sections: [],        // Page sections with context
        components: [],      // Detected component patterns
        accessibility: {
            hasSkipLinks: false,
            hasFocusManagement: false,
            hasAriaLiveRegions: false,
            formLabelsComplete: true,
            imagesHaveAlt: true
        },
        navigation: {
            primary: null,
            secondary: [],
            breadcrumbs: null,
            pagination: null
        },
        interactiveElements: {
            buttons: [],
            links: [],
            forms: []
        }
    };

    // Helper function to get a meaningful selector
    function getSelector(el) {
        if (el.id) return '#' + el.id;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(' ').filter(c => c).slice(0, 2).join('.');
            if (classes) return el.tagName.toLowerCase() + '.' + classes;
        }
        return el.tagName.toLowerCase();
    }

    // Helper to get text content preview
    function getTextPreview(el, maxLength = 50) {
        const text = el.textContent?.trim().replace(/\s+/g, ' ') || '';
        return text.length > maxLength ? text.slice(0, maxLength) + '...' : text;
    }

    // ==========================================================================
    // ARIA LANDMARKS
    // ==========================================================================

    // Implicit landmarks (HTML5 semantic elements)
    const implicitLandmarks = {
        'HEADER': 'banner',
        'NAV': 'navigation',
        'MAIN': 'main',
        'FOOTER': 'contentinfo',
        'ASIDE': 'complementary',
        'FORM': 'form',
        'SECTION': 'region',
        'ARTICLE': 'article'
    };

    // Find all landmark elements
    const landmarkElements = document.querySelectorAll(
        'header, nav, main, footer, aside, section, article, [role]'
    );

    landmarkElements.forEach(el => {
        const explicitRole = el.getAttribute('role');
        const implicitRole = implicitLandmarks[el.tagName];
        const role = explicitRole || implicitRole;

        if (role) {
            const landmark = {
                tag: el.tagName.toLowerCase(),
                role: role,
                selector: getSelector(el),
                ariaLabel: el.getAttribute('aria-label'),
                ariaLabelledby: el.getAttribute('aria-labelledby'),
                childrenCount: el.children.length,
                hasHeading: !!el.querySelector('h1, h2, h3, h4, h5, h6'),
                firstHeading: el.querySelector('h1, h2, h3, h4, h5, h6')?.textContent?.trim().slice(0, 50)
            };

            // Skip empty sections
            if (el.tagName === 'SECTION' && !landmark.ariaLabel && !landmark.firstHeading) {
                return;
            }

            result.landmarks.push(landmark);
        }
    });

    // ==========================================================================
    // SECTION STRUCTURE
    // ==========================================================================

    const sections = document.querySelectorAll('section, [id], [class*="section"]');
    const processedIds = new Set();

    sections.forEach(el => {
        const id = el.id;
        if (id && processedIds.has(id)) return;
        if (id) processedIds.add(id);

        const section = {
            id: id || null,
            tag: el.tagName.toLowerCase(),
            classes: el.className && typeof el.className === 'string' ?
                     el.className.split(' ').filter(c => c).slice(0, 3) : [],
            heading: null,
            headingLevel: null,
            textPreview: null,
            hasImages: el.querySelectorAll('img, picture, video').length > 0,
            hasCTA: !!el.querySelector('a[href], button'),
            estimatedPurpose: null
        };

        // Find section heading
        const heading = el.querySelector('h1, h2, h3, h4, h5, h6');
        if (heading) {
            section.heading = heading.textContent?.trim().slice(0, 100);
            section.headingLevel = parseInt(heading.tagName[1]);
        }

        // Try to guess section purpose from class names and content
        const classStr = (section.classes.join(' ') + ' ' + (section.id || '')).toLowerCase();
        const contentText = el.textContent?.toLowerCase() || '';

        if (classStr.includes('hero') || el.querySelector('h1')) {
            section.estimatedPurpose = 'hero';
        } else if (classStr.includes('feature') || classStr.includes('benefit')) {
            section.estimatedPurpose = 'features';
        } else if (classStr.includes('pricing') || classStr.includes('plan')) {
            section.estimatedPurpose = 'pricing';
        } else if (classStr.includes('testimonial') || classStr.includes('review')) {
            section.estimatedPurpose = 'testimonials';
        } else if (classStr.includes('faq') || classStr.includes('question')) {
            section.estimatedPurpose = 'faq';
        } else if (classStr.includes('team') || classStr.includes('about')) {
            section.estimatedPurpose = 'about/team';
        } else if (classStr.includes('contact') || el.querySelector('form')) {
            section.estimatedPurpose = 'contact';
        } else if (classStr.includes('cta') || classStr.includes('call-to-action')) {
            section.estimatedPurpose = 'cta';
        } else if (classStr.includes('footer')) {
            section.estimatedPurpose = 'footer';
        } else if (classStr.includes('header') || classStr.includes('nav')) {
            section.estimatedPurpose = 'header';
        }

        // Only add meaningful sections
        if (section.heading || section.id || section.estimatedPurpose) {
            result.sections.push(section);
        }
    });

    // ==========================================================================
    // COMPONENT PATTERN DETECTION
    // ==========================================================================

    const componentPatterns = [
        {
            name: 'modal',
            selectors: '[class*="modal"], [role="dialog"], [aria-modal="true"], [class*="popup"], [class*="overlay"]',
            type: 'modal'
        },
        {
            name: 'dropdown',
            selectors: '[class*="dropdown"], [role="menu"], [aria-haspopup="true"], [class*="select"]',
            type: 'dropdown'
        },
        {
            name: 'accordion',
            selectors: '[class*="accordion"], [class*="collapsible"], [data-state="open"], [class*="expand"]',
            type: 'accordion'
        },
        {
            name: 'tabs',
            selectors: '[role="tablist"], [class*="tabs"], [class*="tab-panel"], [role="tabpanel"]',
            type: 'tabs'
        },
        {
            name: 'carousel',
            selectors: '[class*="carousel"], [class*="slider"], [class*="swiper"], [class*="slick"], [class*="glide"]',
            type: 'carousel'
        },
        {
            name: 'toast',
            selectors: '[class*="toast"], [class*="notification"], [class*="snackbar"], [role="alert"]',
            type: 'toast'
        },
        {
            name: 'tooltip',
            selectors: '[class*="tooltip"], [role="tooltip"], [data-tooltip]',
            type: 'tooltip'
        },
        {
            name: 'card',
            selectors: '[class*="card"], article, [class*="tile"]',
            type: 'card'
        },
        {
            name: 'badge',
            selectors: '[class*="badge"], [class*="tag"], [class*="chip"], [class*="label"]',
            type: 'badge'
        },
        {
            name: 'avatar',
            selectors: '[class*="avatar"], [class*="profile-image"]',
            type: 'avatar'
        },
        {
            name: 'progress',
            selectors: '[class*="progress"], [role="progressbar"], [class*="loading"]',
            type: 'progress'
        },
        {
            name: 'skeleton',
            selectors: '[class*="skeleton"], [class*="shimmer"], [class*="placeholder"]',
            type: 'skeleton'
        },
        {
            name: 'form',
            selectors: 'form, [role="form"], [class*="form"]',
            type: 'form'
        },
        {
            name: 'search',
            selectors: '[type="search"], [class*="search"], [role="search"]',
            type: 'search'
        },
        {
            name: 'datepicker',
            selectors: '[class*="datepicker"], [class*="calendar"], [type="date"]',
            type: 'datepicker'
        },
        {
            name: 'table',
            selectors: 'table, [role="table"], [class*="data-table"], [role="grid"]',
            type: 'table'
        }
    ];

    componentPatterns.forEach(({name, selectors, type}) => {
        const elements = document.querySelectorAll(selectors);
        if (elements.length > 0) {
            const firstEl = elements[0];
            result.components.push({
                type: type,
                count: elements.length,
                sampleSelector: getSelector(firstEl),
                sampleClasses: firstEl.className && typeof firstEl.className === 'string' ?
                               firstEl.className.split(' ').filter(c => c).slice(0, 3).join(' ') : '',
                hasAriaLabel: !!firstEl.getAttribute('aria-label'),
                hasRole: !!firstEl.getAttribute('role')
            });
        }
    });

    // ==========================================================================
    // NAVIGATION ANALYSIS
    // ==========================================================================

    // Primary navigation
    const nav = document.querySelector('nav, [role="navigation"]');
    if (nav) {
        const navLinks = nav.querySelectorAll('a');
        result.navigation.primary = {
            selector: getSelector(nav),
            linkCount: navLinks.length,
            links: Array.from(navLinks).slice(0, 10).map(a => ({
                text: a.textContent?.trim().slice(0, 30),
                href: a.getAttribute('href'),
                hasDropdown: !!a.querySelector('[class*="dropdown"], [role="menu"]') ||
                             !!a.getAttribute('aria-haspopup')
            })),
            hasLogo: !!nav.querySelector('img, svg, [class*="logo"]'),
            hasMobileToggle: !!nav.querySelector('[class*="hamburger"], [class*="toggle"], [class*="menu-btn"]')
        };
    }

    // Breadcrumbs
    const breadcrumbs = document.querySelector('[class*="breadcrumb"], [aria-label*="breadcrumb"], nav[aria-label="Breadcrumb"]');
    if (breadcrumbs) {
        result.navigation.breadcrumbs = {
            selector: getSelector(breadcrumbs),
            itemCount: breadcrumbs.querySelectorAll('a, li').length
        };
    }

    // Pagination
    const pagination = document.querySelector('[class*="pagination"], [role="navigation"][aria-label*="pagination"]');
    if (pagination) {
        result.navigation.pagination = {
            selector: getSelector(pagination),
            hasNumbers: !!pagination.querySelector('[class*="page-number"], [aria-current]'),
            hasPrevNext: !!pagination.querySelector('[class*="prev"], [class*="next"]')
        };
    }

    // ==========================================================================
    // ACCESSIBILITY AUDIT
    // ==========================================================================

    // Skip links
    result.accessibility.hasSkipLinks = !!document.querySelector(
        'a[href="#main"], a[href="#content"], [class*="skip"]'
    );

    // Focus management (tabindex usage)
    result.accessibility.hasFocusManagement = document.querySelectorAll('[tabindex]').length > 0;

    // Live regions
    result.accessibility.hasAriaLiveRegions = !!document.querySelector(
        '[aria-live], [role="alert"], [role="status"], [role="log"]'
    );

    // Form label completeness
    const inputs = document.querySelectorAll('input:not([type="hidden"]):not([type="submit"]):not([type="button"]), textarea, select');
    let unlabeledInputs = 0;
    inputs.forEach(input => {
        const id = input.id;
        const hasLabel = id && document.querySelector(`label[for="${id}"]`);
        const hasAriaLabel = input.getAttribute('aria-label');
        const hasAriaLabelledby = input.getAttribute('aria-labelledby');
        const hasPlaceholder = input.getAttribute('placeholder');

        if (!hasLabel && !hasAriaLabel && !hasAriaLabelledby && !hasPlaceholder) {
            unlabeledInputs++;
        }
    });
    result.accessibility.formLabelsComplete = unlabeledInputs === 0;
    result.accessibility.unlabeledInputCount = unlabeledInputs;

    // Images without alt
    const images = document.querySelectorAll('img');
    let imagesWithoutAlt = 0;
    images.forEach(img => {
        if (!img.hasAttribute('alt')) {
            imagesWithoutAlt++;
        }
    });
    result.accessibility.imagesHaveAlt = imagesWithoutAlt === 0;
    result.accessibility.imagesWithoutAltCount = imagesWithoutAlt;

    // ==========================================================================
    // INTERACTIVE ELEMENTS
    // ==========================================================================

    // Buttons
    const buttons = document.querySelectorAll('button, [role="button"], input[type="button"], input[type="submit"]');
    result.interactiveElements.buttons = Array.from(buttons).slice(0, 20).map(btn => ({
        text: btn.textContent?.trim().slice(0, 30) || btn.value,
        selector: getSelector(btn),
        type: btn.type || 'button',
        hasIcon: !!btn.querySelector('svg, [class*="icon"]')
    }));

    // Forms
    const forms = document.querySelectorAll('form');
    result.interactiveElements.forms = Array.from(forms).map(form => ({
        selector: getSelector(form),
        action: form.action,
        method: form.method,
        inputCount: form.querySelectorAll('input, textarea, select').length,
        hasSubmit: !!form.querySelector('[type="submit"], button:not([type="button"])')
    }));

    // ==========================================================================
    // SUMMARY
    // ==========================================================================

    result.summary = {
        landmarkCount: result.landmarks.length,
        sectionCount: result.sections.length,
        componentTypes: result.components.map(c => c.type),
        hasNavigation: !!result.navigation.primary,
        hasBreadcrumbs: !!result.navigation.breadcrumbs,
        hasPagination: !!result.navigation.pagination,
        accessibilityScore: (
            (result.accessibility.hasSkipLinks ? 1 : 0) +
            (result.accessibility.formLabelsComplete ? 1 : 0) +
            (result.accessibility.imagesHaveAlt ? 1 : 0) +
            (result.accessibility.hasAriaLiveRegions ? 1 : 0)
        ) + '/4',
        formCount: result.interactiveElements.forms.length,
        buttonCount: result.interactiveElements.buttons.length,
        estimatedSections: result.sections
            .filter(s => s.estimatedPurpose)
            .map(s => s.estimatedPurpose)
    };

    return result;
})();
