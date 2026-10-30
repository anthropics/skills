/**
 * Framework Detection Script (v4.0)
 *
 * Detects CSS frameworks, animation libraries, icon systems, and component libraries.
 * This information tells Gemini exactly what to generate.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with detected frameworks and libraries
 */
(function() {
    const result = {
        cssFramework: {
            tailwind: false,
            bootstrap: false,
            bulma: false,
            foundation: false,
            custom: true,
            detected: null,
            confidence: 'low'
        },
        jsLibraries: {
            gsap: false,
            scrollTrigger: false,
            framerMotion: false,
            aos: false,
            lenis: false,
            locomotiveScroll: false,
            barba: false,
            animejs: false,
            detected: [],
            primaryAnimation: null
        },
        iconLibrary: {
            heroicons: false,
            lucide: false,
            fontAwesome: false,
            phosphor: false,
            feather: false,
            materialIcons: false,
            inlineSvgCount: 0,
            detected: null
        },
        componentLibrary: {
            radix: false,
            shadcn: false,
            headlessUI: false,
            chakra: false,
            mui: false,
            antDesign: false,
            detected: null
        },
        buildTool: {
            nextjs: false,
            vite: false,
            webpack: false,
            parcel: false,
            detected: null
        },
        uiPatterns: {
            hasStickyNav: false,
            hasHamburgerMenu: false,
            hasModal: false,
            hasDropdown: false,
            hasTabs: false,
            hasAccordion: false,
            hasCarousel: false,
            hasPricingTable: false,
            hasTestimonials: false,
            hasFaq: false
        }
    };

    // ==========================================================================
    // CSS FRAMEWORK DETECTION
    // ==========================================================================

    // Check for Tailwind CSS
    const tailwindPatterns = [
        'flex-', 'grid-', 'gap-', 'space-x-', 'space-y-',
        'px-', 'py-', 'mx-', 'my-', 'mt-', 'mb-', 'ml-', 'mr-',
        'text-sm', 'text-lg', 'text-xl', 'text-2xl',
        'bg-white', 'bg-black', 'bg-gray-', 'bg-blue-',
        'rounded-', 'shadow-', 'hover:', 'focus:',
        'w-full', 'h-full', 'min-h-', 'max-w-',
        'items-center', 'justify-between', 'justify-center'
    ];

    let tailwindScore = 0;
    const allClassNames = new Set();

    document.querySelectorAll('*').forEach(el => {
        if (el.className && typeof el.className === 'string') {
            el.className.split(' ').forEach(cls => allClassNames.add(cls));
        }
    });

    tailwindPatterns.forEach(pattern => {
        for (const cls of allClassNames) {
            if (cls.includes(pattern) || cls.startsWith(pattern)) {
                tailwindScore++;
                break;
            }
        }
    });

    if (tailwindScore > 10) {
        result.cssFramework.tailwind = true;
        result.cssFramework.detected = 'tailwind';
        result.cssFramework.confidence = tailwindScore > 20 ? 'high' : 'medium';
        result.cssFramework.custom = false;
    }

    // Check for Bootstrap
    const bootstrapClasses = ['container', 'row', 'col-', 'btn-primary', 'btn-secondary',
        'navbar', 'nav-item', 'nav-link', 'card-body', 'form-control', 'modal'];
    let bootstrapScore = 0;
    bootstrapClasses.forEach(cls => {
        if ([...allClassNames].some(c => c.includes(cls) || c === cls)) {
            bootstrapScore++;
        }
    });
    if (bootstrapScore > 5) {
        result.cssFramework.bootstrap = true;
        if (!result.cssFramework.detected) {
            result.cssFramework.detected = 'bootstrap';
            result.cssFramework.custom = false;
        }
    }

    // Check for Bulma
    const bulmaClasses = ['is-primary', 'is-info', 'is-success', 'columns', 'column', 'box', 'hero-body'];
    if (bulmaClasses.some(cls => allClassNames.has(cls))) {
        result.cssFramework.bulma = true;
        if (!result.cssFramework.detected) {
            result.cssFramework.detected = 'bulma';
            result.cssFramework.custom = false;
        }
    }

    // ==========================================================================
    // JS ANIMATION LIBRARY DETECTION
    // ==========================================================================

    // Check for GSAP
    if (typeof gsap !== 'undefined') {
        result.jsLibraries.gsap = true;
        result.jsLibraries.detected.push('gsap');
        result.jsLibraries.primaryAnimation = 'gsap';
    }

    // Check for ScrollTrigger
    if (typeof ScrollTrigger !== 'undefined') {
        result.jsLibraries.scrollTrigger = true;
        result.jsLibraries.detected.push('scrollTrigger');
    }

    // Check scripts for GSAP if not in window
    const scripts = Array.from(document.querySelectorAll('script[src]'));
    scripts.forEach(s => {
        const src = s.src.toLowerCase();
        if (src.includes('gsap') || src.includes('greensock')) {
            result.jsLibraries.gsap = true;
            if (!result.jsLibraries.detected.includes('gsap')) {
                result.jsLibraries.detected.push('gsap');
            }
            if (!result.jsLibraries.primaryAnimation) {
                result.jsLibraries.primaryAnimation = 'gsap';
            }
        }
        if (src.includes('scrolltrigger')) {
            result.jsLibraries.scrollTrigger = true;
            if (!result.jsLibraries.detected.includes('scrollTrigger')) {
                result.jsLibraries.detected.push('scrollTrigger');
            }
        }
        if (src.includes('framer-motion') || src.includes('motion')) {
            result.jsLibraries.framerMotion = true;
            result.jsLibraries.detected.push('framerMotion');
            if (!result.jsLibraries.primaryAnimation) {
                result.jsLibraries.primaryAnimation = 'framerMotion';
            }
        }
        if (src.includes('aos')) {
            result.jsLibraries.aos = true;
            result.jsLibraries.detected.push('aos');
        }
        if (src.includes('lenis')) {
            result.jsLibraries.lenis = true;
            result.jsLibraries.detected.push('lenis');
        }
        if (src.includes('locomotive')) {
            result.jsLibraries.locomotiveScroll = true;
            result.jsLibraries.detected.push('locomotiveScroll');
        }
        if (src.includes('anime')) {
            result.jsLibraries.animejs = true;
            result.jsLibraries.detected.push('animejs');
        }
        if (src.includes('barba')) {
            result.jsLibraries.barba = true;
            result.jsLibraries.detected.push('barba');
        }
    });

    // Check for Framer Motion via data attributes
    if (document.querySelector('[data-framer], [data-framer-appear-id]')) {
        result.jsLibraries.framerMotion = true;
        if (!result.jsLibraries.detected.includes('framerMotion')) {
            result.jsLibraries.detected.push('framerMotion');
        }
    }

    // Check for AOS via data attributes
    if (document.querySelector('[data-aos]')) {
        result.jsLibraries.aos = true;
        if (!result.jsLibraries.detected.includes('aos')) {
            result.jsLibraries.detected.push('aos');
        }
        if (!result.jsLibraries.primaryAnimation) {
            result.jsLibraries.primaryAnimation = 'aos';
        }
    }

    // Check for Lenis/Locomotive via globals or data attributes
    if (typeof Lenis !== 'undefined' || document.querySelector('[data-lenis-prevent]')) {
        result.jsLibraries.lenis = true;
        if (!result.jsLibraries.detected.includes('lenis')) {
            result.jsLibraries.detected.push('lenis');
        }
    }

    if (typeof LocomotiveScroll !== 'undefined' || document.querySelector('[data-scroll-container]')) {
        result.jsLibraries.locomotiveScroll = true;
        if (!result.jsLibraries.detected.includes('locomotiveScroll')) {
            result.jsLibraries.detected.push('locomotiveScroll');
        }
    }

    // ==========================================================================
    // ICON LIBRARY DETECTION
    // ==========================================================================

    // Count inline SVGs
    result.iconLibrary.inlineSvgCount = document.querySelectorAll('svg').length;

    // Check for Heroicons (commonly used with class patterns)
    if (document.querySelector('[class*="heroicon"], [data-icon*="hero"]')) {
        result.iconLibrary.heroicons = true;
        result.iconLibrary.detected = 'heroicons';
    }

    // Check for Lucide
    if (document.querySelector('[class*="lucide"]')) {
        result.iconLibrary.lucide = true;
        result.iconLibrary.detected = 'lucide';
    }

    // Check for Font Awesome
    if (document.querySelector('.fa, .fas, .fab, .far, .fal, .fad, [class*="fa-"]')) {
        result.iconLibrary.fontAwesome = true;
        result.iconLibrary.detected = 'fontAwesome';
    }

    // Check for Phosphor
    if (document.querySelector('[class*="ph-"]')) {
        result.iconLibrary.phosphor = true;
        result.iconLibrary.detected = 'phosphor';
    }

    // Check for Feather
    if (document.querySelector('[class*="feather"]')) {
        result.iconLibrary.feather = true;
        result.iconLibrary.detected = 'feather';
    }

    // Check for Material Icons
    if (document.querySelector('.material-icons, .material-icons-outlined, .material-symbols-outlined')) {
        result.iconLibrary.materialIcons = true;
        result.iconLibrary.detected = 'materialIcons';
    }

    // If no icon library detected but has SVGs, mark as inline
    if (!result.iconLibrary.detected && result.iconLibrary.inlineSvgCount > 0) {
        result.iconLibrary.detected = 'inline-svg';
    }

    // ==========================================================================
    // COMPONENT LIBRARY DETECTION
    // ==========================================================================

    // Check for Radix UI
    if (document.querySelector('[data-radix-collection-item], [data-state], [data-orientation]')) {
        result.componentLibrary.radix = true;
        result.componentLibrary.detected = 'radix';
    }

    // Check for Headless UI
    if (document.querySelector('[data-headlessui-state], [data-headlessui]')) {
        result.componentLibrary.headlessUI = true;
        result.componentLibrary.detected = 'headlessUI';
    }

    // Check for Chakra UI
    if (document.querySelector('[class*="chakra"]')) {
        result.componentLibrary.chakra = true;
        result.componentLibrary.detected = 'chakra';
    }

    // Check for MUI
    if (document.querySelector('[class*="Mui"], [class*="css-"][class*="MuiBox"]')) {
        result.componentLibrary.mui = true;
        result.componentLibrary.detected = 'mui';
    }

    // Check for Ant Design
    if (document.querySelector('[class*="ant-"]')) {
        result.componentLibrary.antDesign = true;
        result.componentLibrary.detected = 'antDesign';
    }

    // ==========================================================================
    // BUILD TOOL DETECTION
    // ==========================================================================

    // Check for Next.js
    if (document.querySelector('#__next') || document.querySelector('[data-nextjs-scroll-focus-boundary]')) {
        result.buildTool.nextjs = true;
        result.buildTool.detected = 'nextjs';
    }

    // Check for Vite (common dev script pattern)
    if (document.querySelector('script[type="module"][src*="@vite"]')) {
        result.buildTool.vite = true;
        result.buildTool.detected = 'vite';
    }

    // ==========================================================================
    // UI PATTERN DETECTION
    // ==========================================================================

    // Sticky navigation
    const nav = document.querySelector('nav, header');
    if (nav) {
        const navStyle = getComputedStyle(nav);
        result.uiPatterns.hasStickyNav = navStyle.position === 'sticky' || navStyle.position === 'fixed';
    }

    // Hamburger menu
    result.uiPatterns.hasHamburgerMenu = !!document.querySelector(
        '[class*="hamburger"], [class*="burger"], [class*="menu-toggle"], [aria-label*="menu"]'
    );

    // Modal
    result.uiPatterns.hasModal = !!document.querySelector(
        '[class*="modal"], [role="dialog"], [aria-modal="true"]'
    );

    // Dropdown
    result.uiPatterns.hasDropdown = !!document.querySelector(
        '[class*="dropdown"], [role="menu"], [aria-haspopup="true"]'
    );

    // Tabs
    result.uiPatterns.hasTabs = !!document.querySelector(
        '[role="tablist"], [class*="tabs"], [class*="tab-"]'
    );

    // Accordion
    result.uiPatterns.hasAccordion = !!document.querySelector(
        '[class*="accordion"], [class*="collapsible"], [data-state="open"], [data-state="closed"]'
    );

    // Carousel/Slider
    result.uiPatterns.hasCarousel = !!document.querySelector(
        '[class*="carousel"], [class*="slider"], [class*="swiper"], [class*="slick"]'
    );

    // Pricing table
    result.uiPatterns.hasPricingTable = !!document.querySelector(
        '[class*="pricing"], [class*="price-card"], [class*="plan"]'
    );

    // Testimonials
    result.uiPatterns.hasTestimonials = !!document.querySelector(
        '[class*="testimonial"], [class*="review"], [class*="quote"]'
    );

    // FAQ
    result.uiPatterns.hasFaq = !!document.querySelector(
        '[class*="faq"], [class*="question"], [itemtype*="FAQPage"]'
    );

    // ==========================================================================
    // SUMMARY
    // ==========================================================================

    result.summary = {
        css: result.cssFramework.detected || 'custom',
        animation: result.jsLibraries.primaryAnimation || (result.jsLibraries.detected.length > 0 ? result.jsLibraries.detected[0] : 'css-only'),
        icons: result.iconLibrary.detected || 'none',
        components: result.componentLibrary.detected || 'custom',
        build: result.buildTool.detected || 'unknown',
        allAnimationLibs: result.jsLibraries.detected,
        uiPatternsList: Object.entries(result.uiPatterns)
            .filter(([_, v]) => v === true)
            .map(([k, _]) => k.replace('has', ''))
    };

    return result;
})();
