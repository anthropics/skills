/**
 * Animation Mapping Script (v4.0 Enhanced)
 *
 * Deep analysis of scroll animations, GSAP configuration, and timing values.
 * Captures exact animation configurations for Gemini to reproduce.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with complete animation mapping
 */
(function() {
    const result = {
        library: {
            gsap: false,
            scrollTrigger: false,
            framerMotion: false,
            aos: false,
            lenis: false,
            locomotiveScroll: false,
            animejs: false,
            barba: false,
            detected: null
        },
        gsapConfig: {
            scrollTriggers: [],
            timelines: [],
            tweens: [],
            defaults: null
        },
        cssAnimations: {
            keyframes: [],
            transitions: []
        },
        scrollBehavior: {
            smooth: false,
            lenis: false,
            locomotive: false,
            native: true,
            scrollContainer: null
        },
        timingConstants: {
            easings: [],
            durations: [],
            delays: [],
            staggers: [],
            premiumEasing: null
        },
        animatedElements: [],     // Elements with animations
        hoverTransitions: [],     // Hover state transitions
        scrollRevealElements: [], // Elements that animate on scroll
        parallaxElements: []      // Parallax effects
    };

    // Helper to get selector
    function getSelector(el) {
        if (!el) return null;
        if (el.id) return '#' + el.id;
        if (el.className && typeof el.className === 'string') {
            const classes = el.className.trim().split(' ').filter(c => c).slice(0, 2).join('.');
            if (classes) return el.tagName.toLowerCase() + '.' + classes;
        }
        return el.tagName.toLowerCase();
    }

    // ==========================================================================
    // LIBRARY DETECTION
    // ==========================================================================

    // Check for GSAP
    if (typeof gsap !== 'undefined') {
        result.library.gsap = true;
        result.library.detected = 'gsap';

        // Try to get GSAP defaults
        try {
            result.gsapConfig.defaults = gsap.defaults();
        } catch (e) {}
    }

    // Check for ScrollTrigger
    if (typeof ScrollTrigger !== 'undefined') {
        result.library.scrollTrigger = true;

        // Try to extract active ScrollTriggers
        try {
            const triggers = ScrollTrigger.getAll();
            triggers.forEach(st => {
                const triggerEl = st.trigger;
                result.gsapConfig.scrollTriggers.push({
                    trigger: getSelector(triggerEl),
                    start: st.start,
                    end: st.end,
                    scrub: st.scrub,
                    pin: !!st.pin,
                    pinSpacing: st.pinSpacing,
                    markers: st.markers,
                    toggleActions: st.toggleActions,
                    animation: st.animation ? 'has animation' : null
                });
            });
        } catch (e) {
            result.gsapConfig.scrollTriggerError = e.message;
        }
    }

    // Check for GSAP via scripts
    const scripts = Array.from(document.querySelectorAll('script[src]'));
    scripts.forEach(s => {
        const src = s.src.toLowerCase();
        if (src.includes('gsap') || src.includes('greensock')) {
            result.library.gsap = true;
            if (!result.library.detected) result.library.detected = 'gsap';
        }
        if (src.includes('scrolltrigger')) {
            result.library.scrollTrigger = true;
        }
        if (src.includes('framer-motion')) {
            result.library.framerMotion = true;
            if (!result.library.detected) result.library.detected = 'framerMotion';
        }
        if (src.includes('aos')) {
            result.library.aos = true;
            if (!result.library.detected) result.library.detected = 'aos';
        }
        if (src.includes('lenis')) {
            result.library.lenis = true;
        }
        if (src.includes('locomotive')) {
            result.library.locomotiveScroll = true;
        }
        if (src.includes('anime')) {
            result.library.animejs = true;
            if (!result.library.detected) result.library.detected = 'animejs';
        }
    });

    // ==========================================================================
    // ES MODULE DETECTION FALLBACK
    // ==========================================================================
    // When GSAP is bundled as ES module (Vite/Webpack/Rollup), window.gsap is
    // undefined. Flag for extract_js_animations.js deep bundle forensics.

    if (typeof gsap === 'undefined') {
        const gsapScript = scripts.find(s => {
            const src = s.src.toLowerCase();
            return src.includes('gsap') || src.includes('scrolltrigger') || src.includes('greensock');
        });
        if (gsapScript) {
            result.gsapDetected = true;
            result.gsapBundleUrl = gsapScript.src;
            result.esModule = true;
            result.note = "GSAP loaded as ES module — run extract_js_animations.js for full configs";
        }
    }

    // Barba.js detection (page transitions)
    const barbaScript = scripts.find(s => s.src.toLowerCase().includes('barba'));
    if (barbaScript) {
        result.library.barba = true;
        result.barbaBundleUrl = barbaScript.src;
    }

    // Check for Framer Motion data attributes
    if (document.querySelector('[data-framer], [data-framer-appear-id]')) {
        result.library.framerMotion = true;
        if (!result.library.detected) result.library.detected = 'framerMotion';
    }

    // Check for AOS data attributes
    const aosElements = document.querySelectorAll('[data-aos]');
    if (aosElements.length > 0) {
        result.library.aos = true;
        if (!result.library.detected) result.library.detected = 'aos';

        // Extract AOS configurations
        aosElements.forEach(el => {
            result.scrollRevealElements.push({
                selector: getSelector(el),
                animation: el.getAttribute('data-aos'),
                duration: el.getAttribute('data-aos-duration'),
                delay: el.getAttribute('data-aos-delay'),
                easing: el.getAttribute('data-aos-easing'),
                offset: el.getAttribute('data-aos-offset'),
                once: el.getAttribute('data-aos-once')
            });
        });
    }

    // Check for Lenis
    if (typeof Lenis !== 'undefined' || document.querySelector('[data-lenis-prevent]')) {
        result.library.lenis = true;
        result.scrollBehavior.lenis = true;
        result.scrollBehavior.native = false;
    }

    // Check for Locomotive Scroll
    if (typeof LocomotiveScroll !== 'undefined' || document.querySelector('[data-scroll-container]')) {
        result.library.locomotiveScroll = true;
        result.scrollBehavior.locomotive = true;
        result.scrollBehavior.native = false;

        const scrollContainer = document.querySelector('[data-scroll-container]');
        if (scrollContainer) {
            result.scrollBehavior.scrollContainer = getSelector(scrollContainer);
        }

        // Extract data-scroll elements
        document.querySelectorAll('[data-scroll]').forEach(el => {
            const scrollData = {
                selector: getSelector(el),
                speed: el.getAttribute('data-scroll-speed'),
                direction: el.getAttribute('data-scroll-direction'),
                delay: el.getAttribute('data-scroll-delay'),
                position: el.getAttribute('data-scroll-position'),
                class: el.getAttribute('data-scroll-class'),
                repeat: el.getAttribute('data-scroll-repeat')
            };

            // Filter out null values
            Object.keys(scrollData).forEach(key => {
                if (scrollData[key] === null) delete scrollData[key];
            });

            if (Object.keys(scrollData).length > 1) {
                result.parallaxElements.push(scrollData);
            }
        });
    }

    // ==========================================================================
    // CSS SMOOTH SCROLL
    // ==========================================================================

    const html = document.documentElement;
    const htmlStyle = getComputedStyle(html);
    result.scrollBehavior.smooth = htmlStyle.scrollBehavior === 'smooth';

    // ==========================================================================
    // CSS KEYFRAMES EXTRACTION
    // ==========================================================================

    Array.from(document.styleSheets).forEach(sheet => {
        try {
            Array.from(sheet.cssRules || []).forEach(rule => {
                if (rule instanceof CSSKeyframesRule) {
                    const keyframes = [];
                    Array.from(rule.cssRules).forEach(kf => {
                        keyframes.push({
                            keyText: kf.keyText,
                            style: kf.style.cssText
                        });
                    });
                    result.cssAnimations.keyframes.push({
                        name: rule.name,
                        frames: keyframes
                    });
                }
            });
        } catch (e) {
            // CORS blocked
        }
    });

    // ==========================================================================
    // TIMING CONSTANTS EXTRACTION
    // ==========================================================================

    const easingSet = new Set();
    const durationSet = new Set();
    const delaySet = new Set();

    document.querySelectorAll('*').forEach(el => {
        const s = getComputedStyle(el);

        // Collect transitions
        if (s.transition && s.transition !== 'all 0s ease 0s' && s.transition !== 'none') {
            result.cssAnimations.transitions.push({
                selector: getSelector(el),
                transition: s.transition
            });

            // Parse transition timing
            if (s.transitionTimingFunction && s.transitionTimingFunction !== 'ease') {
                easingSet.add(s.transitionTimingFunction);
            }
            if (s.transitionDuration && s.transitionDuration !== '0s') {
                durationSet.add(s.transitionDuration);
            }
            if (s.transitionDelay && s.transitionDelay !== '0s') {
                delaySet.add(s.transitionDelay);
            }
        }

        // Collect animations
        if (s.animation && s.animation !== 'none') {
            result.animatedElements.push({
                selector: getSelector(el),
                animation: s.animation,
                animationName: s.animationName,
                animationDuration: s.animationDuration,
                animationTimingFunction: s.animationTimingFunction,
                animationDelay: s.animationDelay,
                animationIterationCount: s.animationIterationCount,
                animationDirection: s.animationDirection,
                animationFillMode: s.animationFillMode
            });

            if (s.animationTimingFunction && s.animationTimingFunction !== 'ease') {
                easingSet.add(s.animationTimingFunction);
            }
            if (s.animationDuration && s.animationDuration !== '0s') {
                durationSet.add(s.animationDuration);
            }
        }
    });

    result.timingConstants.easings = [...easingSet];
    result.timingConstants.durations = [...durationSet].sort((a, b) => parseFloat(a) - parseFloat(b));
    result.timingConstants.delays = [...delaySet].sort((a, b) => parseFloat(a) - parseFloat(b));

    // Identify premium easing (cubic-bezier patterns)
    const premiumEasings = result.timingConstants.easings.filter(e =>
        e.includes('cubic-bezier')
    );
    if (premiumEasings.length > 0) {
        // Pick the most common or first one
        result.timingConstants.premiumEasing = premiumEasings[0];
    }

    // ==========================================================================
    // HOVER TRANSITIONS
    // ==========================================================================

    // Note: This captures computed styles, not actual hover states
    // Real hover capture requires the capture_hover_matrix.js script
    document.querySelectorAll('button, a, [class*="card"], [class*="btn"]').forEach(el => {
        const s = getComputedStyle(el);
        if (s.transition && s.transition !== 'all 0s ease 0s' && s.transition !== 'none') {
            result.hoverTransitions.push({
                selector: getSelector(el),
                transition: s.transition,
                cursor: s.cursor,
                willChange: s.willChange !== 'auto' ? s.willChange : null
            });
        }
    });

    // ==========================================================================
    // SCROLL REVEAL DETECTION (Visual Clues)
    // ==========================================================================

    // Look for elements that might be scroll-triggered
    const scrollClues = document.querySelectorAll(
        '[class*="reveal"], [class*="animate-"], [class*="fade-"], [class*="slide-"], ' +
        '[class*="scroll-"], [class*="appear"], [class*="in-view"], [style*="opacity: 0"]'
    );

    scrollClues.forEach(el => {
        const s = getComputedStyle(el);
        if (s.opacity === '0' || s.transform !== 'none') {
            result.scrollRevealElements.push({
                selector: getSelector(el),
                opacity: s.opacity,
                transform: s.transform,
                willChange: s.willChange,
                className: el.className && typeof el.className === 'string' ?
                           el.className.split(' ').slice(0, 3).join(' ') : ''
            });
        }
    });

    // ==========================================================================
    // PARALLAX DETECTION
    // ==========================================================================

    // Look for elements with parallax-style classes or inline transforms
    document.querySelectorAll(
        '[class*="parallax"], [class*="Parallax"], [style*="translateY"], [style*="translate3d"]'
    ).forEach(el => {
        const s = getComputedStyle(el);
        result.parallaxElements.push({
            selector: getSelector(el),
            transform: s.transform,
            willChange: s.willChange,
            position: s.position
        });
    });

    // ==========================================================================
    // STAGGER DETECTION
    // ==========================================================================

    // Look for sibling elements with similar delays (indicates stagger)
    const potentialStaggerGroups = document.querySelectorAll(
        '[class*="stagger"], ul, .grid, [class*="card"]'
    );

    potentialStaggerGroups.forEach(container => {
        const children = container.children;
        if (children.length < 2) return;

        const delays = [];
        Array.from(children).slice(0, 5).forEach((child, i) => {
            const s = getComputedStyle(child);
            if (s.transitionDelay && s.transitionDelay !== '0s') {
                delays.push(parseFloat(s.transitionDelay));
            }
            if (s.animationDelay && s.animationDelay !== '0s') {
                delays.push(parseFloat(s.animationDelay));
            }
        });

        // Check if delays form a stagger pattern
        if (delays.length >= 2) {
            const diffs = [];
            for (let i = 1; i < delays.length; i++) {
                diffs.push(delays[i] - delays[i - 1]);
            }
            const avgDiff = diffs.reduce((a, b) => a + b, 0) / diffs.length;
            if (avgDiff > 0 && avgDiff < 1) {
                result.timingConstants.staggers.push({
                    container: getSelector(container),
                    staggerValue: avgDiff.toFixed(3) + 's',
                    childCount: children.length
                });
            }
        }
    });

    // ==========================================================================
    // SUMMARY
    // ==========================================================================

    result.summary = {
        animationLibrary: result.library.detected || 'css-only',
        hasScrollTrigger: result.library.scrollTrigger,
        scrollBehavior: result.scrollBehavior.lenis ? 'lenis' :
                        result.scrollBehavior.locomotive ? 'locomotive' :
                        result.scrollBehavior.smooth ? 'css-smooth' : 'native',
        keyframeCount: result.cssAnimations.keyframes.length,
        transitionCount: result.cssAnimations.transitions.length,
        scrollTriggerCount: result.gsapConfig.scrollTriggers.length,
        animatedElementCount: result.animatedElements.length,
        scrollRevealCount: result.scrollRevealElements.length,
        parallaxCount: result.parallaxElements.length,
        premiumEasing: result.timingConstants.premiumEasing,
        commonDurations: result.timingConstants.durations.slice(0, 5),
        hasStaggerAnimations: result.timingConstants.staggers.length > 0
    };

    // Limit output size
    if (result.cssAnimations.transitions.length > 20) {
        result.cssAnimations.transitions = result.cssAnimations.transitions.slice(0, 20);
    }
    if (result.animatedElements.length > 20) {
        result.animatedElements = result.animatedElements.slice(0, 20);
    }
    if (result.hoverTransitions.length > 20) {
        result.hoverTransitions = result.hoverTransitions.slice(0, 20);
    }

    return result;
})();
