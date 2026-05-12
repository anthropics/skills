/**
 * JS Bundle Animation Forensics Script
 *
 * Extracts animation configs from ES-module-bundled GSAP sites where
 * window.gsap / ScrollTrigger.getAll() are unavailable (~70% of modern builds).
 *
 * Scans all <script src="..."> bundles via fetch(), regex-extracts animation
 * configs from minified code, and outputs the shared Animation Spec Format.
 *
 * Usage: Run via Chrome DevTools `evaluate_script`
 * Returns: JSON string with complete animation spec
 */
(async function () {
    const result = {
        libraries: { gsap: false, lenis: false, barba: false, splitText: false },
        scrollTriggers: [],
        textAnimations: [],
        parallax: [],
        clipPathReveals: [],
        easings: [],
        staggers: [],
        tweenSignatures: [],
        smoothScroll: null,
        pageTransitions: null,
        easingSignature: null,
        bundleAnalysis: {
            bundlesScanned: 0,
            totalSize: 0,
            matchesFound: 0,
            errors: []
        }
    };

    // Collect all script[src] URLs
    const scriptEls = Array.from(document.querySelectorAll('script[src]'));
    const scriptUrls = scriptEls.map(s => s.src).filter(Boolean);

    for (const url of scriptUrls) {
        try {
            const resp = await fetch(url, { credentials: 'same-origin' });
            if (!resp.ok) continue;
            const code = await resp.text();

            // Skip tiny scripts (< 1KB unlikely to contain animation logic)
            if (code.length < 1000) continue;

            result.bundleAnalysis.bundlesScanned++;
            result.bundleAnalysis.totalSize += code.length;

            // ─── Library Detection (by import/require patterns) ─────────
            if (/from\s*["']\.?\.?\/?gsap|require\(["']gsap/i.test(code)) {
                result.libraries.gsap = true;
            }
            if (/from\s*["']\.?\.?\/?lenis|from\s*["']@studio-freight\/lenis|require\(["']lenis/i.test(code)) {
                result.libraries.lenis = true;
            }
            if (/from\s*["']@barba|from\s*["']\.?\.?\/?barba|require\(["']@barba/i.test(code)) {
                result.libraries.barba = true;
            }
            if (/SplitText/i.test(code) && /\.create\s*\(|new\s+\w+\s*\(/i.test(code)) {
                result.libraries.splitText = true;
            }

            // ─── ScrollTrigger Config Extraction ────────────────────────
            // Property names survive minification — scrollTrigger:{...} is intact
            const stRegex = /scrollTrigger\s*:\s*\{([^}]{10,500})\}/gi;
            let stMatch;
            while ((stMatch = stRegex.exec(code)) !== null) {
                const block = stMatch[1];
                const config = {};

                const triggerMatch = block.match(/trigger\s*:\s*["']([^"']+)["']/);
                if (triggerMatch) config.trigger = triggerMatch[1];

                const startMatch = block.match(/start\s*:\s*["']([^"']+)["']/);
                if (startMatch) config.start = startMatch[1];

                const endMatch = block.match(/end\s*:\s*["']([^"']+)["']/);
                if (endMatch) config.end = endMatch[1];

                const scrubMatch = block.match(/scrub\s*:\s*(true|false|[\d.]+)/);
                if (scrubMatch) config.scrub = scrubMatch[1] === 'true' ? true :
                                               scrubMatch[1] === 'false' ? false :
                                               parseFloat(scrubMatch[1]);

                const pinMatch = block.match(/pin\s*:\s*(true|false|["'][^"']+["'])/);
                if (pinMatch) config.pin = pinMatch[1] === 'true' ? true :
                                           pinMatch[1] === 'false' ? false :
                                           pinMatch[1].replace(/["']/g, '');

                const toggleMatch = block.match(/toggleActions\s*:\s*["']([^"']+)["']/);
                if (toggleMatch) config.toggleActions = toggleMatch[1];

                if (Object.keys(config).length > 0) {
                    result.scrollTriggers.push(config);
                    result.bundleAnalysis.matchesFound++;
                }
            }

            // ─── SplitText Extraction ───────────────────────────────────
            // SplitText.create("selector", {type:"words,chars", mask:"words"})
            const splitRegex = /(?:SplitText\.create|new\s+\w+)\s*\(\s*["']([^"']+)["']\s*,\s*\{([^}]{5,300})\}/gi;
            let splitMatch;
            while ((splitMatch = splitRegex.exec(code)) !== null) {
                const selector = splitMatch[1];
                const block = splitMatch[2];
                const config = { selector };

                const typeMatch = block.match(/type\s*:\s*["']([^"']+)["']/);
                if (typeMatch) config.splitType = typeMatch[1];

                const maskMatch = block.match(/mask\s*:\s*["']([^"']+)["']/);
                if (maskMatch) config.mask = maskMatch[1];

                const linesClassMatch = block.match(/linesClass\s*:\s*["']([^"']+)["']/);
                if (linesClassMatch) config.linesClass = linesClassMatch[1];

                if (config.splitType) {
                    result.textAnimations.push(config);
                    result.bundleAnalysis.matchesFound++;
                }
            }

            // ─── Easing Extraction ──────────────────────────────────────
            const easeRegex = /ease\s*:\s*["']([^"']{3,50})["']/gi;
            let easeMatch;
            const easingSet = new Set(result.easings);
            while ((easeMatch = easeRegex.exec(code)) !== null) {
                easingSet.add(easeMatch[1]);
            }
            result.easings = [...easingSet];

            // ─── Stagger Extraction ─────────────────────────────────────
            // stagger:{amount:0.5} | stagger:{each:0.1} | stagger:0.1
            const staggerRegex = /stagger\s*:\s*(?:\{([^}]{3,100})\}|([\d.]+))/gi;
            let staggerMatch;
            while ((staggerMatch = staggerRegex.exec(code)) !== null) {
                if (staggerMatch[2]) {
                    result.staggers.push({ each: parseFloat(staggerMatch[2]) });
                } else if (staggerMatch[1]) {
                    const block = staggerMatch[1];
                    const config = {};
                    const amountMatch = block.match(/amount\s*:\s*([\d.]+)/);
                    if (amountMatch) config.amount = parseFloat(amountMatch[1]);
                    const eachMatch = block.match(/each\s*:\s*([\d.]+)/);
                    if (eachMatch) config.each = parseFloat(eachMatch[1]);
                    const fromMatch = block.match(/from\s*:\s*["']([^"']+)["']/);
                    if (fromMatch) config.from = fromMatch[1];
                    if (Object.keys(config).length > 0) {
                        result.staggers.push(config);
                        result.bundleAnalysis.matchesFound++;
                    }
                }
            }

            // ─── clipPath Animation Extraction ──────────────────────────
            const clipRegex = /clipPath\s*:\s*["'](inset\([^"']+\))["']/gi;
            let clipMatch;
            while ((clipMatch = clipRegex.exec(code)) !== null) {
                result.clipPathReveals.push({ value: clipMatch[1] });
                result.bundleAnalysis.matchesFound++;
            }

            // ─── Tween Signature Extraction ─────────────────────────────
            // .fromTo("selector", ...) | .from("selector", ...) | .to("selector", ...)
            const tweenRegex = /\.(fromTo|from|to)\s*\(\s*["']([^"']+)["']/gi;
            let tweenMatch;
            while ((tweenMatch = tweenRegex.exec(code)) !== null) {
                result.tweenSignatures.push({
                    method: tweenMatch[1],
                    target: tweenMatch[2]
                });
            }

            // ─── Lenis Config Extraction ────────────────────────────────
            if (result.libraries.lenis && !result.smoothScroll) {
                const lerpMatch = code.match(/lerp\s*:\s*(0?\.[\d]+)/);
                const smoothWheelMatch = code.match(/smoothWheel\s*:\s*(true|false)/);
                result.smoothScroll = {
                    library: 'lenis',
                    lerp: lerpMatch ? parseFloat(lerpMatch[1]) : null,
                    smoothWheel: smoothWheelMatch ? smoothWheelMatch[1] === 'true' : null
                };
            }

            // ─── Barba Transition Mode ──────────────────────────────────
            if (result.libraries.barba && !result.pageTransitions) {
                const modeMatch = code.match(/mode\s*:\s*["'](sync|in-out|out-in)["']/);
                result.pageTransitions = {
                    library: 'barba',
                    mode: modeMatch ? modeMatch[1] : null
                };
            }

        } catch (err) {
            result.bundleAnalysis.errors.push({
                url: url.substring(0, 120),
                error: err.message
            });
        }
    }

    // ─── Post-processing ────────────────────────────────────────────────

    // Deduplicate easings
    result.easings = [...new Set(result.easings)];

    // Cap tween signatures to prevent output bloat
    result.tweenSignatures = result.tweenSignatures.slice(0, 30);

    // Determine easing signature (most prominent easing)
    if (result.easings.length > 0) {
        result.easingSignature = result.easings[0];
    }

    // Deduplicate ScrollTriggers by trigger selector
    const seenTriggers = new Set();
    result.scrollTriggers = result.scrollTriggers.filter(st => {
        const key = st.trigger || JSON.stringify(st);
        if (seenTriggers.has(key)) return false;
        seenTriggers.add(key);
        return true;
    });

    // Deduplicate staggers
    const seenStaggers = new Set();
    result.staggers = result.staggers.filter(s => {
        const key = JSON.stringify(s);
        if (seenStaggers.has(key)) return false;
        seenStaggers.add(key);
        return true;
    });

    return JSON.stringify(result, null, 2);
})();
