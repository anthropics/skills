/**
 * HTML Content Extraction Script (v4.0)
 *
 * Extracts actual rendered content from each page section: headings with exact
 * markup (<br>, <span>), nav links, logo/partner images, CTA buttons, footer
 * link groups, and product/feature card content.
 *
 * This ensures Gemini reproduces exact text, line breaks, image sources, and
 * link structure — not guessed approximations from screenshots.
 *
 * Usage: Inject via mcp__claude-in-chrome__javascript_tool
 * Returns: JSON object with per-section content data
 */
(function() {
    const result = {
        navigation: {
            logo: null,
            links: [],
            ctas: []
        },
        hero: {
            headings: [],
            subheadings: [],
            ctas: [],
            description: null
        },
        logoBar: {
            images: [],
            sectionLabel: null
        },
        sections: [],
        footer: {
            columns: [],
            bottomBar: {
                links: [],
                copyright: null
            }
        },
        metadata: {
            title: document.title,
            description: null,
            extractedAt: new Date().toISOString()
        }
    };

    // Helper: get clean innerHTML preserving <br>, <span>, <em>, <strong>
    function getCleanInnerHTML(el) {
        if (!el) return null;
        // Clone to avoid modifying the DOM
        const clone = el.cloneNode(true);
        // Remove script/style tags
        clone.querySelectorAll('script, style').forEach(s => s.remove());
        return clone.innerHTML.trim();
    }

    // Helper: extract link data
    function extractLink(a) {
        return {
            text: a.textContent.trim(),
            href: a.getAttribute('href'),
            innerHTML: getCleanInnerHTML(a)
        };
    }

    // Helper: extract image data
    function extractImage(img) {
        return {
            src: img.getAttribute('src') || img.dataset.src || null,
            srcset: img.getAttribute('srcset') || null,
            alt: img.getAttribute('alt') || '',
            width: img.naturalWidth || img.width || null,
            height: img.naturalHeight || img.height || null
        };
    }

    // ==========================================================================
    // META DESCRIPTION
    // ==========================================================================
    const metaDesc = document.querySelector('meta[name="description"]');
    if (metaDesc) result.metadata.description = metaDesc.getAttribute('content');

    // ==========================================================================
    // NAVIGATION (header/nav)
    // ==========================================================================
    const header = document.querySelector('header') || document.querySelector('nav');
    if (header) {
        // Logo
        const logoImg = header.querySelector('img[class*="logo"], a[class*="logo"] img, a[href="/"] img, [class*="logo"] svg');
        if (logoImg) {
            if (logoImg.tagName === 'IMG') {
                result.navigation.logo = extractImage(logoImg);
            } else if (logoImg.tagName === 'svg') {
                result.navigation.logo = { svg: logoImg.outerHTML.substring(0, 3000), type: 'svg' };
            }
        }
        // Also check for SVG logo directly
        if (!result.navigation.logo) {
            const svgLogo = header.querySelector('a[href="/"] svg, [class*="logo"] svg');
            if (svgLogo) {
                result.navigation.logo = { svg: svgLogo.outerHTML.substring(0, 3000), type: 'svg' };
            }
        }

        // Nav links (exclude CTAs)
        const navLinks = header.querySelectorAll('nav a, [role="navigation"] a');
        navLinks.forEach(a => {
            const text = a.textContent.trim();
            if (text && text.length < 50) {
                result.navigation.links.push(extractLink(a));
            }
        });

        // CTA buttons in header
        const headerCtas = header.querySelectorAll('a[class*="btn"], a[class*="button"], a[class*="cta"], button');
        headerCtas.forEach(cta => {
            const text = cta.textContent.trim();
            if (text && text.length < 50) {
                result.navigation.ctas.push({
                    text: text,
                    href: cta.getAttribute('href') || null,
                    innerHTML: getCleanInnerHTML(cta),
                    tagName: cta.tagName.toLowerCase()
                });
            }
        });
    }

    // ==========================================================================
    // HERO SECTION
    // ==========================================================================
    // Find hero: first section/div after header, or element with hero-related class
    const heroSelectors = [
        '[class*="hero"]',
        'main > section:first-child',
        'main > div:first-child',
        '#hero',
        'section:first-of-type'
    ];

    let heroEl = null;
    for (const sel of heroSelectors) {
        heroEl = document.querySelector(sel);
        if (heroEl && heroEl.querySelector('h1')) break;
    }

    // Fallback: find the h1 and use its parent section
    if (!heroEl || !heroEl.querySelector('h1')) {
        const h1 = document.querySelector('h1');
        if (h1) {
            heroEl = h1.closest('section') || h1.parentElement;
        }
    }

    if (heroEl) {
        // All headings in hero
        heroEl.querySelectorAll('h1, h2').forEach(h => {
            result.hero.headings.push({
                tag: h.tagName.toLowerCase(),
                text: h.textContent.trim(),
                innerHTML: getCleanInnerHTML(h),
                className: h.className || null
            });
        });

        // Subheadings / descriptions
        heroEl.querySelectorAll('p').forEach(p => {
            const text = p.textContent.trim();
            if (text && text.length > 5) {
                result.hero.subheadings.push({
                    text: text,
                    innerHTML: getCleanInnerHTML(p),
                    className: p.className || null
                });
            }
        });

        // CTAs in hero
        heroEl.querySelectorAll('a[class*="btn"], a[class*="button"], a[class*="cta"], button').forEach(cta => {
            const text = cta.textContent.trim();
            if (text) {
                result.hero.ctas.push({
                    text: text,
                    href: cta.getAttribute('href') || null,
                    innerHTML: getCleanInnerHTML(cta),
                    className: cta.className || null
                });
            }
        });
    }

    // ==========================================================================
    // LOGO / PARTNER BAR
    // ==========================================================================
    // Look for a section with many small images (logos)
    const allSections = document.querySelectorAll('section, [class*="logo"], [class*="partner"], [class*="client"], [class*="brand"], [class*="trusted"]');
    for (const section of allSections) {
        const imgs = section.querySelectorAll('img');
        // A logo bar typically has 4+ small images in a row
        if (imgs.length >= 4) {
            let allSmall = true;
            imgs.forEach(img => {
                const rect = img.getBoundingClientRect();
                if (rect.height > 80) allSmall = false;
            });
            if (allSmall) {
                // This is likely the logo bar
                const label = section.querySelector('p, span, h2, h3, h4');
                if (label) result.logoBar.sectionLabel = label.textContent.trim();

                imgs.forEach(img => {
                    result.logoBar.images.push(extractImage(img));
                });
                break; // Found the logo bar, stop searching
            }
        }
    }

    // ==========================================================================
    // CONTENT SECTIONS (everything between hero and footer)
    // ==========================================================================
    const main = document.querySelector('main') || document.body;
    const contentSections = main.querySelectorAll('section');

    contentSections.forEach((section, index) => {
        // Skip if it's likely the hero (first section with h1)
        if (index === 0 && section.querySelector('h1')) return;
        // Skip if it's the logo bar we already captured
        if (result.logoBar.images.length > 0 && section.querySelectorAll('img').length >= 4) {
            let isLogoBar = true;
            section.querySelectorAll('img').forEach(img => {
                if (img.getBoundingClientRect().height > 80) isLogoBar = false;
            });
            if (isLogoBar) return;
        }

        const sectionData = {
            index: index,
            id: section.id || null,
            className: (section.className || '').substring(0, 200),
            headings: [],
            paragraphs: [],
            images: [],
            links: [],
            cards: []
        };

        // Headings
        section.querySelectorAll('h1, h2, h3, h4').forEach(h => {
            sectionData.headings.push({
                tag: h.tagName.toLowerCase(),
                text: h.textContent.trim(),
                innerHTML: getCleanInnerHTML(h)
            });
        });

        // Paragraphs (first 5 to avoid noise)
        const paras = section.querySelectorAll('p');
        for (let i = 0; i < Math.min(paras.length, 5); i++) {
            const text = paras[i].textContent.trim();
            if (text && text.length > 10) {
                sectionData.paragraphs.push({
                    text: text,
                    innerHTML: getCleanInnerHTML(paras[i])
                });
            }
        }

        // Images
        section.querySelectorAll('img').forEach(img => {
            const rect = img.getBoundingClientRect();
            if (rect.width > 50 && rect.height > 50) { // Skip tiny decorative images
                sectionData.images.push(extractImage(img));
            }
        });

        // Links / CTAs
        section.querySelectorAll('a').forEach(a => {
            const text = a.textContent.trim();
            if (text && text.length > 0 && text.length < 80) {
                sectionData.links.push(extractLink(a));
            }
        });

        // Card-like elements (repeated sibling structures)
        const cardSelectors = '[class*="card"], [class*="item"], [class*="feature"], [class*="product"]';
        const cards = section.querySelectorAll(cardSelectors);
        if (cards.length >= 2) {
            cards.forEach((card, cardIndex) => {
                if (cardIndex >= 8) return; // Limit to 8 cards
                const cardData = {
                    heading: null,
                    description: null,
                    image: null,
                    link: null
                };
                const cardH = card.querySelector('h2, h3, h4, p:first-child');
                if (cardH) cardData.heading = cardH.textContent.trim();
                const cardP = card.querySelector('p:not(:first-child), p + p');
                if (cardP) cardData.description = cardP.textContent.trim();
                const cardImg = card.querySelector('img');
                if (cardImg) cardData.image = extractImage(cardImg);
                const cardA = card.querySelector('a');
                if (cardA) cardData.link = extractLink(cardA);
                sectionData.cards.push(cardData);
            });
        }

        // Only add sections that have meaningful content
        if (sectionData.headings.length > 0 || sectionData.images.length > 0 || sectionData.cards.length > 0) {
            result.sections.push(sectionData);
        }
    });

    // ==========================================================================
    // FOOTER
    // ==========================================================================
    const footer = document.querySelector('footer');
    if (footer) {
        // Footer columns: look for nav groups or div groups with links
        const footerNavs = footer.querySelectorAll('nav, [class*="col"], [class*="group"]');
        if (footerNavs.length > 0) {
            footerNavs.forEach(nav => {
                const heading = nav.querySelector('h3, h4, h5, p:first-child, span:first-child, strong');
                const links = [];
                nav.querySelectorAll('a').forEach(a => {
                    const text = a.textContent.trim();
                    if (text) links.push(extractLink(a));
                });
                if (links.length > 0 || heading) {
                    result.footer.columns.push({
                        heading: heading ? heading.textContent.trim() : null,
                        headingHTML: heading ? getCleanInnerHTML(heading) : null,
                        links: links
                    });
                }
            });
        }

        // Fallback: if no column groups found, gather all footer links
        if (result.footer.columns.length === 0) {
            const allFooterLinks = [];
            footer.querySelectorAll('a').forEach(a => {
                const text = a.textContent.trim();
                if (text) allFooterLinks.push(extractLink(a));
            });
            if (allFooterLinks.length > 0) {
                result.footer.columns.push({ heading: null, links: allFooterLinks });
            }
        }

        // Copyright
        const copyrightEl = footer.querySelector('[class*="copyright"], [class*="legal"], small');
        if (copyrightEl) {
            result.footer.bottomBar.copyright = copyrightEl.textContent.trim();
        }

        // Bottom bar links (privacy, terms, etc.)
        const bottomBar = footer.querySelector('[class*="bottom"], [class*="legal"], [class*="copyright"]');
        if (bottomBar) {
            bottomBar.querySelectorAll('a').forEach(a => {
                result.footer.bottomBar.links.push(extractLink(a));
            });
        }
    }

    // ==========================================================================
    // SUMMARY
    // ==========================================================================
    result.summary = {
        hasNavigation: result.navigation.links.length > 0,
        navLinkCount: result.navigation.links.length,
        hasHero: result.hero.headings.length > 0,
        heroHeadingHTML: result.hero.headings[0] ? result.hero.headings[0].innerHTML : null,
        logoCount: result.logoBar.images.length,
        sectionCount: result.sections.length,
        footerColumnCount: result.footer.columns.length,
        totalImages: result.logoBar.images.length + result.sections.reduce((sum, s) => sum + s.images.length, 0)
    };

    return result;
})();
