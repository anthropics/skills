const { chromium } = require('playwright');

/**
 * Scrape job listings from a careers page
 * Handles JavaScript-rendered pages (Ashby, Lever, Greenhouse, etc.)
 */
async function scrapeJobsPage(url) {
  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({
    userAgent: 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36'
  });
  const page = await context.newPage();

  console.error(`Scraping: ${url}`);

  try {
    await page.goto(url, {
      waitUntil: 'networkidle',
      timeout: 30000
    });

    // Wait a bit for dynamic content
    await page.waitForTimeout(2000);

    // Get the full page content
    const content = await page.content();

    // Try to extract job listings based on common patterns
    const jobs = await page.evaluate(() => {
      const results = [];

      // Ashby pattern
      document.querySelectorAll('[data-testid="job-posting"]').forEach(el => {
        const titleEl = el.querySelector('h3, [data-testid="job-posting-title"]');
        const linkEl = el.querySelector('a');
        const deptEl = el.querySelector('[data-testid="job-posting-department"]');
        if (titleEl) {
          results.push({
            title: titleEl.textContent.trim(),
            link: linkEl?.href || '',
            department: deptEl?.textContent.trim() || ''
          });
        }
      });

      // Lever pattern
      document.querySelectorAll('.posting').forEach(el => {
        const titleEl = el.querySelector('.posting-title h5');
        const linkEl = el.querySelector('a.posting-title');
        const deptEl = el.querySelector('.posting-categories .sort-by-team');
        if (titleEl) {
          results.push({
            title: titleEl.textContent.trim(),
            link: linkEl?.href || '',
            department: deptEl?.textContent.trim() || ''
          });
        }
      });

      // Greenhouse pattern
      document.querySelectorAll('.opening').forEach(el => {
        const titleEl = el.querySelector('a');
        const deptEl = el.querySelector('.department');
        if (titleEl) {
          results.push({
            title: titleEl.textContent.trim(),
            link: titleEl.href || '',
            department: deptEl?.textContent.trim() || ''
          });
        }
      });

      // Generic fallback - look for job-like links
      if (results.length === 0) {
        document.querySelectorAll('a').forEach(el => {
          const href = el.href || '';
          const text = el.textContent.trim();
          // Look for links that seem like job postings
          if (href.includes('/job') || href.includes('/position') ||
              href.includes('/careers/') || href.includes('/opening')) {
            if (text.length > 3 && text.length < 100) {
              results.push({
                title: text,
                link: href,
                department: ''
              });
            }
          }
        });
      }

      return results;
    });

    await browser.close();

    return {
      success: true,
      url,
      jobCount: jobs.length,
      jobs
    };

  } catch (error) {
    await browser.close();
    return {
      success: false,
      url,
      error: error.message,
      jobs: []
    };
  }
}

/**
 * Scrape a single job posting page for full description
 */
async function scrapeJobDescription(url) {
  const browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({
    userAgent: 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36'
  });
  const page = await context.newPage();

  try {
    await page.goto(url, {
      waitUntil: 'networkidle',
      timeout: 30000
    });

    await page.waitForTimeout(2000);

    // Extract text content, focusing on main content area
    const description = await page.evaluate(() => {
      // Remove scripts, styles, nav, footer
      const elementsToRemove = document.querySelectorAll('script, style, nav, footer, header');
      elementsToRemove.forEach(el => el.remove());

      // Try to find main content
      const mainContent = document.querySelector('main, [role="main"], .job-description, .posting-description, article');
      if (mainContent) {
        return mainContent.textContent.replace(/\s+/g, ' ').trim();
      }

      // Fallback to body
      return document.body.textContent.replace(/\s+/g, ' ').trim();
    });

    await browser.close();

    return {
      success: true,
      url,
      description
    };

  } catch (error) {
    await browser.close();
    return {
      success: false,
      url,
      error: error.message,
      description: ''
    };
  }
}

// CLI usage
const args = process.argv.slice(2);

if (args.length === 0) {
  console.log('Usage:');
  console.log('  node scrape.js <careers-url>              # Scrape job listings');
  console.log('  node scrape.js --description <job-url>    # Scrape single job description');
  process.exit(1);
}

if (args[0] === '--description') {
  scrapeJobDescription(args[1]).then(result => {
    console.log(JSON.stringify(result, null, 2));
  });
} else {
  scrapeJobsPage(args[0]).then(result => {
    console.log(JSON.stringify(result, null, 2));
  });
}
