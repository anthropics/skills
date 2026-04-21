import { test, expect } from '@playwright/test';

test.describe('Skills Documentation Examples', () => {
    test('can navigate to skill README files', async ({ page }) => {
        // Example: Testing that skill documentation is properly formatted
        const skillPath = 'file://' + process.cwd() + '/skills/algorithmic-art/SKILL.md';

        // In a real scenario with a served docs site:
        // await page.goto('http://localhost:3000/skills/algorithmic-art');
        // await page.wait_for_load_state('networkidle');

        // Verify the file can be accessed
        await page.goto(skillPath);
        const content = await page.content();
        expect(content).toContain('SKILL');
    });

    test('skill template includes required fields', async ({ page }) => {
        // Example pattern for validating skill structure
        const templatePath = 'file://' + process.cwd() + '/template/SKILL.md';

        await page.goto(templatePath);
        const content = await page.content();

        // Verify required sections exist
        expect(content).toContain('name:');
        expect(content).toContain('description:');
    });
});

test.describe('Web Artifacts Testing', () => {
    test('example: test HTML file directly', async ({ page }) => {
        // Pattern for testing static HTML in web-artifacts-builder
        // 
        // const htmlPath = 'file://' + process.cwd() + '/skills/web-artifacts-builder/examples/demo.html';
        // await page.goto(htmlPath);
        // 
        // // Test that HTML renders correctly
        // const body = await page.locator('body');
        // expect(body).toBeTruthy();
    });

    test('example: test with dev server', async ({ page }) => {
        // Pattern when testing a local dev server
        // First, ensure server is running via:
        //   npm run dev
        // Or use the with_server.py helper

        // await page.goto('http://localhost:3000');
        // await page.wait_for_load_state('networkidle');
        // 
        // // Verify page loaded
        // const title = await page.title();
        // expect(title).toBeTruthy();
    });
});

test.describe('Multi-browser Testing', () => {
    test('verify responsive behavior', async ({ page, context, viewport }) => {
        // Example: Test different viewport sizes
        // This runs on all configured browsers and viewports

        // await page.goto('http://localhost:3000');
        // await page.wait_for_load_state('networkidle');
        // 
        // // Verify layout adapts to viewport
        // const body = page.locator('body');
        // const boundingBox = await body.boundingBox();
        // expect(boundingBox?.width).toBeLessThanOrEqual(viewport?.width || 1280);
    });

    test('test on mobile viewport', async ({ page, isMobile }) => {
        // This test only runs on mobile configurations
        if (!isMobile) {
            test.skip();
        }

        // await page.goto('http://localhost:3000');
        // // Verify mobile-specific behavior
    });
});

test.describe('Console & Network Inspection', () => {
    test('capture browser console messages', async ({ page }) => {
        // Pattern for debugging by capturing console output
        const consoleLogs: string[] = [];

        page.on('console', msg => {
            consoleLogs.push(msg.text());
        });

        // await page.goto('http://localhost:3000');
        // // Perform actions that trigger console messages
        // expect(consoleLogs.length).toBeGreaterThanOrEqual(0);
    });

    test('verify network requests', async ({ page }) => {
        // Pattern for verifying API calls
        const requests: string[] = [];

        page.on('request', request => {
            requests.push(request.url());
        });

        // await page.goto('http://localhost:3000');
        // await page.wait_for_load_state('networkidle');
        // // Verify expected requests were made
    });
});
