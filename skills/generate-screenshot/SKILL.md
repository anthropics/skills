---
name: generate-screenshot
description: >
  Generate screenshots of a web app using Playwright. Captures desktop, tablet, and mobile
  viewports in both light and dark mode. Auto-detects running dev servers, supports multiple
  routes, and saves organised screenshots. Use when the user asks to generate screenshots,
  capture screenshots, or invokes /generate-screenshot.
license: Complete terms in LICENSE.txt
allowed-tools: Bash, Read, Glob, Grep, Write, Edit, AskUserQuestion
argument-hint: "[route1] [route2] [...] [--output dir] [--url http://...] [--viewports desktop,mobile,tablet] [--modes light,dark]"
---

# Generate Screenshot Skill

Generate screenshots of a running web app across multiple viewports and colour modes using Playwright.

## Workflow

Follow these steps **in order**. Do not skip steps.

### Step 1: Ensure Playwright is installed

```bash
cd $SKILL_DIR && node -e "try { require('playwright'); console.log('OK'); } catch(e) { console.log('MISSING'); }" 2>/dev/null
```

If `MISSING`, run:

```bash
cd $SKILL_DIR && npm install
```

Then ensure the Chromium browser is available:

```bash
cd $SKILL_DIR && npx playwright install chromium 2>&1 | tail -5
```

### Step 2: Detect the dev server

Auto-detect a running dev server on common ports:

```bash
cd $SKILL_DIR && node -e "require('./lib/helpers').detectDevServers().then(s => console.log(JSON.stringify(s, null, 2)))"
```

**Common ports checked:** 3000, 3001, 3002, 4200, 5000, 5173, 5174, 8000, 8080, 8888, 9000, 1234

- If **one server** is found, use it as the base URL.
- If **multiple servers** are found, ask the user which one to use.
- If **no server** is found, ask the user for the URL using `AskUserQuestion`.

The user may also provide a URL explicitly via `--url`. That takes priority.

### Step 3: Determine routes to capture

Check if the user provided routes as arguments (e.g. `/generate-screenshot /login /dashboard /settings`).

- If routes **were provided**, use them.
- If routes **were NOT provided**, attempt to scan the project for route definitions:
  1. Search for route files in common framework patterns:
     - **Next.js (App Router):** `Glob` for `app/**/page.{tsx,jsx,ts,js}` — convert file paths to routes
     - **Next.js (Pages Router):** `Glob` for `pages/**/*.{tsx,jsx,ts,js}` — convert file paths to routes
     - **React Router:** `Grep` for `path=` or `<Route` in `*.{tsx,jsx,ts,js}` files
     - **Vue Router:** `Grep` for `path:` in files matching `*router*` or `*routes*`
     - **Nuxt:** `Glob` for `pages/**/*.vue` — convert file paths to routes
     - **SvelteKit:** `Glob` for `src/routes/**/+page.svelte` — convert file paths to routes
     - **Angular:** `Grep` for `path:` in files matching `*routing*` or `*routes*`
     - **Remix:** `Glob` for `app/routes/**/*.{tsx,jsx,ts,js}` — convert file paths to routes
  2. Present the discovered routes to the user and ask them to confirm or modify the list.
  3. If no routes are found, ask the user to provide them manually.

**Always include `/` (home) unless the user explicitly excludes it.**

### Step 4: Determine viewports and colour modes

**Defaults** (used when user provides no overrides):

| Viewport | Width | Height |
|----------|-------|--------|
| Desktop  | 1920  | 1080   |
| Tablet   | 768   | 1024   |
| Mobile   | 375   | 812    |

| Mode  | `prefers-color-scheme` |
|-------|------------------------|
| Light | `light`                |
| Dark  | `dark`                 |

The user can override via:
- `--viewports desktop` — only desktop
- `--viewports mobile,tablet` — mobile and tablet only
- `--modes light` — light mode only

### Step 5: Determine output directory

- Default: `screenshots/` in the project root (current working directory, NOT $SKILL_DIR).
- User can override with `--output path/to/dir`.
- Create the directory if it doesn't exist.

**File naming convention:**

```
{route}--{viewport}--{mode}.png
```

Examples:
- `home--desktop--light.png`
- `login--mobile--dark.png`
- `dashboard-settings--tablet--light.png`

Route naming: replace `/` with `-`, strip leading `-`, use `home` for `/`.

### Step 6: Generate and execute the Playwright script

Write a Playwright script to `/tmp/generate-screenshot-<timestamp>.js` and execute it using the skill's runner:

```bash
cd $SKILL_DIR && node run.js /tmp/generate-screenshot-<timestamp>.js
```

**The generated script MUST:**

1. Launch Chromium in **headless** mode (screenshots don't need visible browser).
2. For each colour mode (`light` / `dark`):
   a. Create a new browser context with `colorScheme` set accordingly.
   b. For each viewport (`desktop` / `tablet` / `mobile`):
      - Set the viewport size on the context.
      - For each route:
        - Navigate to `{baseUrl}{route}`.
        - Wait for network idle (`waitUntil: 'networkidle'`).
        - Wait an additional 500ms for animations to settle.
        - Take a **full-page** screenshot.
        - Save to the output directory with the naming convention above.
3. Close the browser.
4. Print a summary of all screenshots taken.

**Script template reference:**

```javascript
const { chromium } = require('playwright');
const path = require('path');
const fs = require('fs');

(async () => {
  const baseUrl = '{{BASE_URL}}';
  const outputDir = '{{OUTPUT_DIR}}';
  const routes = {{ROUTES_JSON}};

  const viewports = {
    desktop: { width: 1920, height: 1080 },
    tablet: { width: 768, height: 1024 },
    mobile: { width: 375, height: 812 },
  };
  const selectedViewports = {{VIEWPORTS_JSON}};
  const modes = {{MODES_JSON}};

  fs.mkdirSync(outputDir, { recursive: true });

  const browser = await chromium.launch({ headless: true });
  const screenshots = [];

  for (const mode of modes) {
    for (const [vpName, vpSize] of Object.entries(viewports)) {
      if (!selectedViewports.includes(vpName)) continue;

      const context = await browser.newContext({
        viewport: vpSize,
        colorScheme: mode,
      });
      const page = await context.newPage();

      for (const route of routes) {
        const url = `${baseUrl}${route}`;
        const routeName = route === '/' ? 'home' : route.replace(/^\//, '').replace(/\//g, '-');
        const fileName = `${routeName}--${vpName}--${mode}.png`;
        const filePath = path.resolve(outputDir, fileName);

        try {
          await page.goto(url, { waitUntil: 'networkidle', timeout: 30000 });
          await page.waitForTimeout(500);
          await page.screenshot({ path: filePath, fullPage: true });
          screenshots.push({ route, viewport: vpName, mode, file: fileName, status: 'ok' });
          console.log(`  ✓ ${fileName}`);
        } catch (err) {
          screenshots.push({ route, viewport: vpName, mode, file: fileName, status: 'failed', error: err.message });
          console.error(`  ✗ ${fileName} — ${err.message}`);
        }
      }

      await context.close();
    }
  }

  await browser.close();

  const ok = screenshots.filter(s => s.status === 'ok').length;
  const failed = screenshots.filter(s => s.status === 'failed').length;
  console.log(`\nDone: ${ok} captured, ${failed} failed, ${screenshots.length} total.`);
  console.log(`Screenshots saved to: ${path.resolve(outputDir)}`);
})();
```

### Step 7: Report results

After execution, present the user with:
1. A summary table of all screenshots (route, viewport, mode, status).
2. The output directory path.
3. Any failures with error messages.

## Important Notes

- **Never write scripts to `$SKILL_DIR`** — always use `/tmp/`.
- **Use absolute paths** for the output directory when passing to the script.
- **Handle authentication**: If the app requires login, ask the user for credentials or a pre-auth strategy before capturing.
- **Handle cookie banners**: If a cookie/consent banner appears, attempt to dismiss it before taking screenshots.
- **Respect the user's preferences**: If they specify a subset of viewports or modes, only capture those.
- **Error resilience**: If one route fails, continue with the remaining routes. Report all failures at the end.
