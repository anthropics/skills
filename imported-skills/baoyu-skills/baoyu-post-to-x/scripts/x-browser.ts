import fs from 'node:fs';
import { mkdir } from 'node:fs/promises';
import process from 'node:process';
import {
  CHROME_CANDIDATES_FULL,
  CdpConnection,
  copyImageToClipboard,
  findExistingChromeDebugPort,
  getDefaultProfileDir,
  gracefulKillChrome,
  launchChrome,
  openPageSession,
  pasteFromClipboard,
  sleep,
  waitForXSessionPersistence,
  waitForChromeDebugPort,
} from './x-utils.js';

const X_COMPOSE_URL = 'https://x.com/compose/post';

interface XBrowserOptions {
  text?: string;
  images?: string[];
  submit?: boolean;
  timeoutMs?: number;
  profileDir?: string;
  chromePath?: string;
}

export async function postToX(options: XBrowserOptions): Promise<void> {
  const { text, images = [], submit = false, timeoutMs = 120_000, profileDir = getDefaultProfileDir() } = options;

  await mkdir(profileDir, { recursive: true });

  const existingPort = await findExistingChromeDebugPort(profileDir);
  const reusing = existingPort !== null;
  let port = existingPort ?? 0;
  let chrome: Awaited<ReturnType<typeof launchChrome>>['chrome'] | null = null;
  if (!reusing) {
    const launched = await launchChrome(X_COMPOSE_URL, profileDir, CHROME_CANDIDATES_FULL, options.chromePath);
    port = launched.port;
    chrome = launched.chrome;
  }

  if (reusing) console.log(`[x-browser] Reusing existing Chrome on port ${port}`);
  else console.log(`[x-browser] Launching Chrome (profile: ${profileDir})`);

  let cdp: CdpConnection | null = null;
  let sessionId: string | null = null;
  let loggedInDuringRun = false;

  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    cdp = await CdpConnection.connect(wsUrl, 30_000, { defaultTimeoutMs: 15_000 });

    const page = await openPageSession({
      cdp,
      reusing,
      url: X_COMPOSE_URL,
      matchTarget: (target) => target.type === 'page' && target.url.includes('x.com'),
      enablePage: true,
      enableRuntime: true,
      enableNetwork: true,
    });
    const activeSessionId = page.sessionId;
    sessionId = activeSessionId;
    await cdp.send('Input.setIgnoreInputEvents', { ignore: false }, { sessionId: activeSessionId });

    console.log('[x-browser] Waiting for X editor...');
    await sleep(3000);

    const waitForEditor = async (): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < timeoutMs) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `!!document.querySelector('[data-testid="tweetTextarea_0"]')`,
          returnByValue: true,
        }, { sessionId: activeSessionId });
        if (result.result.value) return true;
        await sleep(1000);
      }
      return false;
    };

    const editorFound = await waitForEditor();
    if (!editorFound) {
      console.log('[x-browser] Editor not found. Please log in to X in the browser window.');
      console.log('[x-browser] Waiting for login...');
      const loggedIn = await waitForEditor();
      if (!loggedIn) throw new Error('Timed out waiting for X editor. Please log in first.');
      loggedInDuringRun = true;
    }

    if (text) {
      console.log('[x-browser] Typing text...');
      await cdp.send('Runtime.evaluate', {
        expression: `
          const editor = document.querySelector('[data-testid="tweetTextarea_0"]');
          if (editor) {
            editor.focus();
            document.execCommand('insertText', false, ${JSON.stringify(text)});
          }
        `,
      }, { sessionId: activeSessionId });
      await sleep(500);
    }

    for (const imagePath of images) {
      if (!fs.existsSync(imagePath)) {
        console.warn(`[x-browser] Image not found: ${imagePath}`);
        continue;
      }

      console.log(`[x-browser] Pasting image: ${imagePath}`);

      if (!copyImageToClipboard(imagePath)) {
        console.warn(`[x-browser] Failed to copy image to clipboard: ${imagePath}`);
        continue;
      }

      // Count uploaded images before paste
      const imgCountBefore = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelectorAll('img[src^="blob:"]').length`,
        returnByValue: true,
      }, { sessionId: activeSessionId });

      // Wait for clipboard to be ready
      await sleep(500);

      // Focus the editor
      await cdp.send('Runtime.evaluate', {
        expression: `document.querySelector('[data-testid="tweetTextarea_0"]')?.focus()`,
      }, { sessionId: activeSessionId });
      await sleep(200);

      // Use paste script (handles platform differences, activates Chrome)
      console.log('[x-browser] Pasting from clipboard...');
      const pasteSuccess = pasteFromClipboard('Google Chrome', 5, 500);

      if (!pasteSuccess) {
        // Fallback to CDP (may not work for images on X)
        console.log('[x-browser] Paste script failed, trying CDP fallback...');
        const modifiers = process.platform === 'darwin' ? 4 : 2;
        await cdp.send('Input.dispatchKeyEvent', {
          type: 'keyDown',
          key: 'v',
          code: 'KeyV',
          modifiers,
          windowsVirtualKeyCode: 86,
        }, { sessionId: activeSessionId });
        await cdp.send('Input.dispatchKeyEvent', {
          type: 'keyUp',
          key: 'v',
          code: 'KeyV',
          modifiers,
          windowsVirtualKeyCode: 86,
        }, { sessionId: activeSessionId });
      }

      console.log('[x-browser] Verifying image upload...');
      const expectedImgCount = imgCountBefore.result.value + 1;
      let imgUploadOk = false;
      const imgWaitStart = Date.now();
      while (Date.now() - imgWaitStart < 15_000) {
        const r = await cdp!.send<{ result: { value: number } }>('Runtime.evaluate', {
          expression: `document.querySelectorAll('img[src^="blob:"]').length`,
          returnByValue: true,
        }, { sessionId: activeSessionId });
        if (r.result.value >= expectedImgCount) {
          imgUploadOk = true;
          break;
        }
        await sleep(1000);
      }

      if (imgUploadOk) {
        console.log('[x-browser] Image upload verified');
      } else {
        console.warn('[x-browser] Image upload not detected after 15s. Run check-paste-permissions.ts to diagnose.');
      }
    }

    if (submit) {
      console.log('[x-browser] Submitting post...');
      await cdp.send('Runtime.evaluate', {
        expression: `document.querySelector('[data-testid="tweetButton"]')?.click()`,
      }, { sessionId: activeSessionId });
      await sleep(2000);
      console.log('[x-browser] Post submitted!');
    } else {
      console.log('[x-browser] Post composed. Please review and click the publish button in the browser.');
    }
  } finally {
    let leaveChromeOpen = !submit;
    if (chrome && submit && loggedInDuringRun && cdp && sessionId) {
      console.log('[x-browser] Waiting for X session cookies to persist...');
      const sessionReady = await waitForXSessionPersistence({ cdp, sessionId });
      if (!sessionReady) {
        console.warn('[x-browser] X session cookies not observed yet. Leaving Chrome open so login can finish persisting.');
        leaveChromeOpen = true;
      }
    }

    if (cdp) {
      cdp.close();
    }
    if (chrome) {
      if (leaveChromeOpen) {
        chrome.unref();
      } else {
        await gracefulKillChrome(chrome, port);
      }
    }
  }
}

function printUsage(): never {
  console.log(`Post to X (Twitter) using real Chrome browser

Usage:
  npx -y bun x-browser.ts [options] [text]

Options:
  --image <path>   Add image (can be repeated, max 4)
  --submit         Actually post (default: preview only)
  --profile <dir>  Chrome profile directory
  --help           Show this help

Examples:
  npx -y bun x-browser.ts "Hello from CLI!"
  npx -y bun x-browser.ts "Check this out" --image ./screenshot.png
  npx -y bun x-browser.ts "Post it!" --image a.png --image b.png --submit
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) printUsage();

  const images: string[] = [];
  let submit = false;
  let profileDir: string | undefined;
  const textParts: string[] = [];

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--image' && args[i + 1]) {
      images.push(args[++i]!);
    } else if (arg === '--submit') {
      submit = true;
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (!arg.startsWith('-')) {
      textParts.push(arg);
    }
  }

  const text = textParts.join(' ').trim() || undefined;

  if (!text && images.length === 0) {
    console.error('Error: Provide text or at least one image.');
    process.exit(1);
  }

  await postToX({ text, images, submit, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
