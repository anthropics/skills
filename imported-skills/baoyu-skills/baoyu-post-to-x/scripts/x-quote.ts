import { mkdir } from 'node:fs/promises';
import process from 'node:process';
import {
  CHROME_CANDIDATES_FULL,
  CdpConnection,
  findExistingChromeDebugPort,
  getDefaultProfileDir,
  gracefulKillChrome,
  launchChrome,
  openPageSession,
  sleep,
  waitForXSessionPersistence,
  waitForChromeDebugPort,
} from './x-utils.js';

function extractTweetUrl(urlOrId: string): string | null {
  // If it's already a full URL, normalize it
  if (urlOrId.match(/(?:x\.com|twitter\.com)\/\w+\/status\/\d+/)) {
    return urlOrId.replace(/twitter\.com/, 'x.com').split('?')[0];
  }
  return null;
}

interface QuoteOptions {
  tweetUrl: string;
  comment?: string;
  submit?: boolean;
  timeoutMs?: number;
  profileDir?: string;
  chromePath?: string;
}

export async function quotePost(options: QuoteOptions): Promise<void> {
  const { tweetUrl, comment, submit = false, timeoutMs = 120_000, profileDir = getDefaultProfileDir() } = options;

  await mkdir(profileDir, { recursive: true });

  const existingPort = await findExistingChromeDebugPort(profileDir);
  const reusing = existingPort !== null;
  let port = existingPort ?? 0;
  console.log(`[x-quote] Opening tweet: ${tweetUrl}`);
  let chrome: Awaited<ReturnType<typeof launchChrome>>['chrome'] | null = null;
  if (!reusing) {
    const launched = await launchChrome(tweetUrl, profileDir, CHROME_CANDIDATES_FULL, options.chromePath);
    port = launched.port;
    chrome = launched.chrome;
  }

  if (reusing) console.log(`[x-quote] Reusing existing Chrome on port ${port}`);
  else console.log(`[x-quote] Launching Chrome (profile: ${profileDir})`);

  let cdp: CdpConnection | null = null;
  let sessionId: string | null = null;
  let targetId: string | null = null;
  let loggedInDuringRun = false;

  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    cdp = await CdpConnection.connect(wsUrl, 30_000, { defaultTimeoutMs: 15_000 });

    const page = await openPageSession({
      cdp,
      reusing,
      url: tweetUrl,
      matchTarget: (target) => target.type === 'page' && target.url.includes('x.com'),
      enablePage: true,
      enableRuntime: true,
      enableNetwork: true,
    });
    const activeSessionId = page.sessionId;
    sessionId = activeSessionId;
    targetId = page.targetId;

    console.log('[x-quote] Waiting for tweet to load...');
    await sleep(3000);

    // Wait for retweet button to appear (indicates tweet loaded and user logged in)
    const waitForRetweetButton = async (): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < timeoutMs) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `!!document.querySelector('[data-testid="retweet"]')`,
          returnByValue: true,
        }, { sessionId: activeSessionId });
        if (result.result.value) return true;
        await sleep(1000);
      }
      return false;
    };

    const retweetFound = await waitForRetweetButton();
    if (!retweetFound) {
      console.log('[x-quote] Tweet not found or not logged in. Please log in to X in the browser window.');
      console.log('[x-quote] Waiting for login...');
      const loggedIn = await waitForRetweetButton();
      if (!loggedIn) throw new Error('Timed out waiting for tweet. Please log in first or check the tweet URL.');
      loggedInDuringRun = true;
    }

    // Click the retweet button
    console.log('[x-quote] Clicking retweet button...');
    await cdp.send('Runtime.evaluate', {
      expression: `document.querySelector('[data-testid="retweet"]')?.click()`,
    }, { sessionId: activeSessionId });
    await sleep(1000);

    // Wait for and click the "Quote" option in the menu
    console.log('[x-quote] Selecting quote option...');
    const waitForQuoteOption = async (): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < 10_000) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `!!document.querySelector('[data-testid="Dropdown"] [role="menuitem"]:nth-child(2)')`,
          returnByValue: true,
        }, { sessionId: activeSessionId });
        if (result.result.value) return true;
        await sleep(200);
      }
      return false;
    };

    const quoteOptionFound = await waitForQuoteOption();
    if (!quoteOptionFound) {
      throw new Error('Quote option not found. The menu may not have opened.');
    }

    // Click the quote option (second menu item)
    await cdp.send('Runtime.evaluate', {
      expression: `document.querySelector('[data-testid="Dropdown"] [role="menuitem"]:nth-child(2)')?.click()`,
    }, { sessionId: activeSessionId });
    await sleep(2000);

    // Wait for the quote compose dialog
    console.log('[x-quote] Waiting for quote compose dialog...');
    const waitForQuoteDialog = async (): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < 10_000) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `!!document.querySelector('[data-testid="tweetTextarea_0"]')`,
          returnByValue: true,
        }, { sessionId: activeSessionId });
        if (result.result.value) return true;
        await sleep(200);
      }
      return false;
    };

    const dialogFound = await waitForQuoteDialog();
    if (!dialogFound) {
      throw new Error('Quote compose dialog not found.');
    }

    // Type the comment if provided
    if (comment) {
      console.log('[x-quote] Typing comment...');
      // Use CDP Input.insertText for more reliable text insertion
      await cdp.send('Runtime.evaluate', {
        expression: `document.querySelector('[data-testid="tweetTextarea_0"]')?.focus()`,
      }, { sessionId: activeSessionId });
      await sleep(200);

      await cdp.send('Input.insertText', {
        text: comment,
      }, { sessionId: activeSessionId });
      await sleep(500);
    }

    if (submit) {
      console.log('[x-quote] Submitting quote post...');
      await cdp.send('Runtime.evaluate', {
        expression: `document.querySelector('[data-testid="tweetButton"]')?.click()`,
      }, { sessionId: activeSessionId });
      await sleep(2000);
      console.log('[x-quote] Quote post submitted!');
    } else {
      console.log('[x-quote] Quote composed (preview mode). Add --submit to post.');
      console.log('[x-quote] Browser will stay open for 30 seconds for preview...');
      await sleep(30_000);
    }
  } finally {
    let leaveChromeOpen = false;
    if (chrome && loggedInDuringRun && cdp && sessionId) {
      console.log('[x-quote] Waiting for X session cookies to persist...');
      const sessionReady = await waitForXSessionPersistence({ cdp, sessionId });
      if (!sessionReady) {
        console.warn('[x-quote] X session cookies not observed yet. Leaving Chrome open so login can finish persisting.');
        leaveChromeOpen = true;
      }
    }

    if (cdp) {
      if (reusing && targetId) {
        try { await cdp.send('Target.closeTarget', { targetId }, { timeoutMs: 5_000 }); } catch {}
      }
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
  console.log(`Quote a tweet on X (Twitter) using real Chrome browser

Usage:
  npx -y bun x-quote.ts <tweet-url> [options] [comment]

Options:
  --submit         Actually post (default: preview only)
  --profile <dir>  Chrome profile directory
  --help           Show this help

Examples:
  npx -y bun x-quote.ts https://x.com/user/status/123456789 "Great insight!"
  npx -y bun x-quote.ts https://x.com/user/status/123456789 "I agree!" --submit
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) printUsage();

  let tweetUrl: string | undefined;
  let submit = false;
  let profileDir: string | undefined;
  const commentParts: string[] = [];

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--submit') {
      submit = true;
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (!arg.startsWith('-')) {
      // First non-option argument is the tweet URL
      if (!tweetUrl && arg.match(/(?:x\.com|twitter\.com)\/\w+\/status\/\d+/)) {
        tweetUrl = extractTweetUrl(arg) ?? undefined;
      } else {
        commentParts.push(arg);
      }
    }
  }

  if (!tweetUrl) {
    console.error('Error: Please provide a tweet URL.');
    console.error('Example: npx -y bun x-quote.ts https://x.com/user/status/123456789 "Your comment"');
    process.exit(1);
  }

  const comment = commentParts.join(' ').trim() || undefined;

  await quotePost({ tweetUrl, comment, submit, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
