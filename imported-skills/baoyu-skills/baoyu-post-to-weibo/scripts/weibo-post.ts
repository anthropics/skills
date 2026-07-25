import fs from 'node:fs';
import { mkdir } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import {
  CdpConnection,
  findChromeExecutable,
  findExistingChromeDebugPort,
  getDefaultProfileDir,
  killChromeByProfile,
  launchChrome as launchWeiboChrome,
  sleep,
  waitForChromeDebugPort,
} from './weibo-utils.js';

const WEIBO_HOME_URL = 'https://weibo.com/';

const MAX_FILES = 18;

interface WeiboPostOptions {
  text?: string;
  images?: string[];
  videos?: string[];
  timeoutMs?: number;
  profileDir?: string;
  chromePath?: string;
}

export async function postToWeibo(options: WeiboPostOptions): Promise<void> {
  const { text, images = [], videos = [], timeoutMs = 120_000, profileDir = getDefaultProfileDir() } = options;

  const allFiles = [...images, ...videos];
  if (allFiles.length > MAX_FILES) {
    throw new Error(`Too many files: ${allFiles.length} (max ${MAX_FILES})`);
  }

  await mkdir(profileDir, { recursive: true });

  const chromePath = findChromeExecutable(options.chromePath);
  if (!chromePath) throw new Error('Chrome not found. Set WEIBO_BROWSER_CHROME_PATH env var.');

  let port: number;
  const existingPort = await findExistingChromeDebugPort(profileDir);

  if (existingPort) {
    console.log(`[weibo-post] Found existing Chrome on port ${existingPort}, checking health...`);
    try {
      const wsUrl = await waitForChromeDebugPort(existingPort, 5_000);
      const testCdp = await CdpConnection.connect(wsUrl, 5_000, { defaultTimeoutMs: 5_000 });
      await testCdp.send('Target.getTargets');
      testCdp.close();
      console.log('[weibo-post] Existing Chrome is responsive, reusing.');
      port = existingPort;
    } catch {
      console.log('[weibo-post] Existing Chrome unresponsive, restarting...');
      killChromeByProfile(profileDir);
      await sleep(2000);
      port = await launchWeiboChrome(WEIBO_HOME_URL, profileDir, chromePath);
    }
  } else {
    port = await launchWeiboChrome(WEIBO_HOME_URL, profileDir, chromePath);
  }

  let cdp: CdpConnection | null = null;

  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000);
    cdp = await CdpConnection.connect(wsUrl, 30_000, { defaultTimeoutMs: 15_000 });

    const targets = await cdp.send<{ targetInfos: Array<{ targetId: string; url: string; type: string }> }>('Target.getTargets');
    let pageTarget = targets.targetInfos.find((t) => t.type === 'page' && t.url.includes('weibo.com'));

    if (!pageTarget) {
      const { targetId } = await cdp.send<{ targetId: string }>('Target.createTarget', { url: WEIBO_HOME_URL });
      pageTarget = { targetId, url: WEIBO_HOME_URL, type: 'page' };
    }

    const { sessionId } = await cdp.send<{ sessionId: string }>('Target.attachToTarget', { targetId: pageTarget.targetId, flatten: true });

    await cdp.send('Target.activateTarget', { targetId: pageTarget.targetId });

    await cdp.send('Page.enable', {}, { sessionId });
    await cdp.send('Runtime.enable', {}, { sessionId });
    await cdp.send('Input.setIgnoreInputEvents', { ignore: false }, { sessionId });

    const currentUrl = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
      expression: `window.location.href`,
      returnByValue: true,
    }, { sessionId });

    if (!currentUrl.result.value.includes('weibo.com/') || currentUrl.result.value.includes('card.weibo.com')) {
      console.log('[weibo-post] Navigating to Weibo home...');
      await cdp.send('Page.navigate', { url: WEIBO_HOME_URL }, { sessionId });
      await sleep(3000);
    }

    console.log('[weibo-post] Waiting for Weibo editor...');
    await sleep(3000);

    const waitForEditor = async (): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < timeoutMs) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `!!document.querySelector('#homeWrap textarea')`,
          returnByValue: true,
        }, { sessionId });
        if (result.result.value) return true;
        await sleep(1000);
      }
      return false;
    };

    const editorFound = await waitForEditor();
    if (!editorFound) {
      console.log('[weibo-post] Editor not found. Please log in to Weibo in the browser window.');
      console.log('[weibo-post] Waiting for login...');
      const loggedIn = await waitForEditor();
      if (!loggedIn) throw new Error('Timed out waiting for Weibo editor. Please log in first.');
    }

    if (text) {
      console.log('[weibo-post] Typing text...');

      // Focus and use Input.insertText via CDP
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const editor = document.querySelector('#homeWrap textarea');
          if (editor) { editor.focus(); editor.value = ''; }
        })()`,
      }, { sessionId });
      await sleep(200);

      await cdp.send('Input.insertText', { text }, { sessionId });
      await sleep(500);

      // Verify text was entered
      const textCheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `document.querySelector('#homeWrap textarea')?.value || ''`,
        returnByValue: true,
      }, { sessionId });

      if (textCheck.result.value.length > 0) {
        console.log(`[weibo-post] Text verified (${textCheck.result.value.length} chars)`);
      } else {
        console.warn('[weibo-post] Text input appears empty, trying execCommand fallback...');
        await cdp.send('Runtime.evaluate', {
          expression: `(() => {
            const editor = document.querySelector('#homeWrap textarea');
            if (editor) { editor.focus(); document.execCommand('insertText', false, ${JSON.stringify(text)}); }
          })()`,
        }, { sessionId });
        await sleep(300);

        const textRecheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
          expression: `document.querySelector('#homeWrap textarea')?.value || ''`,
          returnByValue: true,
        }, { sessionId });
        console.log(`[weibo-post] Text after fallback: ${textRecheck.result.value.length} chars`);
      }
    }

    if (allFiles.length > 0) {
      const missing = allFiles.filter((f) => !fs.existsSync(f));
      if (missing.length > 0) {
        throw new Error(`Files not found: ${missing.join(', ')}`);
      }

      const absolutePaths = allFiles.map((f) => path.resolve(f));
      console.log(`[weibo-post] Uploading ${absolutePaths.length} file(s) via file input...`);

      await cdp.send('DOM.enable', {}, { sessionId });

      const { root } = await cdp.send<{ root: { nodeId: number } }>('DOM.getDocument', {}, { sessionId });

      const { nodeId } = await cdp.send<{ nodeId: number }>('DOM.querySelector', {
        nodeId: root.nodeId,
        selector: '#homeWrap input[type="file"]',
      }, { sessionId });

      if (!nodeId || nodeId === 0) {
        throw new Error('File input not found. Make sure the Weibo compose area is visible.');
      }

      await cdp.send('DOM.setFileInputFiles', {
        nodeId,
        files: absolutePaths,
      }, { sessionId });

      console.log('[weibo-post] Files set on input. Waiting for upload...');
      await sleep(2000);

      const uploadCheck = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelectorAll('#homeWrap img[src^="blob:"], #homeWrap img[src^="data:"], #homeWrap video').length`,
        returnByValue: true,
      }, { sessionId });

      if (uploadCheck.result.value > 0) {
        console.log(`[weibo-post] Upload verified (${uploadCheck.result.value} media item(s) detected)`);
      } else {
        console.warn('[weibo-post] Upload may still be in progress. Please verify in browser.');
      }
    }

    console.log('[weibo-post] Post composed. Please review and click the publish button in the browser.');
    console.log('[weibo-post] Browser remains open for manual review.');

  } finally {
    if (cdp) {
      cdp.close();
    }
  }
}

function printUsage(): never {
  console.log(`Post to Weibo using real Chrome browser

Usage:
  npx -y bun weibo-post.ts [options] [text]

Options:
  --image <path>   Add image (can be repeated)
  --video <path>   Add video (can be repeated)
  --profile <dir>  Chrome profile directory
  --help           Show this help

Max ${MAX_FILES} files total (images + videos combined).

Examples:
  npx -y bun weibo-post.ts "Hello from CLI!"
  npx -y bun weibo-post.ts "Check this out" --image ./screenshot.png
  npx -y bun weibo-post.ts "Post it!" --image a.png --image b.png
  npx -y bun weibo-post.ts "Watch this" --video ./clip.mp4
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) printUsage();

  const images: string[] = [];
  const videos: string[] = [];
  let profileDir: string | undefined;
  const textParts: string[] = [];

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--image' && args[i + 1]) {
      images.push(args[++i]!);
    } else if (arg === '--video' && args[i + 1]) {
      videos.push(args[++i]!);
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (!arg.startsWith('-')) {
      textParts.push(arg);
    }
  }

  const text = textParts.join(' ').trim() || undefined;

  if (!text && images.length === 0 && videos.length === 0) {
    console.error('Error: Provide text or at least one image/video.');
    process.exit(1);
  }

  await postToWeibo({ text, images, videos, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
