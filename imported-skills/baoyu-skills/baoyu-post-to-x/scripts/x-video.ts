import fs from 'node:fs';
import { mkdir } from 'node:fs/promises';
import path from 'node:path';
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

const X_COMPOSE_URL = 'https://x.com/compose/post';

interface XVideoOptions {
  text?: string;
  videoPath: string;
  submit?: boolean;
  timeoutMs?: number;
  profileDir?: string;
  chromePath?: string;
}

export async function postVideoToX(options: XVideoOptions): Promise<void> {
  const { text, videoPath, submit = false, timeoutMs = 120_000, profileDir = getDefaultProfileDir() } = options;

  if (!fs.existsSync(videoPath)) throw new Error(`Video not found: ${videoPath}`);

  const absVideoPath = path.resolve(videoPath);
  console.log(`[x-video] Video: ${absVideoPath}`);

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

  if (reusing) console.log(`[x-video] Reusing existing Chrome on port ${port}`);
  else console.log(`[x-video] Launching Chrome (profile: ${profileDir})`);

  let cdp: CdpConnection | null = null;
  let sessionId: string | null = null;
  let targetId: string | null = null;
  let loggedInDuringRun = false;

  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    cdp = await CdpConnection.connect(wsUrl, 30_000, { defaultTimeoutMs: 30_000 });

    const page = await openPageSession({
      cdp,
      reusing,
      url: X_COMPOSE_URL,
      matchTarget: (target) => target.type === 'page' && target.url.includes('x.com'),
      enablePage: true,
      enableRuntime: true,
      enableDom: true,
      enableNetwork: true,
    });
    const activeSessionId = page.sessionId;
    sessionId = activeSessionId;
    targetId = page.targetId;
    await cdp.send('Input.setIgnoreInputEvents', { ignore: false }, { sessionId: activeSessionId });

    console.log('[x-video] Waiting for X editor...');
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
      console.log('[x-video] Editor not found. Please log in to X in the browser window.');
      console.log('[x-video] Waiting for login...');
      const loggedIn = await waitForEditor();
      if (!loggedIn) throw new Error('Timed out waiting for X editor. Please log in first.');
      loggedInDuringRun = true;
    }

    // Upload video FIRST (before typing text to avoid text being cleared)
    console.log('[x-video] Uploading video...');

    const { root } = await cdp.send<{ root: { nodeId: number } }>('DOM.getDocument', {}, { sessionId: activeSessionId });
    const { nodeId } = await cdp.send<{ nodeId: number }>('DOM.querySelector', {
      nodeId: root.nodeId,
      selector: 'input[type="file"][accept*="video"], input[data-testid="fileInput"], input[type="file"]',
    }, { sessionId: activeSessionId });

    if (!nodeId || nodeId === 0) {
      throw new Error('Could not find file input for video upload.');
    }

    await cdp.send('DOM.setFileInputFiles', {
      nodeId,
      files: [absVideoPath],
    }, { sessionId: activeSessionId });
    console.log('[x-video] Video file set, uploading in background...');

    // Wait a moment for upload to start, then type text while video processes
    await sleep(2000);

    // Type text while video uploads in background
    if (text) {
      console.log('[x-video] Typing text...');
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

    // Wait for video to finish processing by checking if tweet button is enabled
    console.log('[x-video] Waiting for video processing...');
    const waitForVideoReady = async (maxWaitMs = 180_000): Promise<boolean> => {
      const start = Date.now();
      let dots = 0;
      while (Date.now() - start < maxWaitMs) {
        const result = await cdp!.send<{ result: { value: { hasMedia: boolean; buttonEnabled: boolean } } }>('Runtime.evaluate', {
          expression: `(() => {
            const hasMedia = !!document.querySelector('[data-testid="attachments"] video, [data-testid="videoPlayer"], video');
            const tweetBtn = document.querySelector('[data-testid="tweetButton"]');
            const buttonEnabled = tweetBtn && !tweetBtn.disabled && tweetBtn.getAttribute('aria-disabled') !== 'true';
            return { hasMedia, buttonEnabled };
          })()`,
          returnByValue: true,
        }, { sessionId: activeSessionId });

        const { hasMedia, buttonEnabled } = result.result.value;
        if (hasMedia && buttonEnabled) {
          console.log('');
          return true;
        }

        process.stdout.write('.');
        dots++;
        if (dots % 60 === 0) console.log(''); // New line every 60 dots
        await sleep(2000);
      }
      console.log('');
      return false;
    };

    const videoReady = await waitForVideoReady();
    if (videoReady) {
      console.log('[x-video] Video ready!');
    } else {
      console.log('[x-video] Video may still be processing. Please check browser window.');
    }

    if (submit) {
      console.log('[x-video] Submitting post...');
      await cdp.send('Runtime.evaluate', {
        expression: `document.querySelector('[data-testid="tweetButton"]')?.click()`,
      }, { sessionId: activeSessionId });
      await sleep(5000);
      console.log('[x-video] Post submitted!');
    } else {
      console.log('[x-video] Post composed (preview mode). Add --submit to post.');
      console.log('[x-video] Browser stays open for review.');
    }
  } finally {
    let leaveChromeOpen = !submit;
    if (chrome && submit && loggedInDuringRun && cdp && sessionId) {
      console.log('[x-video] Waiting for X session cookies to persist...');
      const sessionReady = await waitForXSessionPersistence({ cdp, sessionId });
      if (!sessionReady) {
        console.warn('[x-video] X session cookies not observed yet. Leaving Chrome open so login can finish persisting.');
        leaveChromeOpen = true;
      }
    }

    if (cdp) {
      if (reusing && submit && targetId) {
        try { await cdp.send('Target.closeTarget', { targetId }, { timeoutMs: 5_000 }); } catch {}
      }
      cdp.close();
    }
    if (chrome && submit) {
      if (leaveChromeOpen) {
        chrome.unref();
      } else {
        await gracefulKillChrome(chrome, port);
      }
    }
  }
}

function printUsage(): never {
  console.log(`Post video to X (Twitter) using real Chrome browser

Usage:
  npx -y bun x-video.ts [options] --video <path> [text]

Options:
  --video <path>   Video file path (required, supports mp4/mov/webm)
  --submit         Actually post (default: preview only)
  --profile <dir>  Chrome profile directory
  --help           Show this help

Examples:
  npx -y bun x-video.ts --video ./clip.mp4 "Check out this video!"
  npx -y bun x-video.ts --video ./demo.mp4 --submit
  npx -y bun x-video.ts --video ./video.mp4 "Multi-line text
works too"

Notes:
  - Video is uploaded first, then text is added (to avoid text being cleared)
  - Video processing may take 30-60 seconds depending on file size
  - Maximum video length on X: 140 seconds (regular) or 60 min (Premium)
  - Supported formats: MP4, MOV, WebM
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) printUsage();

  let videoPath: string | undefined;
  let submit = false;
  let profileDir: string | undefined;
  const textParts: string[] = [];

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--video' && args[i + 1]) {
      videoPath = args[++i]!;
    } else if (arg === '--submit') {
      submit = true;
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (!arg.startsWith('-')) {
      textParts.push(arg);
    }
  }

  const text = textParts.join(' ').trim() || undefined;

  if (!videoPath) {
    console.error('Error: --video <path> is required.');
    printUsage();
  }

  await postVideoToX({ text, videoPath, submit, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
