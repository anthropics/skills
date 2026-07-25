import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const WECHAT_URL = 'https://mp.weixin.qq.com/';
const SESSION = 'wechat-post';

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function quoteForLog(arg: string): string {
  return /[\s"'\\]/.test(arg) ? JSON.stringify(arg) : arg;
}

function toSafeJsStringLiteral(value: string): string {
  return JSON.stringify(value)
    .replace(/\u2028/g, '\\u2028')
    .replace(/\u2029/g, '\\u2029');
}

function runAgentBrowser(args: string[]): {
  success: boolean;
  output: string;
  spawnError?: string;
} {
  const result = spawnSync('agent-browser', ['--session', SESSION, ...args], {
    encoding: 'utf8',
    stdio: ['pipe', 'pipe', 'pipe']
  });
  const spawnError = result.error?.message?.trim();
  const output = result.stdout || result.stderr || '';
  return {
    success: result.status === 0,
    output: output || spawnError || '',
    spawnError
  };
}

function ab(args: string[], json = false): string {
  const fullArgs = json ? [...args, '--json'] : args;
  console.log(`[ab] agent-browser --session ${SESSION} ${fullArgs.map(quoteForLog).join(' ')}`);
  const result = runAgentBrowser(fullArgs);
  if (result.spawnError) {
    throw new Error(`agent-browser failed to start: ${result.spawnError}`);
  }
  if (!result.success) {
    console.error(`[ab] Error: ${result.output.trim()}`);
  }
  return result.output.trim();
}

function abRaw(args: string[]): { success: boolean; output: string } {
  return runAgentBrowser(args);
}

interface SnapshotElement {
  ref: string;
  role: string;
  name: string;
}

function parseSnapshot(output: string): SnapshotElement[] {
  const elements: SnapshotElement[] = [];
  const refPattern = /\[ref=(@?\w+)\]/g;
  const lines = output.split('\n');

  for (const line of lines) {
    const match = line.match(/\[ref=([@\w]+)\]/);
    if (match) {
      const ref = match[1].startsWith('@') ? match[1] : `@${match[1]}`;
      const roleMatch = line.match(/^-\s+(\w+)/);
      const nameMatch = line.match(/"([^"]+)"/);
      elements.push({
        ref,
        role: roleMatch?.[1] || 'unknown',
        name: nameMatch?.[1] || ''
      });
    }
  }
  return elements;
}

function findElementByText(snapshot: string, text: string): string | null {
  const lines = snapshot.split('\n');
  for (const line of lines) {
    if (line.includes(`"${text}"`) || line.includes(text)) {
      const match = line.match(/\[ref=([@\w]+)\]/);
      if (match) {
        return match[1].startsWith('@') ? match[1] : `@${match[1]}`;
      }
    }
  }
  return null;
}

function findElementBySelector(snapshot: string, selector: string): string | null {
  return null;
}

interface WeChatOptions {
  title: string;
  content: string;
  images: string[];
  submit?: boolean;
  keepOpen?: boolean;
}

async function postToWeChat(options: WeChatOptions): Promise<void> {
  const { title, content, images, submit = false, keepOpen = true } = options;

  if (title.length > 20) throw new Error(`Title too long: ${title.length} chars (max 20)`);
  if (content.length > 1000) throw new Error(`Content too long: ${content.length} chars (max 1000)`);
  if (images.length === 0) throw new Error('At least one image is required');

  const absoluteImages = images.map(p => path.isAbsolute(p) ? p : path.resolve(process.cwd(), p));
  for (const img of absoluteImages) {
    if (!fs.existsSync(img)) throw new Error(`Image not found: ${img}`);
  }

  console.log('[wechat] Opening WeChat Official Account...');
  ab(['open', WECHAT_URL, '--headed']);
  await sleep(5000);

  console.log('[wechat] Checking login status...');
  let url = ab(['get', 'url']);
  console.log(`[wechat] Current URL: ${url}`);

  const waitForLogin = async (timeoutMs = 120_000): Promise<boolean> => {
    const start = Date.now();
    while (Date.now() - start < timeoutMs) {
      url = ab(['get', 'url']);
      if (url.includes('/cgi-bin/home')) return true;
      console.log('[wechat] Waiting for login...');
      await sleep(3000);
    }
    return false;
  };

  if (!url.includes('/cgi-bin/home')) {
    console.log('[wechat] Not logged in. Please scan QR code...');
    const loggedIn = await waitForLogin();
    if (!loggedIn) throw new Error('Login timeout');
  }
  console.log('[wechat] Logged in.');
  await sleep(2000);

  console.log('[wechat] Getting page snapshot...');
  let snapshot = ab(['snapshot']);
  console.log(snapshot);

  console.log('[wechat] Looking for "图文" menu...');
  const tuWenRef = findElementByText(snapshot, '图文');

  if (!tuWenRef) {
    console.log('[wechat] Using eval to find and click menu...');
    ab(['eval', "document.querySelectorAll('.new-creation__menu .new-creation__menu-item')[2].click()"]);
  } else {
    console.log(`[wechat] Clicking menu ref: ${tuWenRef}`);
    ab(['click', tuWenRef]);
  }

  await sleep(4000);

  console.log('[wechat] Checking for new tab...');
  const tabsOutput = ab(['tab']);
  console.log(`[wechat] Tabs: ${tabsOutput}`);

  const tabLines = tabsOutput.split('\n');
  const editorTabLine = tabLines.find(l => l.includes('appmsg') || (!l.includes('cgi-bin/home') && l.includes('mp.weixin.qq.com')));

  if (tabLines.length > 1) {
    const tabMatch = tabsOutput.match(/\[(\d+)\].*(?:appmsg|edit)/i);
    if (tabMatch) {
      console.log(`[wechat] Switching to editor tab ${tabMatch[1]}...`);
      ab(['tab', tabMatch[1]]);
    } else {
      const lastTabMatch = tabsOutput.match(/\[(\d+)\]/g);
      if (lastTabMatch && lastTabMatch.length > 1) {
        const lastTab = lastTabMatch[lastTabMatch.length - 1].match(/\d+/)?.[0];
        if (lastTab) {
          console.log(`[wechat] Switching to last tab ${lastTab}...`);
          ab(['tab', lastTab]);
        }
      }
    }
  }

  await sleep(3000);

  url = ab(['get', 'url']);
  console.log(`[wechat] Editor URL: ${url}`);

  console.log('[wechat] Getting editor snapshot...');
  snapshot = ab(['snapshot']);
  console.log(snapshot.substring(0, 2000));

  console.log('[wechat] Uploading images...');
  const fileInputSelector = '.js_upload_btn_container input[type=file]';
  const fileInputSelectorJs = toSafeJsStringLiteral(fileInputSelector);

  ab(['eval', `{
    const input = document.querySelector(${fileInputSelectorJs});
    if (input) input.style.display = 'block';
  }`]);
  await sleep(500);

  const uploadResult = abRaw(['upload', fileInputSelector, ...absoluteImages]);
  console.log(`[wechat] Upload result: ${uploadResult.output}`);

  if (!uploadResult.success) {
    console.log('[wechat] Using alternative upload method...');
    for (const img of absoluteImages) {
      console.log(`[wechat] Uploading: ${img}`);
      const imgUrlJs = toSafeJsStringLiteral(`file://${img}`);
      const imgFileNameJs = toSafeJsStringLiteral(path.basename(img));
      ab(['eval', `
        const input = document.querySelector(${fileInputSelectorJs});
        if (input) {
          const dt = new DataTransfer();
          fetch(${imgUrlJs}).then(r => r.blob()).then(b => {
            const file = new File([b], ${imgFileNameJs}, { type: 'image/png' });
            dt.items.add(file);
            input.files = dt.files;
            input.dispatchEvent(new Event('change', { bubbles: true }));
          });
        }
      `]);
      await sleep(2000);
    }
  }

  console.log('[wechat] Waiting for uploads to complete...');
  await sleep(10000);

  console.log('[wechat] Filling title...');
  snapshot = ab(['snapshot', '-i']);
  const titleRef = findElementByText(snapshot, 'title') || findElementByText(snapshot, '标题');

  if (titleRef) {
    ab(['fill', titleRef, title]);
  } else {
    const titleJs = toSafeJsStringLiteral(title);
    ab(['eval', `const t = document.querySelector('#title'); if(t) { t.value = ${titleJs}; t.dispatchEvent(new Event('input', {bubbles: true})); }`]);
  }
  await sleep(500);

  console.log('[wechat] Clicking on content editor...');
  const editorRef = findElementByText(snapshot, 'js_pmEditorArea') || findElementByText(snapshot, 'textbox');

  if (editorRef) {
    ab(['click', editorRef]);
  } else {
    ab(['eval', "document.querySelector('.js_pmEditorArea')?.click()"]);
  }
  await sleep(500);

  console.log('[wechat] Typing content...');
  const lines = content.split('\n');
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.length > 0) {
      const lineJs = toSafeJsStringLiteral(line);
      ab(['eval', `document.execCommand('insertText', false, ${lineJs})`]);
    }
    if (i < lines.length - 1) {
      ab(['press', 'Enter']);
    }
    await sleep(100);
  }

  console.log('[wechat] Content typed.');
  await sleep(1000);

  if (submit) {
    console.log('[wechat] Saving as draft...');
    const submitRef = findElementByText(snapshot, 'js_submit') || findElementByText(snapshot, '保存');
    if (submitRef) {
      ab(['click', submitRef]);
    } else {
      ab(['eval', "document.querySelector('#js_submit')?.click()"]);
    }
    await sleep(3000);
    console.log('[wechat] Draft saved!');
  } else {
    console.log('[wechat] Article composed (preview mode). Add --submit to save as draft.');
  }

  if (!keepOpen) {
    console.log('[wechat] Closing browser...');
    ab(['close']);
  } else {
    console.log('[wechat] Done. Browser window left open.');
  }
}

function printUsage(): never {
  console.log(`Post to WeChat Official Account using agent-browser

Usage:
  npx -y bun wechat-agent-browser.ts [options]

Options:
  --title <text>   Article title (max 20 chars, required)
  --content <text> Article content (max 1000 chars, required)
  --image <path>   Add image (can be repeated, 1+ images, required)
  --submit         Save as draft (default: preview only)
  --close          Close browser after operation (default: keep open)
  --help           Show this help

Examples:
  npx -y bun wechat-agent-browser.ts --title "测试" --content "内容" --image ./photo.png
  npx -y bun wechat-agent-browser.ts --title "测试" --content "内容" --image a.png --image b.png --submit
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) printUsage();

  const images: string[] = [];
  let submit = false;
  let keepOpen = true;
  let title: string | undefined;
  let content: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--image' && args[i + 1]) {
      images.push(args[++i]!);
    } else if (arg === '--title' && args[i + 1]) {
      title = args[++i];
    } else if (arg === '--content' && args[i + 1]) {
      content = args[++i];
    } else if (arg === '--submit') {
      submit = true;
    } else if (arg === '--close') {
      keepOpen = false;
    }
  }

  if (!title) {
    console.error('Error: --title is required');
    process.exit(1);
  }
  if (!content) {
    console.error('Error: --content is required');
    process.exit(1);
  }
  if (images.length === 0) {
    console.error('Error: At least one --image is required');
    process.exit(1);
  }

  await postToWeChat({ title, content, images, submit, keepOpen });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
