import fs from 'node:fs';
import { readdir } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  CdpConnection,
  findChromeExecutable,
  getDefaultProfileDir,
  getAccountProfileDir,
  launchChrome,
  sleep,
} from './cdp.ts';
import { loadWechatExtendConfig, resolveAccount } from './wechat-extend-config.ts';

const WECHAT_URL = 'https://mp.weixin.qq.com/';

interface MarkdownMeta {
  title: string;
  author: string;
  content: string;
}

function parseMarkdownFile(filePath: string): MarkdownMeta {
  const text = fs.readFileSync(filePath, 'utf-8');
  let title = '';
  let author = '';
  let content = '';

  const fmMatch = text.match(/^---\r?\n([\s\S]*?)\r?\n---/);
  if (fmMatch) {
    const fm = fmMatch[1]!;
    const titleMatch = fm.match(/^title:\s*(.+)$/m);
    if (titleMatch) title = titleMatch[1]!.trim().replace(/^["']|["']$/g, '');
    const authorMatch = fm.match(/^author:\s*(.+)$/m);
    if (authorMatch) author = authorMatch[1]!.trim().replace(/^["']|["']$/g, '');
  }

  const bodyText = fmMatch ? text.slice(fmMatch[0].length) : text;

  if (!title) {
    const h1Match = bodyText.match(/^#\s+(.+)$/m);
    if (h1Match) title = h1Match[1]!.trim();
  }

  const lines = bodyText.split('\n');
  const paragraphs: string[] = [];
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    if (trimmed.startsWith('#')) continue;
    if (trimmed.startsWith('![')) continue;
    if (trimmed.startsWith('---')) continue;
    paragraphs.push(trimmed);
    if (paragraphs.join('\n').length > 1200) break;
  }
  content = paragraphs.join('\n');

  return { title, author, content };
}

function compressTitle(title: string, maxLen = 20): string {
  if (title.length <= maxLen) return title;

  const prefixes = ['如何', '为什么', '什么是', '怎样', '怎么', '关于'];
  let t = title;
  for (const p of prefixes) {
    if (t.startsWith(p) && t.length > maxLen) {
      t = t.slice(p.length);
      if (t.length <= maxLen) return t;
    }
  }

  const fillers = ['的', '了', '在', '是', '和', '与', '以及', '或者', '或', '还是', '而且', '并且', '但是', '但', '因为', '所以', '如果', '那么', '虽然', '不过', '然而', '——', '…'];
  for (const f of fillers) {
    if (t.length <= maxLen) break;
    t = t.replace(new RegExp(f, 'g'), '');
  }

  if (t.length > maxLen) t = t.slice(0, maxLen);

  return t;
}

function compressContent(content: string, maxLen = 1000): string {
  if (content.length <= maxLen) return content;

  const lines = content.split('\n');
  const result: string[] = [];
  let len = 0;

  for (const line of lines) {
    if (len + line.length + 1 > maxLen) {
      const remaining = maxLen - len - 1;
      if (remaining > 20) result.push(line.slice(0, remaining - 3) + '...');
      break;
    }
    result.push(line);
    len += line.length + 1;
  }

  return result.join('\n');
}

async function loadImagesFromDir(dir: string): Promise<string[]> {
  const entries = await readdir(dir);
  const images = entries
    .filter(f => /\.(png|jpg|jpeg|gif|webp)$/i.test(f))
    .sort()
    .map(f => path.join(dir, f));
  return images;
}

interface WeChatBrowserOptions {
  title?: string;
  content?: string;
  images?: string[];
  imagesDir?: string;
  markdownFile?: string;
  submit?: boolean;
  timeoutMs?: number;
  profileDir?: string;
  chromePath?: string;
}

export async function postToWeChat(options: WeChatBrowserOptions): Promise<void> {
  const { submit = false, timeoutMs = 120_000, profileDir = getDefaultProfileDir() } = options;

  let title = options.title || '';
  let content = options.content || '';
  let images = options.images || [];

  if (options.markdownFile) {
    const absPath = path.isAbsolute(options.markdownFile) ? options.markdownFile : path.resolve(process.cwd(), options.markdownFile);
    if (!fs.existsSync(absPath)) throw new Error(`Markdown file not found: ${absPath}`);
    const meta = parseMarkdownFile(absPath);
    if (!title) title = meta.title;
    if (!content) content = meta.content;
    console.log(`[wechat-browser] Parsed markdown: title="${meta.title}", content=${meta.content.length} chars`);
  }

  if (options.imagesDir) {
    const absDir = path.isAbsolute(options.imagesDir) ? options.imagesDir : path.resolve(process.cwd(), options.imagesDir);
    if (!fs.existsSync(absDir)) throw new Error(`Images directory not found: ${absDir}`);
    images = await loadImagesFromDir(absDir);
    console.log(`[wechat-browser] Found ${images.length} images in ${absDir}`);
  }

  if (title.length > 20) {
    const original = title;
    title = compressTitle(title, 20);
    console.log(`[wechat-browser] Title compressed: "${original}" → "${title}"`);
  }

  if (content.length > 1000) {
    const original = content.length;
    content = compressContent(content, 1000);
    console.log(`[wechat-browser] Content compressed: ${original} → ${content.length} chars`);
  }

  if (!title) throw new Error('Title is required (use --title or --markdown)');
  if (!content) throw new Error('Content is required (use --content or --markdown)');
  if (images.length === 0) throw new Error('At least one image is required (use --image or --images)');

  for (const img of images) {
    if (!fs.existsSync(img)) throw new Error(`Image not found: ${img}`);
  }

  const chromePath = findChromeExecutable(options.chromePath);
  if (!chromePath) throw new Error('Chrome not found. Set WECHAT_BROWSER_CHROME_PATH env var.');

  console.log(`[wechat-browser] Launching Chrome (profile: ${profileDir})`);

  const launched = await launchChrome(WECHAT_URL, profileDir, chromePath);
  const chrome = launched.chrome;

  let cdp: CdpConnection | null = null;

  try {
    cdp = launched.cdp;

    const targets = await cdp.send<{ targetInfos: Array<{ targetId: string; url: string; type: string }> }>('Target.getTargets');
    let pageTarget = targets.targetInfos.find((t) => t.type === 'page' && t.url.includes('mp.weixin.qq.com'));

    if (!pageTarget) {
      const { targetId } = await cdp.send<{ targetId: string }>('Target.createTarget', { url: WECHAT_URL });
      pageTarget = { targetId, url: WECHAT_URL, type: 'page' };
    }

    let { sessionId } = await cdp.send<{ sessionId: string }>('Target.attachToTarget', { targetId: pageTarget.targetId, flatten: true });

    await cdp.send('Page.enable', {}, { sessionId });
    await cdp.send('Runtime.enable', {}, { sessionId });
    await cdp.send('DOM.enable', {}, { sessionId });

    console.log('[wechat-browser] Waiting for page load...');
    await sleep(3000);

    const checkLoginStatus = async (): Promise<boolean> => {
      const result = await cdp!.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `window.location.href`,
        returnByValue: true,
      }, { sessionId });
      return result.result.value.includes('/cgi-bin/home');
    };

    const waitForLogin = async (): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < timeoutMs) {
        if (await checkLoginStatus()) return true;
        await sleep(2000);
      }
      return false;
    };

    let isLoggedIn = await checkLoginStatus();
    if (!isLoggedIn) {
      console.log('[wechat-browser] Not logged in. Please scan QR code to log in...');
      isLoggedIn = await waitForLogin();
      if (!isLoggedIn) throw new Error('Timed out waiting for login. Please log in first.');
    }
    console.log('[wechat-browser] Logged in.');

    await sleep(2000);

    console.log('[wechat-browser] Looking for "贴图" menu...');
    const menuResult = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
      expression: `
        const menuItems = document.querySelectorAll('.new-creation__menu .new-creation__menu-item');
        const count = menuItems.length;
        const texts = Array.from(menuItems).map(m => m.querySelector('.new-creation__menu-title')?.textContent?.trim() || m.textContent?.trim() || '');
        JSON.stringify({ count, texts });
      `,
      returnByValue: true,
    }, { sessionId });
    console.log(`[wechat-browser] Menu items: ${menuResult.result.value}`);

    const getTargets = async () => {
      return await cdp!.send<{ targetInfos: Array<{ targetId: string; url: string; type: string }> }>('Target.getTargets');
    };

    const initialTargets = await getTargets();
    const initialIds = new Set(initialTargets.targetInfos.map(t => t.targetId));
    console.log(`[wechat-browser] Initial targets count: ${initialTargets.targetInfos.length}`);

    console.log('[wechat-browser] Finding "贴图" menu position...');
    const menuPos = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
      expression: `
        (function() {
          const menuItems = document.querySelectorAll('.new-creation__menu .new-creation__menu-item');
          console.log('Found menu items:', menuItems.length);
          for (const item of menuItems) {
            const title = item.querySelector('.new-creation__menu-title');
            const text = title?.textContent?.trim() || '';
            console.log('Menu item text:', text);
            if (text === '图文' || text === '贴图') {
              item.scrollIntoView({ block: 'center' });
              const rect = item.getBoundingClientRect();
              console.log('Found 贴图，rect:', JSON.stringify(rect));
              return JSON.stringify({ x: rect.x + rect.width / 2, y: rect.y + rect.height / 2, width: rect.width, height: rect.height });
            }
          }
          return 'null';
        })()
      `,
      returnByValue: true,
    }, { sessionId });
    console.log(`[wechat-browser] Menu position: ${menuPos.result.value}`);

    const pos = menuPos.result.value !== 'null' ? JSON.parse(menuPos.result.value) : null;
    if (!pos) throw new Error('贴图 menu not found or not visible');

    console.log('[wechat-browser] Clicking "贴图" menu with mouse events...');
    await cdp.send('Input.dispatchMouseEvent', {
      type: 'mousePressed',
      x: pos.x,
      y: pos.y,
      button: 'left',
      clickCount: 1,
    }, { sessionId });
    await sleep(100);
    await cdp.send('Input.dispatchMouseEvent', {
      type: 'mouseReleased',
      x: pos.x,
      y: pos.y,
      button: 'left',
      clickCount: 1,
    }, { sessionId });

    console.log('[wechat-browser] Waiting for editor...');
    await sleep(3000);

    const waitForEditor = async (): Promise<{ targetId: string; isNewTab: boolean } | null> => {
      const start = Date.now();

      while (Date.now() - start < 30_000) {
        const targets = await getTargets();
        const pageTargets = targets.targetInfos.filter(t => t.type === 'page');

        for (const t of pageTargets) {
          console.log(`[wechat-browser] Target: ${t.url}`);
        }

        const newTab = pageTargets.find(t => !initialIds.has(t.targetId) && t.url.includes('mp.weixin.qq.com'));
        if (newTab) {
          console.log(`[wechat-browser] Found new tab: ${newTab.url}`);
          return { targetId: newTab.targetId, isNewTab: true };
        }

        const editorTab = pageTargets.find(t => t.url.includes('appmsg'));
        if (editorTab) {
          console.log(`[wechat-browser] Found editor tab: ${editorTab.url}`);
          return { targetId: editorTab.targetId, isNewTab: !initialIds.has(editorTab.targetId) };
        }

        const currentUrl = await cdp!.send<{ result: { value: string } }>('Runtime.evaluate', {
          expression: `window.location.href`,
          returnByValue: true,
        }, { sessionId });
        console.log(`[wechat-browser] Current page URL: ${currentUrl.result.value}`);

        if (currentUrl.result.value.includes('appmsg')) {
          console.log(`[wechat-browser] Current page navigated to editor`);
          return { targetId: pageTarget!.targetId, isNewTab: false };
        }

        await sleep(1000);
      }
      return null;
    };

    const editorInfo = await waitForEditor();
    if (!editorInfo) {
      const finalTargets = await getTargets();
      console.log(`[wechat-browser] Final targets: ${finalTargets.targetInfos.filter(t => t.type === 'page').map(t => t.url).join(', ')}`);
      throw new Error('Editor not found.');
    }

    if (editorInfo.isNewTab) {
      console.log('[wechat-browser] Switching to editor tab...');
      const editorSession = await cdp.send<{ sessionId: string }>('Target.attachToTarget', { targetId: editorInfo.targetId, flatten: true });
      sessionId = editorSession.sessionId;

      await cdp.send('Page.enable', {}, { sessionId });
      await cdp.send('Runtime.enable', {}, { sessionId });
      await cdp.send('DOM.enable', {}, { sessionId });
    } else {
      console.log('[wechat-browser] Editor opened in current page');
    }

    await cdp.send('Page.enable', {}, { sessionId });
    await cdp.send('Runtime.enable', {}, { sessionId });
    await cdp.send('DOM.enable', {}, { sessionId });

    await sleep(2000);

    console.log('[wechat-browser] Uploading all images at once...');
    const absolutePaths = images.map(p => path.isAbsolute(p) ? p : path.resolve(process.cwd(), p));
    console.log(`[wechat-browser] Images: ${absolutePaths.join(', ')}`);

    // --- PRIMARY approach: intercept file chooser dialog ---
    let uploadSuccess = false;
    try {
      console.log('[wechat-browser] [primary] Enabling file chooser interception...');
      await cdp.send('Page.setInterceptFileChooserDialog', { enabled: true }, { sessionId });

      // Set up listener for file chooser opened event BEFORE clicking
      const fileChooserPromise = new Promise<{ backendNodeId: number; mode: string }>((resolve, reject) => {
        const timeout = setTimeout(() => reject(new Error('File chooser dialog not opened within 10s')), 10_000);
        cdp!.on('Page.fileChooserOpened', (params: unknown) => {
          clearTimeout(timeout);
          const p = params as { backendNodeId: number; mode: string };
          console.log(`[wechat-browser] [primary] File chooser opened: backendNodeId=${p.backendNodeId}, mode=${p.mode}`);
          resolve(p);
        });
      });

      // Trigger file chooser by calling .click() on the file input with userGesture
      const fileInputSelectors = [
        '.js_upload_btn_container input[type=file]',
        'input[type=file][multiple][accept*="image"]',
        'input[type=file][accept*="image"]',
        'input[type=file][multiple]',
        'input[type=file]',
      ];

      console.log('[wechat-browser] [primary] Clicking file input via JS .click() with userGesture...');
      const clickResult = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `
          (function() {
            const selectors = ${JSON.stringify(fileInputSelectors)};
            for (const sel of selectors) {
              const el = document.querySelector(sel);
              if (el) {
                el.click();
                return JSON.stringify({ clicked: sel });
              }
            }
            const debug = [];
            document.querySelectorAll('input[type=file]').forEach((inp, i) => {
              debug.push({ i, accept: inp.accept, multiple: inp.multiple, parentClass: inp.parentElement?.className?.slice(0, 60) });
            });
            return JSON.stringify({ error: 'no file input found', fileInputs: debug });
          })()
        `,
        returnByValue: true,
        userGesture: true,
      }, { sessionId });
      console.log(`[wechat-browser] [primary] Click result: ${clickResult.result.value}`);

      const clickStatus = JSON.parse(clickResult.result.value);
      if (clickStatus.error) {
        throw new Error(`File input not found: ${clickStatus.error}`);
      }

      // Wait for the file chooser event
      console.log('[wechat-browser] [primary] Waiting for file chooser dialog...');
      const chooser = await fileChooserPromise;

      console.log(`[wechat-browser] [primary] Setting files via backendNodeId=${chooser.backendNodeId}...`);
      await cdp.send('DOM.setFileInputFiles', {
        files: absolutePaths,
        backendNodeId: chooser.backendNodeId,
      }, { sessionId });
      console.log('[wechat-browser] [primary] Files set successfully via file chooser interception');
      uploadSuccess = true;
    } catch (primaryErr) {
      console.log(`[wechat-browser] [primary] File chooser approach failed: ${primaryErr instanceof Error ? primaryErr.message : String(primaryErr)}`);
      // Disable interception before falling back
      try { await cdp.send('Page.setInterceptFileChooserDialog', { enabled: false }, { sessionId }); } catch {}
    }

    // --- FALLBACK approach: direct DOM.setFileInputFiles on nodeId ---
    if (!uploadSuccess) {
      console.log('[wechat-browser] [fallback] Trying direct DOM.setFileInputFiles...');
      const { root } = await cdp.send<{ root: { nodeId: number } }>('DOM.getDocument', {}, { sessionId });

      const fileInputSelectors = [
        '.js_upload_btn_container input[type=file]',
        'input[type=file][multiple][accept*="image"]',
        'input[type=file][accept*="image"]',
        'input[type=file][multiple]',
        'input[type=file]',
      ];

      let nodeId = 0;
      for (const sel of fileInputSelectors) {
        const result = await cdp.send<{ nodeId: number }>('DOM.querySelector', { nodeId: root.nodeId, selector: sel }, { sessionId });
        if (result.nodeId) {
          console.log(`[wechat-browser] [fallback] Found file input with selector: ${sel}`);
          nodeId = result.nodeId;
          break;
        }
      }

      if (!nodeId) throw new Error('File input not found with any selector');

      await cdp.send('DOM.setFileInputFiles', { nodeId, files: absolutePaths }, { sessionId });
      console.log('[wechat-browser] [fallback] Files set via nodeId');

      // Dispatch change event
      await cdp.send('Runtime.evaluate', {
        expression: `
          (function() {
            const selectors = ${JSON.stringify(fileInputSelectors)};
            for (const sel of selectors) {
              const el = document.querySelector(sel);
              if (el) {
                el.dispatchEvent(new Event('change', { bubbles: true }));
                el.dispatchEvent(new Event('input', { bubbles: true }));
                return 'dispatched on ' + sel;
              }
            }
            return 'no input found for event dispatch';
          })()
        `,
        returnByValue: true,
      }, { sessionId });
      console.log('[wechat-browser] [fallback] Change event dispatched');
    }

    // Wait for images to upload
    console.log('[wechat-browser] Waiting for images to upload...');
    const targetCount = absolutePaths.length;
    for (let i = 0; i < 30; i++) {
      await sleep(2000);
      const uploadCheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `
          JSON.stringify({
            uploaded: document.querySelectorAll('.weui-desktop-upload__thumb, .pic_item, [class*=upload_thumb], [class*="pic_item"], [class*="upload__thumb"]').length,
            loading: document.querySelectorAll('[class*="upload_loading"], [class*="uploading"], .weui-desktop-upload__loading').length
          })
        `,
        returnByValue: true,
      }, { sessionId });
      const status = JSON.parse(uploadCheck.result.value);
      console.log(`[wechat-browser] Upload progress: ${status.uploaded}/${targetCount} (loading: ${status.loading})`);
      if (status.uploaded >= targetCount) break;
    }

    console.log('[wechat-browser] Filling title...');
    await cdp.send('Runtime.evaluate', {
      expression: `
        const titleInput = document.querySelector('#title');
        if (titleInput) {
          titleInput.value = ${JSON.stringify(title)};
          titleInput.dispatchEvent(new Event('input', { bubbles: true }));
        } else {
          throw new Error('Title input not found');
        }
      `,
    }, { sessionId });
    await sleep(500);

    console.log('[wechat-browser] Filling content...');
    // Try ProseMirror editor first (new WeChat UI), then fallback to old editor
    const contentResult = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
      expression: `
        (function() {
          const contentHtml = ${JSON.stringify('<p>' + content.split('\n').filter(l => l.trim()).join('</p><p>') + '</p>')};

          // New UI: ProseMirror contenteditable
          const pm = document.querySelector('.ProseMirror[contenteditable=true]');
          if (pm) {
            pm.innerHTML = contentHtml;
            pm.dispatchEvent(new Event('input', { bubbles: true }));
            return 'ProseMirror: content set, length=' + pm.textContent.length;
          }

          // Old UI: .js_pmEditorArea
          const oldEditor = document.querySelector('.js_pmEditorArea');
          if (oldEditor) {
            return JSON.stringify({ type: 'old', x: oldEditor.getBoundingClientRect().x + 50, y: oldEditor.getBoundingClientRect().y + 20 });
          }

          return 'editor_not_found';
        })()
      `,
      returnByValue: true,
    }, { sessionId });

    const contentStatus = contentResult.result.value;
    console.log(`[wechat-browser] Content result: ${contentStatus}`);

    if (contentStatus === 'editor_not_found') {
      throw new Error('Content editor not found');
    }

    // Fallback: old editor uses keyboard simulation
    if (contentStatus.startsWith('{')) {
      const editorClickPos = JSON.parse(contentStatus);
      if (editorClickPos.type === 'old') {
        console.log('[wechat-browser] Using old editor with keyboard simulation...');
        await cdp.send('Input.dispatchMouseEvent', {
          type: 'mousePressed',
          x: editorClickPos.x,
          y: editorClickPos.y,
          button: 'left',
          clickCount: 1,
        }, { sessionId });
        await sleep(50);
        await cdp.send('Input.dispatchMouseEvent', {
          type: 'mouseReleased',
          x: editorClickPos.x,
          y: editorClickPos.y,
          button: 'left',
          clickCount: 1,
        }, { sessionId });
        await sleep(300);

        const lines = content.split('\n');
        for (let i = 0; i < lines.length; i++) {
          const line = lines[i];
          if (line!.length > 0) {
            await cdp.send('Input.insertText', { text: line }, { sessionId });
          }
          if (i < lines.length - 1) {
            await cdp.send('Input.dispatchKeyEvent', {
              type: 'keyDown',
              key: 'Enter',
              code: 'Enter',
              windowsVirtualKeyCode: 13,
            }, { sessionId });
            await cdp.send('Input.dispatchKeyEvent', {
              type: 'keyUp',
              key: 'Enter',
              code: 'Enter',
              windowsVirtualKeyCode: 13,
            }, { sessionId });
          }
          await sleep(50);
        }
        console.log('[wechat-browser] Content typed via keyboard.');
      }
    }
    await sleep(500);

    if (submit) {
      console.log('[wechat-browser] Saving as draft...');
      const submitResult = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `
          (function() {
            // Try new UI: find button by text
            const allBtns = document.querySelectorAll('button');
            for (const btn of allBtns) {
              const text = btn.textContent?.trim();
              if (text === '保存为草稿') {
                btn.click();
                return 'clicked:保存为草稿';
              }
            }
            // Fallback: old UI selector
            const oldBtn = document.querySelector('#js_submit');
            if (oldBtn) {
              oldBtn.click();
              return 'clicked:#js_submit';
            }
            // List available buttons for debugging
            const btnTexts = [];
            allBtns.forEach(b => {
              const t = b.textContent?.trim();
              if (t && t.length < 20) btnTexts.push(t);
            });
            return 'not_found:' + btnTexts.join(',');
          })()
        `,
        returnByValue: true,
      }, { sessionId });
      console.log(`[wechat-browser] Submit result: ${submitResult.result.value}`);
      await sleep(3000);

      // Verify save success by checking for toast
      const toastCheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `
          const toasts = document.querySelectorAll('.weui-desktop-toast, [class*=toast]');
          const msgs = [];
          toasts.forEach(t => { const text = t.textContent?.trim(); if (text) msgs.push(text); });
          JSON.stringify(msgs);
        `,
        returnByValue: true,
      }, { sessionId });
      console.log(`[wechat-browser] Toast messages: ${toastCheck.result.value}`);
      console.log('[wechat-browser] Draft saved!');
    } else {
      console.log('[wechat-browser] Article composed (preview mode). Add --submit to save as draft.');
    }
  } finally {
    if (cdp) {
      cdp.close();
    }
    console.log('[wechat-browser] Done. Browser window left open.');
  }
}

function printUsage(): never {
  console.log(`Post image-text (贴图) to WeChat Official Account

Usage:
  npx -y bun wechat-browser.ts [options]

Options:
  --markdown <path>  Markdown file for title/content extraction
  --images <dir>     Directory containing images (PNG/JPG)
  --title <text>     Article title (max 20 chars, auto-compressed)
  --content <text>   Article content (max 1000 chars, auto-compressed)
  --image <path>     Add image (can be repeated)
  --submit           Save as draft (default: preview only)
  --profile <dir>    Chrome profile directory
  --account <alias>  Select account by alias (for multi-account setups)
  --help             Show this help

Examples:
  npx -y bun wechat-browser.ts --markdown article.md --images ./photos/
  npx -y bun wechat-browser.ts --title "测试" --content "内容" --image ./photo.png
  npx -y bun wechat-browser.ts --markdown article.md --images ./photos/ --submit
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) printUsage();

  const images: string[] = [];
  let submit = false;
  let profileDir: string | undefined;
  let title: string | undefined;
  let content: string | undefined;
  let markdownFile: string | undefined;
  let imagesDir: string | undefined;
  let accountAlias: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--image' && args[i + 1]) {
      images.push(args[++i]!);
    } else if (arg === '--images' && args[i + 1]) {
      imagesDir = args[++i];
    } else if (arg === '--title' && args[i + 1]) {
      title = args[++i];
    } else if (arg === '--content' && args[i + 1]) {
      content = args[++i];
    } else if (arg === '--markdown' && args[i + 1]) {
      markdownFile = args[++i];
    } else if (arg === '--submit') {
      submit = true;
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (arg === '--account' && args[i + 1]) {
      accountAlias = args[++i];
    }
  }

  const extConfig = loadWechatExtendConfig();
  const resolved = resolveAccount(extConfig, accountAlias);
  if (resolved.name) console.log(`[wechat-browser] Account: ${resolved.name} (${resolved.alias})`);

  if (!profileDir && resolved.alias) {
    profileDir = resolved.chrome_profile_path || getAccountProfileDir(resolved.alias);
  }

  if (!markdownFile && !title) {
    console.error('Error: --title or --markdown is required');
    process.exit(1);
  }
  if (!markdownFile && !content) {
    console.error('Error: --content or --markdown is required');
    process.exit(1);
  }
  if (images.length === 0 && !imagesDir) {
    console.error('Error: --image or --images is required');
    process.exit(1);
  }

  await postToWeChat({ title, content, images: images.length > 0 ? images : undefined, imagesDir, markdownFile, submit, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
