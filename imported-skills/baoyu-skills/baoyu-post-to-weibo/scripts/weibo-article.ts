import fs from 'node:fs';
import { mkdir, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {
  CdpConnection,
  copyHtmlToClipboard,
  copyImageToClipboard,
  findChromeExecutable,
  findExistingChromeDebugPort,
  getDefaultProfileDir,
  launchChrome,
  pasteFromClipboard,
  sleep,
  waitForChromeDebugPort,
} from './weibo-utils.js';
import { parseMarkdown } from './md-to-html.js';

const WEIBO_ARTICLE_URL = 'https://card.weibo.com/article/v3/editor';

const TITLE_MAX_LENGTH = 32;
const SUMMARY_MAX_LENGTH = 44;

interface ArticleOptions {
  markdownPath: string;
  coverImage?: string;
  title?: string;
  summary?: string;
  profileDir?: string;
  chromePath?: string;
}

export async function publishArticle(options: ArticleOptions): Promise<void> {
  const { markdownPath, profileDir = getDefaultProfileDir() } = options;

  console.log('[weibo-article] Parsing markdown...');
  const parsed = await parseMarkdown(markdownPath, {
    title: options.title,
    coverImage: options.coverImage,
  });

  let title = parsed.title;
  if (title.length > TITLE_MAX_LENGTH) {
    console.warn(`[weibo-article] Title exceeds ${TITLE_MAX_LENGTH} chars (${title.length}), truncating at word boundary...`);
    const truncated = title.slice(0, TITLE_MAX_LENGTH);
    const breakChars = ['：', '，', '、', '。', ' ', '—', '→', '｜', '|', '-'];
    let lastBreak = -1;
    for (const ch of breakChars) {
      const idx = truncated.lastIndexOf(ch);
      if (idx > lastBreak) lastBreak = idx;
    }
    title = lastBreak > TITLE_MAX_LENGTH * 0.4
      ? truncated.slice(0, lastBreak).replace(/[\s→—\-|｜：，]+$/, '')
      : truncated;
  }

  let summary = options.summary || parsed.summary || '';
  if (summary.length > SUMMARY_MAX_LENGTH) {
    console.warn(`[weibo-article] Summary exceeds ${SUMMARY_MAX_LENGTH} chars (${summary.length}), regenerating from content...`);
    summary = parsed.shortSummary || summary.slice(0, SUMMARY_MAX_LENGTH - 1) + '\u2026';
  }

  console.log(`[weibo-article] Title (${title.length}/${TITLE_MAX_LENGTH}): ${title}`);
  console.log(`[weibo-article] Summary (${summary.length}/${SUMMARY_MAX_LENGTH}): ${summary}`);
  console.log(`[weibo-article] Cover: ${parsed.coverImage ?? 'none'}`);
  console.log(`[weibo-article] Content images: ${parsed.contentImages.length}`);

  const htmlPath = path.join(os.tmpdir(), 'weibo-article-content.html');
  await writeFile(htmlPath, parsed.html, 'utf-8');
  console.log(`[weibo-article] HTML saved to: ${htmlPath}`);

  await mkdir(profileDir, { recursive: true });

  // Try reusing an existing Chrome instance with the same profile
  const existingPort = await findExistingChromeDebugPort(profileDir);
  let port: number;

  if (existingPort) {
    console.log(`[weibo-article] Found existing Chrome on port ${existingPort}, reusing...`);
    port = existingPort;
  } else {
    const chromePath = findChromeExecutable(options.chromePath);
    if (!chromePath) throw new Error('Chrome not found. Set WEIBO_BROWSER_CHROME_PATH env var.');

    port = await launchChrome(WEIBO_ARTICLE_URL, profileDir, chromePath);
  }

  let cdp: CdpConnection | null = null;

  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000);
    cdp = await CdpConnection.connect(wsUrl, 30_000, { defaultTimeoutMs: 60_000 });

    const targets = await cdp.send<{ targetInfos: Array<{ targetId: string; url: string; type: string }> }>('Target.getTargets');
    // Always create a fresh tab for the article editor
    const { targetId } = await cdp.send<{ targetId: string }>('Target.createTarget', { url: WEIBO_ARTICLE_URL });
    const pageTarget = { targetId, url: WEIBO_ARTICLE_URL, type: 'page' };
    console.log('[weibo-article] Opened article editor in new tab');

    const { sessionId } = await cdp.send<{ sessionId: string }>('Target.attachToTarget', { targetId: pageTarget.targetId, flatten: true });

    await cdp.send('Page.enable', {}, { sessionId });
    await cdp.send('Runtime.enable', {}, { sessionId });
    await cdp.send('DOM.enable', {}, { sessionId });

    console.log('[weibo-article] Waiting for article editor page...');
    await sleep(3000);

    const waitForElement = async (expression: string, timeoutMs = 60_000): Promise<boolean> => {
      const start = Date.now();
      while (Date.now() - start < timeoutMs) {
        const result = await cdp!.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression,
          returnByValue: true,
        }, { sessionId });
        if (result.result.value) return true;
        await sleep(500);
      }
      return false;
    };

    // Step 1: Find and click "写文章" button
    console.log('[weibo-article] Looking for "写文章" button...');
    const writeButtonFound = await waitForElement(`
      !!Array.from(document.querySelectorAll('button, a, div[role="button"]')).find(el => el.textContent?.trim() === '写文章')
    `, 15_000);

    if (writeButtonFound) {
      console.log('[weibo-article] Clicking "写文章" button...');
      await cdp.send('Runtime.evaluate', {
        expression: `
          const btn = Array.from(document.querySelectorAll('button, a, div[role="button"]')).find(el => el.textContent?.trim() === '写文章');
          if (btn) btn.click();
        `,
      }, { sessionId });
      await sleep(1000);

      // Wait for title input to become editable (not readonly)
      console.log('[weibo-article] Waiting for editor to become editable...');
      const editable = await waitForElement(`
        (() => {
          const el = document.querySelector('textarea[placeholder="请输入标题"]');
          return el && !el.readOnly && !el.disabled;
        })()
      `, 15_000);

      if (!editable) {
        console.warn('[weibo-article] Title input still readonly after waiting. Proceeding anyway...');
      }
    } else {
      // Maybe we're already on the editor page
      console.log('[weibo-article] "写文章" button not found, checking if editor is already loaded...');
      const editorExists = await waitForElement(`
        !!document.querySelector('textarea[placeholder="请输入标题"]')
      `, 10_000);
      if (!editorExists) {
        throw new Error('Weibo article editor not found. Please ensure you are logged in.');
      }
    }

    // Step 2: Fill title
    if (title) {
      console.log('[weibo-article] Filling title...');

      // Check if title input exists
      const titleExists = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
        expression: `!!document.querySelector('textarea[placeholder="请输入标题"]')`,
        returnByValue: true,
      }, { sessionId });

      if (!titleExists.result.value) {
        console.error('[weibo-article] Title input NOT found: textarea[placeholder="请输入标题"]');
      } else {
        console.log('[weibo-article] Title input found');

        // Focus and use Input.insertText via CDP (more reliable for React/Vue controlled inputs)
        await cdp.send('Runtime.evaluate', {
          expression: `(() => {
            const el = document.querySelector('textarea[placeholder="请输入标题"]');
            if (el) { el.focus(); el.value = ''; }
          })()`,
        }, { sessionId });
        await sleep(200);

        await cdp.send('Input.insertText', { text: title }, { sessionId });
        await sleep(500);

        // Verify title was entered
        const titleCheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
          expression: `document.querySelector('textarea[placeholder="请输入标题"]')?.value || ''`,
          returnByValue: true,
        }, { sessionId });

        if (titleCheck.result.value === title) {
          console.log(`[weibo-article] Title verified: "${titleCheck.result.value}"`);
        } else if (titleCheck.result.value.length > 0) {
          console.warn(`[weibo-article] Title partially entered: "${titleCheck.result.value}" (expected: "${title}")`);
        } else {
          console.warn('[weibo-article] Title input appears empty after insertion, trying execCommand fallback...');
          await cdp.send('Runtime.evaluate', {
            expression: `(() => {
              const el = document.querySelector('textarea[placeholder="请输入标题"]');
              if (el) { el.focus(); document.execCommand('insertText', false, ${JSON.stringify(title)}); }
            })()`,
          }, { sessionId });
          await sleep(300);

          const titleRecheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `document.querySelector('textarea[placeholder="请输入标题"]')?.value || ''`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] Title after fallback: "${titleRecheck.result.value}"`);
        }
      }
    }

    // Step 3: Fill summary (导语)
    if (summary) {
      console.log('[weibo-article] Filling summary...');

      const summaryExists = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
        expression: `!!document.querySelector('textarea[placeholder="导语（选填）"]')`,
        returnByValue: true,
      }, { sessionId });

      if (!summaryExists.result.value) {
        console.error('[weibo-article] Summary input NOT found: textarea[placeholder="导语（选填）"]');
      } else {
        console.log('[weibo-article] Summary input found');

        await cdp.send('Runtime.evaluate', {
          expression: `(() => {
            const el = document.querySelector('textarea[placeholder="导语（选填）"]');
            if (el) { el.focus(); el.value = ''; }
          })()`,
        }, { sessionId });
        await sleep(200);

        await cdp.send('Input.insertText', { text: summary }, { sessionId });
        await sleep(500);

        // Verify summary was entered
        const summaryCheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
          expression: `document.querySelector('textarea[placeholder="导语（选填）"]')?.value || ''`,
          returnByValue: true,
        }, { sessionId });

        if (summaryCheck.result.value === summary) {
          console.log(`[weibo-article] Summary verified: "${summaryCheck.result.value}"`);
        } else if (summaryCheck.result.value.length > 0) {
          console.warn(`[weibo-article] Summary partially entered: "${summaryCheck.result.value}"`);
        } else {
          console.warn('[weibo-article] Summary input appears empty, trying execCommand fallback...');
          await cdp.send('Runtime.evaluate', {
            expression: `(() => {
              const el = document.querySelector('textarea[placeholder="导语（选填）"]');
              if (el) { el.focus(); document.execCommand('insertText', false, ${JSON.stringify(summary)}); }
            })()`,
          }, { sessionId });
          await sleep(300);

          const summaryRecheck = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `document.querySelector('textarea[placeholder="导语（选填）"]')?.value || ''`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] Summary after fallback: "${summaryRecheck.result.value}"`);
        }
      }
    }

    // Step 4: Insert HTML content into ProseMirror editor
    console.log('[weibo-article] Inserting content...');

    const htmlContent = fs.readFileSync(htmlPath, 'utf-8');

    // Check if ProseMirror editor exists
    const editorExists2 = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
      expression: `(() => {
        const el = document.querySelector('div[contenteditable="true"]');
        if (!el) return 'NOT_FOUND';
        return 'class=' + el.className;
      })()`,
      returnByValue: true,
    }, { sessionId });

    if (editorExists2.result.value === 'NOT_FOUND') {
      console.error('[weibo-article] ProseMirror editor NOT found: div[contenteditable="true"]');
    } else {
      console.log(`[weibo-article] Editor found (${editorExists2.result.value})`);
    }

    // Focus ProseMirror editor
    await cdp.send('Runtime.evaluate', {
      expression: `(() => {
        const editor = document.querySelector('div[contenteditable="true"]');
        if (editor) { editor.focus(); editor.click(); }
      })()`,
    }, { sessionId });
    await sleep(300);

    // Method 1: Copy HTML to system clipboard, then real paste keystroke
    console.log('[weibo-article] Copying HTML to clipboard and pasting...');
    copyHtmlToClipboard(htmlPath);
    await sleep(500);

    // Focus editor again before paste
    await cdp.send('Runtime.evaluate', {
      expression: `document.querySelector('div[contenteditable="true"]')?.focus()`,
    }, { sessionId });
    await sleep(200);

    pasteFromClipboard('Google Chrome', 5, 500);
    await sleep(2000);

    // Check if content was inserted
    const contentCheck = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
      expression: `document.querySelector('div[contenteditable="true"]')?.innerText?.length || 0`,
      returnByValue: true,
    }, { sessionId });

    if (contentCheck.result.value > 50) {
      console.log(`[weibo-article] Content inserted via clipboard paste (${contentCheck.result.value} chars)`);
    } else {
      console.log(`[weibo-article] Clipboard paste got ${contentCheck.result.value} chars, trying DataTransfer paste event...`);

      // Method 2: Simulate paste event with HTML data
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const editor = document.querySelector('div[contenteditable="true"]');
          if (!editor) return false;
          editor.focus();

          const html = ${JSON.stringify(htmlContent)};
          const dt = new DataTransfer();
          dt.setData('text/html', html);
          dt.setData('text/plain', html.replace(/<[^>]*>/g, ''));

          const pasteEvent = new ClipboardEvent('paste', {
            bubbles: true, cancelable: true, clipboardData: dt
          });
          editor.dispatchEvent(pasteEvent);
          return true;
        })()`,
        returnByValue: true,
      }, { sessionId });
      await sleep(1000);

      const check2 = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelector('div[contenteditable="true"]')?.innerText?.length || 0`,
        returnByValue: true,
      }, { sessionId });

      if (check2.result.value > 50) {
        console.log(`[weibo-article] Content inserted via DataTransfer (${check2.result.value} chars)`);
      } else {
        console.log(`[weibo-article] DataTransfer got ${check2.result.value} chars, trying insertHTML...`);

        // Method 3: execCommand insertHTML
        await cdp.send('Runtime.evaluate', {
          expression: `(() => {
            const editor = document.querySelector('div[contenteditable="true"]');
            if (!editor) return false;
            editor.focus();
            document.execCommand('insertHTML', false, ${JSON.stringify(htmlContent)});
            return true;
          })()`,
        }, { sessionId });
        await sleep(1000);

        const check3 = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
          expression: `document.querySelector('div[contenteditable="true"]')?.innerText?.length || 0`,
          returnByValue: true,
        }, { sessionId });

        if (check3.result.value > 50) {
          console.log(`[weibo-article] Content inserted via execCommand (${check3.result.value} chars)`);
        } else {
          console.error('[weibo-article] All auto-insert methods failed. HTML is on clipboard - please paste manually (Cmd+V)');
          console.log('[weibo-article] Waiting 30s for manual paste...');
          await sleep(30_000);
        }
      }
    }

    // Step 5: Insert content images
    if (parsed.contentImages.length > 0) {
      console.log('[weibo-article] Inserting content images...');

      const editorContent = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `document.querySelector('div[contenteditable="true"]')?.innerText || ''`,
        returnByValue: true,
      }, { sessionId });

      console.log('[weibo-article] Checking for placeholders in content...');
      let placeholderCount = 0;
      for (const img of parsed.contentImages) {
        const regex = new RegExp(img.placeholder + '(?!\\d)');
        if (regex.test(editorContent.result.value)) {
          console.log(`[weibo-article] Found: ${img.placeholder}`);
          placeholderCount++;
        } else {
          console.log(`[weibo-article] NOT found: ${img.placeholder}`);
        }
      }
      console.log(`[weibo-article] ${placeholderCount}/${parsed.contentImages.length} placeholders found in editor`);

      const getPlaceholderIndex = (placeholder: string): number => {
        const match = placeholder.match(/WBIMGPH_(\d+)/);
        return match ? Number(match[1]) : Number.POSITIVE_INFINITY;
      };
      const sortedImages = [...parsed.contentImages].sort(
        (a, b) => getPlaceholderIndex(a.placeholder) - getPlaceholderIndex(b.placeholder),
      );

      for (let i = 0; i < sortedImages.length; i++) {
        const img = sortedImages[i]!;
        console.log(`[weibo-article] [${i + 1}/${sortedImages.length}] Inserting image at placeholder: ${img.placeholder}`);

        const selectPlaceholder = async (maxRetries = 3): Promise<boolean> => {
          for (let attempt = 1; attempt <= maxRetries; attempt++) {
            await cdp!.send('Runtime.evaluate', {
              expression: `(() => {
                const editor = document.querySelector('div[contenteditable="true"]');
                if (!editor) return false;

                const placeholder = ${JSON.stringify(img.placeholder)};

                const walker = document.createTreeWalker(editor, NodeFilter.SHOW_TEXT, null, false);
                let node;

                while ((node = walker.nextNode())) {
                  const text = node.textContent || '';
                  let searchStart = 0;
                  let idx;
                  while ((idx = text.indexOf(placeholder, searchStart)) !== -1) {
                    const afterIdx = idx + placeholder.length;
                    const charAfter = text[afterIdx];
                    if (charAfter === undefined || !/\\d/.test(charAfter)) {
                      const parentElement = node.parentElement;
                      if (parentElement) {
                        parentElement.scrollIntoView({ behavior: 'instant', block: 'center' });
                      }

                      const range = document.createRange();
                      range.setStart(node, idx);
                      range.setEnd(node, idx + placeholder.length);
                      const sel = window.getSelection();
                      sel.removeAllRanges();
                      sel.addRange(range);
                      return true;
                    }
                    searchStart = afterIdx;
                  }
                }
                return false;
              })()`,
            }, { sessionId });

            await sleep(800);

            const selectionCheck = await cdp!.send<{ result: { value: string } }>('Runtime.evaluate', {
              expression: `window.getSelection()?.toString() || ''`,
              returnByValue: true,
            }, { sessionId });

            const selectedText = selectionCheck.result.value.trim();
            if (selectedText === img.placeholder) {
              console.log(`[weibo-article] Selection verified: "${selectedText}"`);
              return true;
            }

            if (attempt < maxRetries) {
              console.log(`[weibo-article] Selection attempt ${attempt} got "${selectedText}", retrying...`);
              await sleep(500);
            } else {
              console.warn(`[weibo-article] Selection failed after ${maxRetries} attempts, got: "${selectedText}"`);
            }
          }
          return false;
        };

        // Step A: Copy image to clipboard first (slow due to Swift compilation)
        console.log(`[weibo-article] Copying image to clipboard: ${path.basename(img.localPath)}`);
        if (!copyImageToClipboard(img.localPath)) {
          console.warn(`[weibo-article] Failed to copy image to clipboard`);
          continue;
        }
        await sleep(500);

        // Step B: Select placeholder text (paste will replace the selection)
        const selected = await selectPlaceholder(3);
        if (!selected) {
          console.warn(`[weibo-article] Skipping image - could not select placeholder: ${img.placeholder}`);
          continue;
        }

        // Step C: Delete selected placeholder via Backspace (ProseMirror-compatible)
        console.log(`[weibo-article] Deleting placeholder via Backspace...`);
        await cdp.send('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Backspace', code: 'Backspace', windowsVirtualKeyCode: 8 }, { sessionId });
        await cdp.send('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Backspace', code: 'Backspace', windowsVirtualKeyCode: 8 }, { sessionId });
        await sleep(500);

        // Verify placeholder was deleted
        const placeholderGone = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
          expression: `(() => {
            const editor = document.querySelector('div[contenteditable="true"]');
            if (!editor) return true;
            const placeholder = ${JSON.stringify(img.placeholder)};
            const regex = new RegExp(placeholder + '(?!\\\\d)');
            return !regex.test(editor.innerText);
          })()`,
          returnByValue: true,
        }, { sessionId });

        if (placeholderGone.result.value) {
          console.log(`[weibo-article] Placeholder deleted`);
        } else {
          console.warn(`[weibo-article] Placeholder may still exist, trying execCommand delete...`);
          // Re-select and delete via execCommand
          await selectPlaceholder(1);
          await cdp.send('Runtime.evaluate', {
            expression: `document.execCommand('delete')`,
          }, { sessionId });
          await sleep(300);
        }

        // Step D: Focus editor and paste image
        await cdp.send('Runtime.evaluate', {
          expression: `document.querySelector('div[contenteditable="true"]')?.focus()`,
        }, { sessionId });
        await sleep(200);

        // Count images before paste
        const imgCountBefore = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
          expression: `document.querySelectorAll('div[contenteditable="true"] img').length`,
          returnByValue: true,
        }, { sessionId });

        // Paste image at cursor position (where placeholder was)
        console.log(`[weibo-article] Pasting image...`);
        if (pasteFromClipboard('Google Chrome', 5, 1000)) {
          console.log(`[weibo-article] Paste keystroke sent for: ${path.basename(img.localPath)}`);
        } else {
          console.warn(`[weibo-article] Failed to paste image after retries`);
        }

        // Verify image appeared in editor
        console.log(`[weibo-article] Verifying image insertion...`);
        const expectedImgCount = imgCountBefore.result.value + 1;
        let imgInserted = false;
        const imgWaitStart = Date.now();
        while (Date.now() - imgWaitStart < 15_000) {
          const r = await cdp!.send<{ result: { value: number } }>('Runtime.evaluate', {
            expression: `document.querySelectorAll('div[contenteditable="true"] img').length`,
            returnByValue: true,
          }, { sessionId });
          if (r.result.value >= expectedImgCount) {
            imgInserted = true;
            break;
          }
          await sleep(1000);
        }

        if (imgInserted) {
          console.log(`[weibo-article] Image insertion verified (${expectedImgCount} image(s) in editor)`);

          await sleep(1000);

          // Clean up extra empty <p> before the image (Tiptap invisible chars + <br>)
          console.log(`[weibo-article] Cleaning up empty lines around image...`);
          await cdp!.send('Runtime.evaluate', {
            expression: `(() => {
              const editor = document.querySelector('div[contenteditable="true"]');
              if (!editor) return;
              const imageViews = editor.querySelectorAll('.image-view__body');
              const lastView = imageViews[imageViews.length - 1];
              const imgBlock = lastView?.closest('div[data-type], .ProseMirror > *') || lastView?.parentElement;
              if (!imgBlock) return;
              let prev = imgBlock.previousElementSibling;
              let removed = 0;
              while (prev) {
                const tag = prev.tagName?.toLowerCase();
                const text = prev.textContent?.replace(/\\u200b/g, '').trim();
                const hasOnlyBreaks = prev.querySelectorAll('br, .Tiptap-invisible-character').length > 0;
                if ((tag === 'p' || tag === 'div') && (!text || text === '') && hasOnlyBreaks) {
                  const toRemove = prev;
                  prev = prev.previousElementSibling;
                  toRemove.remove();
                  removed++;
                  if (removed >= 2) break;
                } else {
                  break;
                }
              }
            })()`,
          }, { sessionId });

          // Fill image caption if alt text exists
          const altText = img.alt?.trim();
          if (altText) {
            console.log(`[weibo-article] Setting image caption: "${altText}"`);
            const captionResult = await cdp!.send<{ result: { value: string } }>('Runtime.evaluate', {
              expression: `(() => {
                const editor = document.querySelector('div[contenteditable="true"]');
                if (!editor) return 'no_editor';
                const views = editor.querySelectorAll('.image-view__body');
                const lastView = views[views.length - 1];
                if (!lastView) return 'no_view';
                const captionSpan = lastView.querySelector('.image-view__caption span[data-node-view-content]');
                if (!captionSpan) return 'no_caption_span';
                captionSpan.focus();
                captionSpan.textContent = ${JSON.stringify(altText)};
                captionSpan.dispatchEvent(new Event('input', { bubbles: true }));
                return 'set';
              })()`,
              returnByValue: true,
            }, { sessionId });
            console.log(`[weibo-article] Caption result: ${captionResult.result.value}`);
            await sleep(300);
          }
        } else {
          console.warn(`[weibo-article] Image insertion not detected after 15s`);
          if (i === 0) {
            console.error('[weibo-article] First image paste failed. Check Accessibility permissions for your terminal app.');
          }
        }

        // Wait for editor to stabilize
        await sleep(2000);
      }

      console.log('[weibo-article] All images processed.');

      // Clean up extra empty <p> before images (Tiptap invisible chars + <br>)
      console.log('[weibo-article] Cleaning up extra line breaks before images...');
      const cleanupResult = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `(() => {
          const editor = document.querySelector('div[contenteditable="true"]');
          if (!editor) return 0;
          let removed = 0;
          const imageViews = editor.querySelectorAll('.image-view__body');
          for (const view of imageViews) {
            const imgBlock = view.closest('div[data-type], .ProseMirror > *') || view.parentElement;
            if (!imgBlock) continue;
            let prev = imgBlock.previousElementSibling;
            while (prev) {
              const tag = prev.tagName?.toLowerCase();
              const text = prev.textContent?.replace(/\\u200b/g, '').trim();
              const hasOnlyBreaks = prev.querySelectorAll('br, .Tiptap-invisible-character').length > 0;
              if ((tag === 'p' || tag === 'div') && (!text || text === '') && hasOnlyBreaks) {
                const toRemove = prev;
                prev = toRemove.previousElementSibling;
                toRemove.remove();
                removed++;
              } else {
                break;
              }
            }
          }
          return removed;
        })()`,
        returnByValue: true,
      }, { sessionId });
      if (cleanupResult.result.value > 0) {
        console.log(`[weibo-article] Removed ${cleanupResult.result.value} extra line break(s) before images.`);
      }
      await sleep(500);

      // Final verification
      console.log('[weibo-article] Running post-composition verification...');
      const finalEditorContent = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
        expression: `document.querySelector('div[contenteditable="true"]')?.innerText || ''`,
        returnByValue: true,
      }, { sessionId });

      const remainingPlaceholders: string[] = [];
      for (const img of parsed.contentImages) {
        const regex = new RegExp(img.placeholder + '(?!\\d)');
        if (regex.test(finalEditorContent.result.value)) {
          remainingPlaceholders.push(img.placeholder);
        }
      }

      const finalImgCount = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelectorAll('div[contenteditable="true"] img').length`,
        returnByValue: true,
      }, { sessionId });

      const expectedCount = parsed.contentImages.length;
      const actualCount = finalImgCount.result.value;

      if (remainingPlaceholders.length > 0 || actualCount < expectedCount) {
        console.warn('[weibo-article] POST-COMPOSITION CHECK FAILED:');
        if (remainingPlaceholders.length > 0) {
          console.warn(`[weibo-article]   Remaining placeholders: ${remainingPlaceholders.join(', ')}`);
        }
        if (actualCount < expectedCount) {
          console.warn(`[weibo-article]   Image count: expected ${expectedCount}, found ${actualCount}`);
        }
        console.warn('[weibo-article]   Please check the article before publishing.');
      } else {
        console.log(`[weibo-article] Verification passed: ${actualCount} image(s), no remaining placeholders.`);
      }
    }

    // Step 6: Set cover image
    const coverImagePath = parsed.coverImage;
    if (coverImagePath && fs.existsSync(coverImagePath)) {
      console.log(`[weibo-article] Setting cover image: ${path.basename(coverImagePath)}`);

      // Scroll to top first
      await cdp.send('Runtime.evaluate', {
        expression: `window.scrollTo(0, 0)`,
      }, { sessionId });
      await sleep(500);

      // 1. Click cover area to open dialog (cover-empty or cover-preview)
      // First scroll element into view
      await cdp.send('Runtime.evaluate', {
        expression: `(() => {
          const el = document.querySelector('.cover-empty') || document.querySelector('.cover-preview');
          if (el) { el.scrollIntoView({ block: 'center' }); return true; }
          return false;
        })()`,
        returnByValue: true,
      }, { sessionId });
      await sleep(1000);

      // Then get coordinates after scroll settles
      const coverBtnPos = await cdp.send<{ result: { value: { x: number; y: number } | null } }>('Runtime.evaluate', {
        expression: `(() => {
          const el = document.querySelector('.cover-empty') || document.querySelector('.cover-preview');
          if (el) {
            const rect = el.getBoundingClientRect();
            return { x: rect.x + rect.width / 2, y: rect.y + rect.height / 2 };
          }
          return null;
        })()`,
        returnByValue: true,
      }, { sessionId });

      if (coverBtnPos.result.value) {
        const { x, y } = coverBtnPos.result.value;
        console.log(`[weibo-article] "设置文章封面" at (${x}, ${y}), clicking...`);
        await cdp.send('Input.dispatchMouseEvent', { type: 'mousePressed', x, y, button: 'left', clickCount: 1 }, { sessionId });
        await sleep(100);
        await cdp.send('Input.dispatchMouseEvent', { type: 'mouseReleased', x, y, button: 'left', clickCount: 1 }, { sessionId });
      } else {
        console.warn('[weibo-article] "设置文章封面" (.cover-empty) not found');
      }
      await sleep(2000);

      // Wait for dialog to appear
      const dialogReady = await waitForElement(`!!document.querySelector('.n-dialog')`, 10_000);
      console.log(`[weibo-article] Dialog appeared: ${dialogReady}`);

      // 2. Click "图片库" tab
      const tabClicked = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
        expression: `(() => {
          const tabs = document.querySelectorAll('.n-tabs-tab');
          for (const t of tabs) {
            if (t.querySelector('.n-tabs-tab__label span')?.textContent?.trim() === '图片库') { t.click(); return true; }
          }
          return false;
        })()`,
        returnByValue: true,
      }, { sessionId });
      console.log(`[weibo-article] "图片库" tab clicked: ${tabClicked.result.value}`);
      await sleep(1000);

      // 3. Count existing items before upload
      const itemCountBefore = await cdp.send<{ result: { value: number } }>('Runtime.evaluate', {
        expression: `document.querySelectorAll('.image-list .image-item').length`,
        returnByValue: true,
      }, { sessionId });
      console.log(`[weibo-article] Items before upload: ${itemCountBefore.result.value}`);

      // 4. Upload via hidden file input
      console.log('[weibo-article] Uploading cover image via file input...');
      const absPath = path.resolve(coverImagePath);

      // Get DOM document root first, then find file input via DOM.querySelector
      const docRoot = await cdp.send<{ root: { nodeId: number } }>('DOM.getDocument', { depth: -1 }, { sessionId });
      const fileInputNodes = await cdp.send<{ nodeIds: number[] }>('DOM.querySelectorAll', {
        nodeId: docRoot.root.nodeId,
        selector: 'input[type="file"]',
      }, { sessionId });

      const fileInputNodeId = fileInputNodes.nodeIds?.[0];
      if (!fileInputNodeId) {
        console.warn('[weibo-article] File input not found, skipping cover image');
      } else {
        await cdp.send('DOM.setFileInputFiles', {
          nodeId: fileInputNodeId,
          files: [absPath],
        }, { sessionId });
        console.log('[weibo-article] File set on input, waiting for upload...');

        // 5. Wait for a new item to appear (item count increases)
        let uploadSuccess = false;
        const uploadStart = Date.now();
        while (Date.now() - uploadStart < 30_000) {
          const state = await cdp.send<{ result: { value: { count: number; firstSrc: string } } }>('Runtime.evaluate', {
            expression: `(() => {
              const items = document.querySelectorAll('.image-list .image-item');
              const first = items[0];
              const img = first?.querySelector('img');
              return { count: items.length, firstSrc: img?.src || '' };
            })()`,
            returnByValue: true,
          }, { sessionId });
          const { count, firstSrc } = state.result.value;
          if (count > itemCountBefore.result.value && firstSrc.startsWith('https://')) {
            console.log(`[weibo-article] New image uploaded (${count} items, src: https://...)`);
            uploadSuccess = true;
            break;
          }
          if (firstSrc.startsWith('blob:')) {
            console.log('[weibo-article] Cover image uploading (blob detected)...');
          }
          await sleep(1000);
        }

        if (!uploadSuccess) {
          // Fallback: check if first item has https (maybe count didn't change but image was replaced)
          const fallback = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `document.querySelector('.image-list .image-item img')?.src || ''`,
            returnByValue: true,
          }, { sessionId });
          if (fallback.result.value.startsWith('https://')) {
            console.log('[weibo-article] Cover image ready (fallback check)');
            uploadSuccess = true;
          } else {
            console.warn('[weibo-article] Cover image upload timed out after 30s');
          }
        }

        if (uploadSuccess) {
          // 6. Click first item to select it
          const clickResult = await cdp.send<{ result: { value: boolean } }>('Runtime.evaluate', {
            expression: `(() => {
              const item = document.querySelector('.image-list .image-item');
              if (item) { item.click(); return true; }
              return false;
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] First item clicked: ${clickResult.result.value}`);
          await sleep(500);

          // Verify selection
          const selected = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `(() => {
              const items = document.querySelectorAll('.image-list .image-item');
              const selectedIdx = Array.from(items).findIndex(i => i.classList.contains('is-selected'));
              return 'selected_index=' + selectedIdx + ' total=' + items.length;
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] Selection: ${selected.result.value}`);

          // 7. Click "下一步" in dialog (image selection → crop)
          const nextResult = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `(() => {
              const dialog = document.querySelector('.n-dialog');
              if (!dialog) return 'no_dialog';
              const buttons = dialog.querySelectorAll('.n-button');
              for (const b of buttons) {
                const text = b.querySelector('.n-button__content')?.textContent?.trim() || '';
                if (text === '下一步') { b.click(); return 'clicked'; }
              }
              return 'not_found';
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] "下一步" (select→crop): ${nextResult.result.value}`);
          await sleep(3000);

          // 8. Click "确定" in crop dialog
          // First check button state and dispatch full pointer event sequence
          const confirmInfo = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `(() => {
              const dialog = document.querySelector('.n-dialog');
              if (!dialog) return 'no_dialog';
              const buttons = dialog.querySelectorAll('.n-button');
              for (const b of buttons) {
                const text = b.querySelector('.n-button__content')?.textContent?.trim() || '';
                if (text === '确定' || text === '确认') {
                  const disabled = b.disabled || b.classList.contains('n-button--disabled');
                  const rect = b.getBoundingClientRect();
                  return 'found:' + text + ':disabled=' + disabled + ':y=' + rect.y + ':h=' + rect.height;
                }
              }
              const allTexts = Array.from(buttons).map(b => b.querySelector('.n-button__content')?.textContent?.trim() || '').join(',');
              return 'not_found:' + allTexts;
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] Confirm button info: ${confirmInfo.result.value}`);

          // Use full pointer event simulation via JS (not CDP Input.dispatchMouseEvent)
          const confirmClickResult = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `(() => {
              const dialog = document.querySelector('.n-dialog');
              if (!dialog) return 'no_dialog';
              const buttons = dialog.querySelectorAll('.n-button');
              for (const b of buttons) {
                const text = b.querySelector('.n-button__content')?.textContent?.trim() || '';
                if (text === '确定' || text === '确认') {
                  b.scrollIntoView({ block: 'center' });
                  const rect = b.getBoundingClientRect();
                  const cx = rect.x + rect.width / 2;
                  const cy = rect.y + rect.height / 2;
                  const opts = { bubbles: true, cancelable: true, clientX: cx, clientY: cy, button: 0 };
                  b.dispatchEvent(new PointerEvent('pointerdown', opts));
                  b.dispatchEvent(new MouseEvent('mousedown', opts));
                  b.dispatchEvent(new PointerEvent('pointerup', opts));
                  b.dispatchEvent(new MouseEvent('mouseup', opts));
                  b.dispatchEvent(new MouseEvent('click', opts));
                  return 'dispatched:' + text;
                }
              }
              return 'not_found';
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] Confirm click: ${confirmClickResult.result.value}`);
          await sleep(2000);

          // Check dialog state
          const afterConfirm = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `(() => {
              const dialog = document.querySelector('.n-dialog');
              if (!dialog) return 'closed';
              const buttons = dialog.querySelectorAll('.n-button');
              return 'open:' + Array.from(buttons).map(b => b.querySelector('.n-button__content')?.textContent?.trim() || '').join(',');
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] After confirm: ${afterConfirm.result.value}`);

          // If still open, try focusing the button and pressing Enter
          if (afterConfirm.result.value !== 'closed') {
            console.log('[weibo-article] Dialog still open, trying focus + Enter...');
            await cdp!.send('Runtime.evaluate', {
              expression: `(() => {
                const dialog = document.querySelector('.n-dialog');
                if (!dialog) return;
                const buttons = dialog.querySelectorAll('.n-button');
                for (const b of buttons) {
                  const text = b.querySelector('.n-button__content')?.textContent?.trim() || '';
                  if (text === '确定' || text === '确认') { b.focus(); return; }
                }
              })()`,
            }, { sessionId });
            await sleep(200);
            await cdp!.send('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13 }, { sessionId });
            await cdp!.send('Input.dispatchKeyEvent', { type: 'keyUp', key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13 }, { sessionId });
            await sleep(2000);

            const afterEnter = await cdp!.send<{ result: { value: string } }>('Runtime.evaluate', {
              expression: `!document.querySelector('.n-dialog') ? 'closed' : 'still_open'`,
              returnByValue: true,
            }, { sessionId });
            console.log(`[weibo-article] After Enter: ${afterEnter.result.value}`);
          }

          await sleep(1000);

          // Verify cover was set (cover-preview with img should exist)
          const coverSet = await cdp.send<{ result: { value: string } }>('Runtime.evaluate', {
            expression: `(() => {
              const preview = document.querySelector('.cover-preview .cover-img');
              if (preview) return 'cover_set';
              const empty = document.querySelector('.cover-empty');
              if (empty) return 'cover_empty_still_exists';
              return 'cover_unknown';
            })()`,
            returnByValue: true,
          }, { sessionId });
          console.log(`[weibo-article] Cover result: ${coverSet.result.value}`);
        }
      }
    } else if (coverImagePath) {
      console.warn(`[weibo-article] Cover image not found: ${coverImagePath}`);
    } else {
      console.log('[weibo-article] No cover image specified');
    }

    console.log('[weibo-article] Article composed. Please review and publish manually.');
    console.log('[weibo-article] Browser remains open for manual review.');

  } finally {
    if (cdp) {
      cdp.close();
    }
  }
}

function printUsage(): never {
  console.log(`Publish Markdown article to Weibo Headline Articles

Usage:
  npx -y bun weibo-article.ts <markdown_file> [options]

Options:
  --title <title>       Override title (max 32 chars)
  --summary <text>      Override summary (max 44 chars)
  --cover <image>       Override cover image
  --profile <dir>       Chrome profile directory
  --help                Show this help

Markdown frontmatter:
  ---
  title: My Article Title
  summary: Brief description
  cover_image: /path/to/cover.jpg
  ---

Example:
  npx -y bun weibo-article.ts article.md
  npx -y bun weibo-article.ts article.md --cover ./hero.png
  npx -y bun weibo-article.ts article.md --title "Custom Title"
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
  }

  let markdownPath: string | undefined;
  let title: string | undefined;
  let summary: string | undefined;
  let coverImage: string | undefined;
  let profileDir: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--title' && args[i + 1]) {
      title = args[++i];
    } else if (arg === '--summary' && args[i + 1]) {
      summary = args[++i];
    } else if (arg === '--cover' && args[i + 1]) {
      const raw = args[++i]!;
      coverImage = path.isAbsolute(raw) ? raw : path.resolve(process.cwd(), raw);
    } else if (arg === '--profile' && args[i + 1]) {
      profileDir = args[++i];
    } else if (!arg.startsWith('-')) {
      markdownPath = arg;
    }
  }

  if (!markdownPath) {
    console.error('Error: Markdown file path required');
    process.exit(1);
  }

  if (!fs.existsSync(markdownPath)) {
    console.error(`Error: File not found: ${markdownPath}`);
    process.exit(1);
  }

  await publishArticle({ markdownPath, title, summary, coverImage, profileDir });
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
